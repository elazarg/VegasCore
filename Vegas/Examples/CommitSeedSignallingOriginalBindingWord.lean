/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalEarlySuccess
import Vegas.Examples.CommitSeedSignallingOriginalLateSuccess
import Vegas.Examples.CommitSeedSignallingSnapshotOrigin
import Interaction.ReactiveMenuRestriction

/-! # Exact resolved original binding success from its retained emission clocks -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem binding_clock_iff_emission (coordinate : CommitAttemptEvent graph) (owner : Player)
    (execution : app.Execution) (clock : Nat) :
    clock ∈ PhaseService.bindingEmissionClocks runtime leaks coordinate owner execution ↔
      ∃ message, (clock, message) ∈ (PhaseSeedScheduler.localInput runtime leaks coordinate owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  constructor
  · intro member
    obtain ⟨pair, emitted, same⟩ := List.mem_map.mp member
    rcases pair with ⟨tick, message⟩
    cases same
    exact ⟨message, emitted⟩
  · rintro ⟨message, emitted⟩
    exact List.mem_map.mpr ⟨(clock, message), emitted, rfl⟩

private theorem recorded_clock_zero_emission (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ execution.recall owner)
    (material : WitnessedSubmission graph) (transmitted : entry.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (originalEntry : entry.beforeView.application.2.attempt = originalAttempt)
    (zero : entry.beforeView.application.1.publicView.clock = 0) :
    (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  obtain ⟨coordinate, requested, _stamp, names⟩ := PhaseCount.recorded_material_request runtime
    leaks bounds plan (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
      (setup.initialLaw.map encodeInputs) horizon (family seeds) _ trace owner entry member
        material transmitted
  obtain ⟨before, prior, _kept, _active, viewed, _offered, _later, _recalled⟩ :=
    countedMenu.recorded_response_prefix initial horizon (family seeds) _ trace owner entry member
  have beforeRaw := countedMenu.toRawTrace initial horizon (family seeds) prior
  have valid := raw_native_valid (family seeds) _ beforeRaw
  have publicRequest := requested
  rw [viewed] at publicRequest
  change PhaseRuntimeState.requests before.execution.application.publicView owner coordinate
    at publicRequest
  have request := (before.execution.application.requests_publicView valid owner coordinate).mp
    publicRequest
  have original : before.execution.application.attempt = originalAttempt := by
    rw [viewed] at originalEntry
    exact originalEntry
  have coordinateEq := original_request_coordinate seeds before beforeRaw coordinate owner
    (request.1.trans original) request
  rw [coordinateEq] at requested names
  obtain ⟨actual, actualEmitted, authored, call⟩ := PhaseCount.recalled_submission_emitted runtime
    leaks initial horizon (family seeds) raw owner entry member material transmitted
  have sameMessage : actual = message := Option.some.inj (actualEmitted.symm.trans emitted)
  subst actual
  have tag := phase_recalled_emission_attempt runtime leaks initial horizon (family seeds) raw
    owner entry member message emitted
  have tagged : message.payload.attempt = originalAttempt := tag.trans originalEntry
  have named : message.payload.packet.call.event? graph = some (bindingEvent owner) := by
    rw [call]
    exact names
  have selected : PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner message = true :=
    decide_eq_true ⟨authored, tagged, named⟩
  have nativeZero : entry.beforeView.application.2.native.clock = 0 := by
    rw [viewed] at zero ⊢
    exact zero
  have age : entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock = 0 := by
    rw [nativeZero, Nat.zero_sub]
  have record : (0, entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner)) ∈
      PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
        (execution.recall owner) := by
    apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨member, decide_eq_true requested⟩, ?_⟩
    exact congrArg (fun clock => (clock, entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner))) age
  have packet : message ∈ entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner) := by
    rw [emitted]
    exact List.mem_filter.mpr ⟨List.mem_singleton_self _, selected⟩
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seeds) remaining execution trace
  rw [PhaseSeedScheduler.localInput_word, words owner (originalCoordinate owner)]
  exact List.mem_flatMap.mpr ⟨_, record, List.mem_map.mpr ⟨message, packet, rfl⟩⟩

private theorem original_idle_binding_accepted_iff_clocks (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (resolved : (originalCoordinate owner).Resolved execution.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner execution ↔
      0 ∈ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
          execution ∨
        lateClock owner (seeds.2 (originalAddress owner)) ∈
          PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
            execution := by
  constructor
  · intro accepted
    have rawTrace := (PhaseCount.onePacketMenu_in_raw runtime leaks bounds).trace initial horizon
      (family seeds) trace
    rcases original_binding_accepted_emission seeds remaining execution rawTrace owner accepted
      with early | late
    · obtain ⟨snapshot, message, selected, input, authored, _tagged⟩ := early
      obtain ⟨entry, member, material, transmitted, emitted, originalEntry, zero⟩ :=
        snapshot_packet_original_clock_zero seeds remaining execution rawTrace snapshot selected
          owner message input authored
      exact Or.inl ((binding_clock_iff_emission (originalCoordinate owner) owner execution 0).mpr
        ⟨message, recorded_clock_zero_emission seeds remaining execution trace owner entry member
          material transmitted message emitted originalEntry zero⟩)
    · obtain ⟨_before, _used, message, _prior, _count, _attempt, _kept, _position, emitted⟩ := late
      exact Or.inr ((binding_clock_iff_emission (originalCoordinate owner) owner execution _).mpr
        ⟨message, emitted⟩)
  · intro clocks
    rcases clocks with early | late
    · obtain ⟨message, emitted⟩ :=
        (binding_clock_iff_emission (originalCoordinate owner) owner execution 0).mp early
      exact original_clock_zero_emission_resolved_accepted seeds remaining execution trace owner
        resolved message emitted
    · obtain ⟨message, emitted⟩ :=
        (binding_clock_iff_emission (originalCoordinate owner) owner execution _).mp late
      exact original_eligible_emission_resolved_accepted seeds remaining execution trace owner
        resolved message emitted

/-- At every resolved counted endpoint, the original binding is accepted exactly
when its retained emission word contains clock zero or its original seed's eligible
late clock. Arbitrary counted preparations, aliases and evidence are retained. -/
theorem original_binding_accepted_iff_clocks (seeds : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player)
    (resolved : (originalCoordinate owner).Resolved current.execution.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner current.execution ↔
      0 ∈ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
          current.execution ∨
        lateClock owner (seeds.2 (originalAddress owner)) ∈
          PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
            current.execution := by
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none =>
      exact original_idle_binding_accepted_iff_clocks seeds remaining execution trace owner resolved
  | some actor =>
      obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seeds) remaining
        execution actor ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds actor _ _)
      exact original_idle_binding_accepted_iff_clocks seeds remaining
        (execution.respond app actor ⟨none⟩) responded owner resolved

end Vegas.Examples.CommitSeedSignalling
