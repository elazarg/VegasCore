/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingWord
import Vegas.Pending.PhaseRecordedCountedRequest
import Interaction.ReactiveRecordedResponse

/-! # A retained original declaration contributes its actual service clock -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- This conclusion retains the packet's actual preparation and evidence. It
does not require that its private binding result can later be opened. -/
theorem original_recorded_transmission_clock (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (material : WitnessedSubmission graph) (transmitted : entry.action.transmission = some material)
    (clock : Nat) (physical : entry.beforeView.application.2.native.clock = clock) :
    clock ∈ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
      execution := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  obtain ⟨coordinate, actualRequest, _stamp, names⟩ := PhaseCount.recorded_material_request runtime
    leaks bounds plan (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
      (setup.initialLaw.map encodeInputs) horizon (family seed) _ compiledTrace owner entry member
        material transmitted
  obtain ⟨before, prior, _kept, _active, viewed, _offered, _later, _recalled⟩ :=
    countedMenu.recorded_response_prefix initial horizon (family seed) _ trace owner entry member
  have beforeRaw := countedMenu.toRawTrace initial horizon (family seed) prior
  have valid := raw_native_valid (family seed) _ beforeRaw
  have publicOriginal := requested
  have publicActual := actualRequest
  rw [viewed] at publicOriginal publicActual
  have originalRequest := (before.execution.application.requests_publicView valid owner
    (originalCoordinate owner)).mp publicOriginal
  have actual := (before.execution.application.requests_publicView valid owner coordinate).mp
    publicActual
  have original : before.execution.application.attempt = originalAttempt :=
    originalRequest.1.symm
  have coordinateEq := original_request_coordinate seed before beforeRaw coordinate owner
    (actual.1.trans original) actual
  rw [coordinateEq] at actualRequest names
  obtain ⟨message, emitted, authored, call⟩ := PhaseCount.recalled_submission_emitted runtime
    leaks initial horizon (family seed) raw owner entry member material transmitted
  have tag := phase_recalled_emission_attempt runtime leaks initial horizon (family seed) raw
    owner entry member message emitted
  have originalEntry : entry.beforeView.application.2.attempt = originalAttempt := requested.1.symm
  have tagged : message.payload.attempt = originalAttempt := tag.trans originalEntry
  have named : message.payload.packet.call.event? graph = some (bindingEvent owner) := by
    rw [call]
    exact names
  have selected : PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner message = true :=
    decide_eq_true ⟨authored, tagged, named⟩
  have stamp := original_timer (family seed) before beforeRaw original owner
    originalRequest.2.2.1.1
  have stampView : entry.beforeView.application.2.native.activatedAt (bindingEvent owner) =
      some 0 := by
    rw [viewed]
    exact stamp
  have age : entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock = clock := by
    rw [stampView, Option.getD_some, Nat.sub_zero, physical]
  have record : (clock, entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner)) ∈
      PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
        (execution.recall owner) := by
    apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨member, decide_eq_true requested⟩, ?_⟩
    exact congrArg (fun elapsed => (elapsed, entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner))) age
  have packet : message ∈ entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner) := by
    rw [emitted]
    exact List.mem_filter.mpr ⟨List.mem_singleton_self _, selected⟩
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining execution trace
  have timed : (clock, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions := by
    rw [PhaseSeedScheduler.localInput_word, words owner (originalCoordinate owner)]
    exact List.mem_flatMap.mpr ⟨_, record, List.mem_map.mpr ⟨message, packet, rfl⟩⟩
  exact List.mem_map.mpr ⟨(clock, message), timed, rfl⟩

end Vegas.Examples.CommitSeedBroadcast
