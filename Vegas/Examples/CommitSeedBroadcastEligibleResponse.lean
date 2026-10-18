/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalLateSuccess
import Vegas.Examples.CommitSeedBroadcastProperResponse
import Vegas.Examples.CommitSeedBroadcastAddressedSeed
import Vegas.Pending.PhaseSeedPosteriorResponse
import Vegas.Pending.PhaseSeedEmissionPersistence
import Interaction.ReactiveRoundTrace

/-! # Actual eligible original responses obtain admission at resolved endpoints -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- At an unsent original callback, the proper policy for its actual clock
emits a fresh, successful TRUE declaration. This also covers the helper slot. -/
theorem proper_original_clock_response
    (selected : app.Scheduler) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : Nat) (physical : execution.application.current.native.clock = clock)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner)) :
    ∃ serial, serial < horizon ∧
      properPolicy (lateAtRule clock) owner (execution.recall owner)
          (execution.observe app owner) =
        PMF.pure (phaseBindingResponse runtime leaks owner (bindingEvent owner)
          .bool (.success true) serial) ∧
      reactiveFreshSlot (execution.observe app owner).application.1 = some serial ∧
      execution.application.current.native.candidates.lookup (owner, .prepared serial) = .fresh ∧
      (execution.respond app owner
        (phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool (.success true)
          serial)).application.current.native.bindingResult (owner, .prepared serial) .bool =
        .success true := by
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have requested : execution.application.SeedRequest owner
      ⟨execution.application.attempt, bindingEvent owner⟩ := by
    simpa only [original, originalCoordinate] using request
  have timer := original_timer selected ⟨remaining, some owner, execution⟩
    (rawMenu.toRawTrace initial horizon selected trace) original owner request.2.2.1.1
  have chosen : lateAtRule clock owner ⟨execution.application.attempt, bindingEvent owner⟩
      (PhaseSeedScheduler.serviceClocks runtime leaks
        ⟨execution.application.attempt, bindingEvent owner⟩ owner
          (execution.recall owner) (execution.observe app owner)) = true := by
    simp only [lateAtRule, original, ite_true, PhaseSeedScheduler.serviceClocks,
      PhaseSeedScheduler.informationInput, List.getLastD_concat]
    change decide (execution.application.current.native.clock -
      (execution.application.current.native.activatedAt (bindingEvent owner)).getD
        execution.application.current.native.clock = clock) = true
    rw [timer, physical]
    exact decide_eq_true (Nat.sub_zero clock)
  apply properPolicy_binding_response (lateAtRule clock) selected
    ⟨remaining, some owner, execution⟩ trace owner rfl (bindingEvent owner)
      (bindingEvent_layout owner) requested
  · simpa only [original, originalCoordinate] using unsent
  · exact Or.inr chosen

/-- A permitted original binding response in its owner's eligible physical slot
is admitted by every resolved endpoint of the same continuation. Its timed
emission is derived from the actual response, not assumed from a later receipt. -/
theorem original_eligible_response_resolved_accepted
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = lateClock (seed.2 owner))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (named : material.call.packet.event? graph = some (bindingEvent owner))
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (after : app.Execution)
    (reached : after ∈ (app.runRounds (family seed) players remaining
      (execution.respond app owner ⟨some material⟩)).support)
    (resolved : (originalCoordinate owner).Resolved after.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution owner ⟨some material⟩ trace offered
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining (execution.respond app owner ⟨some material⟩) responded
  have valid := raw_native_valid (family seed) ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace)
  have stamp := original_timer (family seed) ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace) request.1.symm owner
      request.2.2.1.1
  obtain ⟨message, _identifier, emitted⟩ := PhaseSeedCalendar.response_envelope_recorded
    runtime leaks execution valid owner (originalAddress owner) request material
      named 0 stamp words
  have emission : (lateClock (seed.2 owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        (execution.respond app owner ⟨some material⟩).environmentRecall
        ((execution.respond app owner ⟨some material⟩).observeEnvironment app)).emissions := by
    simpa only [Nat.sub_zero, clock, originalAddress] using emitted
  have retained := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks (family seed)
    players remaining (execution.respond app owner ⟨some material⟩) after words reached owner
      (originalCoordinate owner)
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining (execution.respond app owner ⟨some material⟩) after
      (by simpa only [Nat.zero_add] using responded) reached
  exact original_eligible_emission_resolved_accepted seed 0 after finalTrace owner resolved
    message (retained.subset emission)

end Vegas.Examples.CommitSeedBroadcast
