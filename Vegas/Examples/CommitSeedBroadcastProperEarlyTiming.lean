/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperTimingValue
import Vegas.Examples.CommitSeedBroadcastRecordedEmission
import Vegas.Examples.CommitSeedBroadcastAllGoodAdmission

/-! # Survival of the proper initial packet under every original service seed -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The proper initial packet obtains original admission and survives every
covered continuation, regardless of opponents' preparations and service bits. -/
theorem scheduled_proper_early_finish_survives
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 0 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (after : app.Execution)
    (reached : app.finished after ∈ (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after ∧
      owner ∉ after.application.current.excluded := by
  classical
  have unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner) := by
    rw [word]
    exact fun _ member => (List.not_mem_nil member).elim
  obtain ⟨serial, _bounded, proper, _slot, _fresh, _result⟩ := proper_original_clock_response
    (family seed) remaining execution owner
      (countedInRaw.trace initial horizon (family seed) trace) request 0 clock unsent
  let action := phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
    (.success true) serial
  have literal : scheduledProperPolicy 0 owner (execution.recall owner)
      (execution.observe app owner) = PMF.pure action := by
    rw [scheduledProperPolicy_zero]
    exact proper
  have actionSupported : action ∈ (players owner (execution.recall owner)
      (execution.observe app owner)).support := by
    rw [selected, literal]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have offered := covered owner _ _ action actionSupported
  have actual : after ∈ (app.runRounds (family seed) players remaining
      (execution.respond app owner action)).support := by
    change app.finished after ∈ (((app.resume players (some owner) execution).bind
      (app.runRounds (family seed) players remaining)).map app.finished).support at reached
    rw [ReactiveApplication.resume, ReactiveApplication.invoke, selected, literal,
      PMF.pure_map, PMF.pure_bind, PMF.support_map] at reached
    obtain ⟨final, supported, equal⟩ := reached
    have same : final = after := congrArg ReactiveApplication.Control.execution
      (Option.some.inj equal)
    exact same ▸ supported
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution owner action trace offered
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining (execution.respond app owner action) after
      (by simpa only [Nat.zero_add] using responded) actual
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution owner action
  let entry : app.PlayerEntry := ⟨execution.observe app owner, action, emitted⟩
  have retained := rounds_recall_retained (family seed) players remaining
    (execution.respond app owner action) after actual owner
  have member : entry ∈ after.recall owner := retained.subset (by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _))
  have valid := raw_native_valid (family seed) ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace)
  have requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner) :=
    (execution.application.requests_publicView valid owner (originalCoordinate owner)).mpr request
  have zero := original_recorded_transmission_clock seed 0 after finalTrace owner entry member
    requested
      (⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial),
        some ⟨.bool, true⟩⟩, .none⟩ : WitnessedSubmission graph) rfl 0 clock
  have length := (countedMenu.roundSupported_uniform initial horizon (family seed) finalTrace).1
  have enough : 30 ≤ after.environmentRecall.length := by
    change after.environmentRecall.length + 0 = 128 at length
    omega
  have resolved := original_bindings_resolved seed ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon (family seed) finalTrace) enough owner
  have accepted := (original_binding_accepted_iff_clocks seed ⟨0, none, after⟩ finalTrace owner
    resolved).mpr (Or.inl zero)
  have recovered : players owner =
      (scheduledProperPolicy 0 owner).recover (scheduledProperPolicy 0 owner) := by
    rw [selected]
    funext earlier view
    simp only [ReactiveApplication.Policy.recover, ite_self]
  have invariant := (scheduledProperPolicy 0 owner).recover_invariant
    (scheduledProperPolicy 0 owner) owner players recovered
  have past : (scheduledProperPolicy 0 owner).Consistent (execution.recall owner) := by
    rw [word]
    exact .nil
  have consistent := invariant.runRounds (family seed) remaining
    (execution.respond app owner action) after
      (invariant.respond execution owner action past actionSupported) actual
  exact ⟨accepted, scheduled_proper_original_binding_survives 0 seed ⟨0, none, after⟩
    finalTrace owner consistent accepted⟩

end Vegas.Examples.CommitSeedBroadcast
