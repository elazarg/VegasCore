/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastEligibleResponse
import Vegas.Examples.CommitSeedBroadcastProperSurvival
import Interaction.ReactiveRecovery

/-! # Proper continuations survive at every eligible original clock -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The proper response at an eligible original clock obtains its actual
receipt and survives the entire continuation, independently of opponents'
hidden preparations and all their counted future responses. -/
theorem scheduled_proper_eligible_finish_survives (slot : Nat)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = slot)
    (eligible : slot = lateClock (seed.2 owner))
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy slot owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (past : (scheduledProperPolicy slot owner).Consistent (execution.recall owner))
    (after : app.Execution)
    (reached : app.finished after ∈ (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after ∧
      owner ∉ after.application.current.excluded := by
  classical
  obtain ⟨serial, _bounded, proper, _slot, _fresh, _result⟩ := proper_original_clock_response
    (family seed) remaining execution owner
      (countedInRaw.trace initial horizon (family seed) trace) request slot clock unsent
  let action := phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
    (.success true) serial
  have literal : scheduledProperPolicy slot owner (execution.recall owner)
      (execution.observe app owner) = PMF.pure action := by
    unfold scheduledProperPolicy
    rw [ite_eq_right (fun both => by
      have zero := both.2.1
      change execution.application.current.native.clock = 0 at zero
      have positive : 0 < slot := by
        rw [eligible]
        cases seed.2 owner <;> decide
      omega)]
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
  have length := (countedMenu.roundSupported_uniform initial horizon (family seed) finalTrace).1
  have enough : 30 ≤ after.environmentRecall.length := by
    change after.environmentRecall.length + 0 = 128 at length
    omega
  have resolved := original_bindings_resolved seed ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon (family seed) finalTrace) enough owner
  have accepted := original_eligible_response_resolved_accepted seed remaining execution owner
    trace request (clock.trans eligible)
      (⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial),
        some ⟨.bool, true⟩⟩, .none⟩ : WitnessedSubmission graph)
      offered rfl players covered after actual resolved
  have recovered : players owner =
      (scheduledProperPolicy slot owner).recover (scheduledProperPolicy slot owner) := by
    rw [selected]
    funext earlier view
    simp only [ReactiveApplication.Policy.recover, ite_self]
  have invariant := (scheduledProperPolicy slot owner).recover_invariant
    (scheduledProperPolicy slot owner) owner players recovered
  have consistent := invariant.runRounds (family seed) remaining
    (execution.respond app owner action) after
      (invariant.respond execution owner action past actionSupported) actual
  exact ⟨accepted, scheduled_proper_original_binding_survives slot seed ⟨0, none, after⟩
    finalTrace owner consistent accepted⟩

end Vegas.Examples.CommitSeedBroadcast
