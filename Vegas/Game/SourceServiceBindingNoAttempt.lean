/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingFirstPacket
import Vegas.Game.SourceServiceLateDecisionCompletion
import Vegas.Pending.ReactiveBindingAcceptanceReceipts
import Vegas.Pending.ReactiveBindingOmission

/-! # Actual binding omission after protection closes

A ready event retains its original activation until completion, and the clock
only increases. Its closed protected inclusion gate cannot reopen. The actual
owner turn policy is therefore silent for every timing lottery until the event
completes. An initialized unrecorded binding then has no owner packet naming it;
complete play produces a real public miss and typed failure.

Foreign policies remain arbitrary raw policies. No silence, eventual miss,
acceptance probability or completed endpoint is supplied as a premise.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem closed_after_progress
    {inputs : (graph setup).Inputs} {ticks : Nat}
    {before after : (application setup leaks).State}
    (progress : State.ServiceProgress inputs ticks before after)
    (event : (graph setup).EventId) (entered : Nat)
    (activated : before.activatedAt event = some entered)
    (bound : (graph setup).EventId → Nat)
    (closed : ¬ before.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (unfinished : event ∉ after.config.cut.completed) :
    ¬ after.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  have current := progress.activated event entered activated unfinished
  intro fits
  unfold PublicView.InclusionFitsDeadline at closed fits
  change ¬ (match before.activatedAt event with
    | none => False
    | some first => before.clock - first + bound event < (runtime setup).deadline event) at closed
  change (match after.activatedAt event with
    | none => False
    | some first => after.clock - first + bound event < (runtime setup).deadline event) at fits
  rw [activated] at closed
  rw [current, progress.clock] at fits
  omega

/-- At an actual ready owned input with closed protection, the whole timing
mixture is silent, including its selected turn. -/
theorem sourceServiceTurnPolicy_input_of_closed
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (closed : ¬ execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) =
      (application setup leaks).silentPolicy (execution.recall owner)
        (execution.observe (application setup leaks) owner) := by
  let app := application setup leaks
  have sole := soleReady_of_ready setup execution.application ready
  have turn := PublicView.ownTurn?_of_ownTurn execution.application.publicView owner event
    (sole.ownTurn owned)
  have viewClosed : ¬ (execution.observe app owner).application.publicView.InclusionFitsDeadline
      (runtime setup) bound event := closed
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns timing profile owner _ _ event
    owned turn, app.policyMixture_policy]
  have family (slot : Fin (turns + 1)) :
      sourceServiceTurnFamily setup leaks bound profile owner event turns slot
        (execution.recall owner) (execution.observe app owner) =
      app.silentPolicy (execution.recall owner) (execution.observe app owner) := by
    simp only [sourceServiceTurnFamily, ReactiveApplication.turnScheduledPolicy]
    split
    · by_cases recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true
      · simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte]
        rfl
      · simp only [sourceServiceCanonicalOpportunity, recorded, Bool.false_eq_true, viewClosed,
          ↓reduceIte]
        rfl
    · rfl
  dsimp only [app] at family
  simp only [family, PMF.bind_const]

private theorem closed_runUntil_owner_silent
    {inputs : (graph setup).Inputs}
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (count : Nat) (execution : (application setup leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (closed : ¬ execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event) :
    (application setup leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (Function.update players owner (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := application setup leaks
  let invariant := fun current : app.Execution =>
    ∃ ticks, State.ServiceProgress inputs ticks execution.application current.application
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor event ready
    (by rw [owned]; rfl)
  have resources (current : app.Execution) (holds : invariant current)
      (running : event ∉ current.application.config.cut.completed) :
      current.application.config.cut.Ready event ∧
        ¬ current.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
    obtain ⟨ticks, progress⟩ := holds
    exact ⟨(progress.ready_or_completed event ready).resolve_left running,
      closed_after_progress progress event entered activated bound closed running⟩
  apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
  · intro current holds running command _ middle moved who active
    by_cases foreign : who ≠ owner
    · simp only [Function.update_of_ne foreign]
    · have own : who = owner := not_ne_iff.mp foreign
      subst who
      rw [Function.update_self, follows]
      cases command with
      | activate actor =>
          have applicationEq := activation_application setup leaks current middle actor moved
          have facts := resources current holds running
          apply sourceServiceTurnPolicy_input_of_closed bound turns timing profile middle owner
            event
          · rw [applicationEq]
            exact facts.1
          · exact owned
          · rw [applicationEq]
            exact facts.2
      | «include» _ | application _ | wait => cases active
  · intro current holds _running next reached
    obtain ⟨ticks, progress⟩ := holds
    obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    exact ⟨ticks + (runtime setup).reactiveTicks leaks command,
      progress.trans ((runtime setup).reactive_dispatch_progress leaks inputs players current
        next command progress.invariant moved)⟩
  · exact ⟨0, .refl valid⟩

/-- Every actual stopped endpoint of an unrecorded binding with closed
protection is an actual public miss with typed failure. No owner envelope for
the event is emitted anywhere in the retained network. -/
theorem sourceService_binding_no_attempt
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (closed : ¬ execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support) :
    event ∈ stopped.application.config.cut.completed ∧
      event ∈ stopped.application.missedEvents ∧
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.binding owner payload)).get? stopped.application.config.store = some .failure ∧
      (runtime setup).eventRecorded leaks (stopped.recall owner) event = false ∧
      stopped.network.Satisfies (fun message => message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) := by
  let app := application setup leaks
  have valid : ∃ inputs, execution.application.Invariant inputs := by
    let preserved : app.ServiceInvariant scheduler (fun current =>
        ∃ inputs, current.application.Invariant inputs) := {
      respond := fun current who response holds => by
        obtain ⟨inputs, valid⟩ := holds
        exact ⟨inputs, ((runtime setup).reactive_respond_progress leaks inputs current who
          response valid).invariant⟩
      environment := fun current next command holds _ reached => by
        obtain ⟨inputs, valid⟩ := holds
        exact ⟨inputs, ((runtime setup).reactive_environment_progress leaks inputs current next
          command valid reached).invariant⟩ }
    exact preserved.history (initialLaw setup) horizon (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨setup.eventInputs initial, State.initial_invariant _⟩) trace
  obtain ⟨inputs, valid⟩ := valid
  have stoppedLaw : app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution =
      app.runUntilHorizon scheduler (Function.update players owner app.silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
    unfold ReactiveApplication.runUntilHorizon
    exact closed_runUntil_owner_silent scheduler players bound turns timing profile owner follows
      _ execution valid event ready owned closed
  have silentReached := stoppedLaw ▸ reached
  have retained : app.PolicyInvariant (Function.update players owner app.silentPolicy)
      (fun current => (runtime setup).eventRecorded leaks (current.recall owner) event = false) := {
    respond := fun current who response holds supported => by
      apply Eq.trans ((runtime setup).eventRecorded_respond_other leaks current who owner response
        event ?_) holds
      intro same
      subst who
      rw [Function.update_self] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro impossible
      cases impossible
    environment := fun current next command holds moved => by
      rw [app.environmentStep_recall current next command moved]
      exact holds }
  obtain ⟨used, budget, rounds, length⟩ := app.runUntil_runRounds scheduler
    (Function.update players owner app.silentPolicy)
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - execution.environmentRecall.length) execution stopped silentReached
  have unrecordedFinal := retained.runRounds scheduler used execution stopped unrecorded rounds
  have accounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  change execution.environmentRecall.length + remaining = horizon at accounted
  have completed := runUntilHorizon_completes contract.completes (by omega)
    (by simpa only [show horizon - execution.environmentRecall.length = remaining by omega]
      using trace) stopped reached
  have usedWithin : used ≤ remaining := by omega
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler
    (Function.update players owner app.silentPolicy) (remaining - used) used execution stopped
    (by simpa only [Nat.sub_add_cancel usedWithin] using trace) rounds
  have facts := legalFacts setup leaks horizon scheduler _ finalTrace
  have noPacket := sourceService_unrecorded_event_packets setup leaks stopped owner event
    facts.provenance unrecordedFinal
  have inputTrace := finalTrace
  rw [initialLaw_eq_inputs] at inputTrace
  have absent : stopped.application.accepted (.inr event) = none := by
    cases accepted : stopped.application.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        obtain ⟨kind, typed⟩ := facts.binding.accepted_typed (.inr event) candidate accepted
        change (graph setup).outputLayout event = .binding candidate.1 kind at typed
        have authored : candidate.1 = owner :=
          (EventGraph.EventField.binding.inj (typed.symm.trans outputEq)).1
        obtain ⟨message, published, sender, named, _⟩ := acceptedBindingReceipts_history
          (runtime setup) leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler
          inputTrace event candidate accepted
        exact ((noPacket.ledger message published (sender.trans authored))
          (by rw [named]; rfl)).elim
  have misses := bindingMissesExact_history (runtime setup) leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace event owner payload
    outputEq
  refine ⟨completed, misses.mpr ⟨completed, absent⟩, ?_, unrecordedFinal, noPacket⟩
  let ref : EventGraph.FieldRef (graph setup).layout (.binding owner payload) :=
    ⟨.inr event, outputEq⟩
  have present := ref.get?_isSome stopped.application.config.store
    ((stopped.application.config.output_available event).mpr completed)
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
  cases value with
  | failure => exact stored
  | success value =>
      obtain ⟨candidate, accepted, _, _⟩ := facts.binding.success_provenance ref value stored
      rw [absent] at accepted
      cases accepted

end Vegas
