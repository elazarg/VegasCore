/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingFirstPacket
import Vegas.Game.SourceServiceLateDecisionCompletion
import Vegas.Game.SourceServiceRecordedBindingCompletion
import Vegas.Pending.ReactiveBindingAcceptanceReceipts
import Vegas.Pending.ReactiveBindingOmission

/-! # Actual acceptance or public miss of one timely binding attempt

At a raw initialized prefix with a fresh counted candidate, a manual timely
canonical binding call either receives acceptance for its own actual identifier
and completes with the selected typed value, or expires with the real public
miss marker and typed failure. The owner subsequently follows its
recorded turn policy, while foreign policies remain arbitrary raw policies.

The manual attempt can occur outside protected inclusion. This theorem does
not claim the protected timing policy itself transmits at that opportunity.
It derives packet uniqueness, complete play and receipt identity from the
actual prefix and continuation, with no supplied selection probability.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A timely first binding call has the exact binary physical outcome. Both
branches retain the selected original identifier; hidden usability does not
change acceptance, and only actual expiry creates the miss branch. -/
theorem sourceService_binding_attempt_completion
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some site.owner, execution⟩))
    (fresh : execution.application.candidates.lookup
      (site.owner, .prepared (execution.application.publicView.bindingCount site.owner)) = .fresh)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (value : PublicationResult (L.Val site.payload))
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution.respond (application setup leaks) site.owner
        ((runtime setup).reactiveBinding leaks site.owner event site.payload value
          (execution.application.publicView.bindingCount site.owner)))).support) :
    event ∈ stopped.application.config.cut.completed ∧
      (((site.owner, execution.network.nextSerial site.owner), true) ∈ stopped.receipts ∧
        event ∉ stopped.application.missedEvents ∧
        stopped.application.config = execution.application.config.complete event
          ((execution.application.publicView_eventReady event).mp
            (PublicView.ownTurn?_spec _ site.owner event turn).1)
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value) ∨
      event ∈ stopped.application.missedEvents ∧
        ((site.owner, execution.network.nextSerial site.owner), true) ∉ stopped.receipts ∧
        (⟨.inr event, site.outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.binding site.owner site.payload)).get? stopped.application.config.store =
            some .failure) := by
  let app := application setup leaks
  let owner := site.owner
  let serial := execution.application.publicView.bindingCount owner
  let response := (runtime setup).reactiveBinding leaks owner event site.payload value serial
  let start := execution.respond app owner response
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, execution.network.nextSerial owner),
      ⟨.commitment event (owner, .prepared serial), none,
        execution.application.publicView.tokenFor
          (.commitment event (owner, .prepared serial))⟩⟩
  let action := cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ owner event turn).1
  have rawTrace := trace
  have selected : canonicalFreshSlot owner (execution.observe app owner).application =
      some serial := canonicalFreshSlot_canonical owner _ fresh
  have decided := (runtime setup).canonicalServiceDecision_binding leaks owner
    (execution.recall owner) (execution.observe app owner) event site.payload site.outputEq
    site.code (nodeView_eq_bind site.outputEq site.code) serial selected value
  have effective : EffectiveAction execution.application.config event action := by
    unfold EffectiveAction
    rw [nodeView_eq_bind site.outputEq site.code]
    trivial
  have afterReady : start.application.config.cut.Ready event := by
    rw [((runtime setup).reactive_respond_application leaks execution owner response).1]
    exact ready
  have recorded : (runtime setup).eventRecorded leaks (start.recall owner) event = true :=
    (runtime setup).eventRecorded_respond leaks execution owner response event rfl
  have stoppedLaw : app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon start =
      app.runUntilHorizon scheduler (Function.update players owner app.silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon start := by
    unfold ReactiveApplication.runUntilHorizon
    exact sourceServiceTurnPolicy_runUntil_owner_silent setup leaks scheduler players bound turns
      timing profile owner follows _ start event afterReady site.owned recorded
  have silentReached := stoppedLaw ▸ reached
  have dichotomy := sourceServiceCanonicalDecision_include_or_miss contract owner execution
    rawTrace event site.owned ready timely unrecorded action effective
    (Function.update players owner app.silentPolicy) (Function.update_self ..) stopped
    (by
      dsimp only [action]
      rw [decided]
      exact silentReached)
  have complete := dichotomy.1
  have accounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  change execution.environmentRecall.length + remaining = horizon at accounted
  obtain ⟨startTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler remaining
    execution owner response rawTrace
  have startBudget : start.environmentRecall.length + remaining = horizon := by
    rw [app.respond_environmentRecall]
    exact accounted
  obtain ⟨used, budget, rounds, length⟩ := app.runUntil_runRounds scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - start.environmentRecall.length) start stopped reached
  have usedWithin : used ≤ remaining := by omega
  obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
    (remaining - used) used start stopped
    (by simpa only [Nat.sub_add_cancel usedWithin] using startTrace) rounds
  have facts := legalFacts setup leaks horizon scheduler _ stoppedTrace
  have inputTrace := stoppedTrace
  rw [initialLaw_eq_inputs] at inputTrace
  have misses := bindingMissesExact_history (runtime setup) leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace event owner site.payload
    site.outputEq
  have sole := sourceService_binding_first_packet setup leaks scheduler players bound turns timing
    profile owner follows horizon remaining execution rawTrace event ready site.owned unrecorded
    site.payload value serial stopped reached
  let material : app.Submission :=
    ⟨⟨.commitment event (owner, .prepared serial), match value with
      | .failure => none
      | .success drawn => some ⟨site.payload, drawn⟩⟩, .none⟩
  let entry : app.PlayerEntry := ⟨execution.observe app owner, response, some message⟩
  have packetEq := reactiveApplication_packet_none (runtime setup) leaks execution.application
    owner (execution.network.known owner) material.call
  have recalled : start.recall owner = execution.recall owner ++ [entry] := by
    have actual := respond_submit_recall execution owner material
    rw [packetEq] at actual
    have responseEq : response = ⟨some material⟩ := by
      cases value <;> rfl
    rw [← responseEq] at actual
    change start.recall owner = execution.recall owner ++ [entry] at actual
    exact actual
  have initialMember : entry ∈ start.recall owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have retained : app.PolicyInvariant players (fun current => entry ∈ current.recall owner) := {
    respond := fun current actor chosen present _ =>
      app.respond_recall_mono current actor owner chosen present
    environment := fun current next command present moved => by
      rw [app.environmentStep_recall current next command moved]
      exact present }
  have finalMember := retained.runRounds scheduler used start stopped initialMember rounds
  have output : message ∈ app.outputs (stopped.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, finalMember, rfl⟩
  rw [← facts.inputs owner] at output
  have input : message ∈ stopped.network.inputs := (List.mem_filter.mp output).1
  refine ⟨complete, ?_⟩
  by_cases missed : event ∈ stopped.application.missedEvents
  · right
    obtain ⟨_, absent⟩ := misses.mp missed
    refine ⟨missed, ?_, ?_⟩
    · intro receipt
      obtain ⟨packet, published, identified, accepted⟩ :=
        bindingReceipts_history (runtime setup) leaks (setup.initialLaw.map setup.eventInputs)
          horizon scheduler _ inputTrace message.id receipt
      have same := (facts.unique.inputs message input).ledger packet published identified
      subst packet
      have associated := accepted event (owner, .prepared serial) rfl
      rw [absent] at associated
      cases associated
    · let ref : EventGraph.FieldRef (graph setup).layout (.binding owner site.payload) :=
        ⟨.inr event, site.outputEq⟩
      have present := ref.get?_isSome stopped.application.config.store
        ((stopped.application.config.output_available event).mpr complete)
      obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp present
      cases result with
      | failure => exact stored
      | success result =>
          obtain ⟨candidate, associated, _, _⟩ := facts.binding.success_provenance ref result stored
          rw [absent] at associated
          cases associated
  · left
    have chosen := dichotomy.2.resolve_left missed
    have step := execution.application.config.step_eq_map_of_code event ready site.outputEq
      (.bind owner site.payload) site.code value (PMF.pure value) rfl
    rw [step, PMF.pure_map, PMF.mem_support_pure_iff] at chosen
    cases associated : stopped.application.accepted (.inr event) with
    | none => exact (missed (misses.mpr ⟨complete, associated⟩)).elim
    | some candidate =>
        obtain ⟨payload, typed⟩ := facts.binding.accepted_typed (.inr event) candidate associated
        change (graph setup).outputLayout event = .binding candidate.1 payload at typed
        have authored : candidate.1 = owner :=
          (EventGraph.EventField.binding.inj (typed.symm.trans site.outputEq)).1
        obtain ⟨packet, published, sender, call, receipt⟩ :=
          acceptedBindingReceipts_history (runtime setup) leaks
            (setup.initialLaw.map setup.eventInputs) horizon scheduler inputTrace event candidate
            associated
        have same := sole.ledger packet published (sender.trans authored)
          (by rw [call]; rfl)
        rw [same] at receipt
        exact ⟨receipt, missed, chosen⟩

end Vegas
