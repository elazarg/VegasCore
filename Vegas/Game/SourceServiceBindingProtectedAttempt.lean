/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingAttemptCompletion

/-! # Acceptance of an actual protected canonical binding attempt

A raw initialized input with a fresh counted candidate renders its canonical
binding as an acceptable protected fresh call. The recorded owner is silent
afterward, and actual packet provenance identifies this one packet throughout
the stopped continuation. Protected inclusion rules out the miss branch of the
receipt-driven physical completion law. Foreign policies remain arbitrary.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A protected manual canonical call is accepted with its actual identifier
and makes its chosen typed binding step. Every resource comes from the raw
input and the actual call, without a globally clean menu history. -/
theorem BindingSource.protected_attempt_completion
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
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
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
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value)) := by
  let app := application setup leaks
  let owner := site.owner
  let serial := execution.application.publicView.bindingCount owner
  let response := (runtime setup).reactiveBinding leaks owner event site.payload value serial
  let material : app.Submission :=
    ⟨⟨.commitment event (owner, .prepared serial), match value with
      | .failure => none
      | .success drawn => some ⟨site.payload, drawn⟩⟩, .none⟩
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, execution.network.nextSerial owner),
      ⟨.commitment event (owner, .prepared serial), none,
        execution.application.publicView.tokenFor
          (.commitment event (owner, .prepared serial))⟩⟩
  let entry : app.PlayerEntry := ⟨execution.observe app owner, response, some message⟩
  let start := execution.respond app owner response
  let action := cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ owner event turn).1
  have responseEq : response = ⟨some material⟩ := by cases value <;> rfl
  have packetEq := reactiveApplication_packet_none (runtime setup) leaks execution.application
    owner (execution.network.known owner) material.call
  have decided := (runtime setup).canonicalServiceDecision_binding leaks owner
    (execution.recall owner) (execution.observe app owner) event site.payload site.outputEq
    site.code (nodeView_eq_bind site.outputEq site.code) serial
    (canonicalFreshSlot_canonical owner (execution.observe app owner).application fresh) value
  have call : FreshCall setup leaks owner event bound entry message := {
    fresh := ⟨material, congrArg ReactiveApplication.Action.transmission responseEq⟩
    emitted := rfl
    authored := rfl
    addressed := rfl
    ready := (PublicView.ownTurn?_spec _ owner event turn).1
    fits := fits
    conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) (by
      have conforms := canonicalServiceDecision_freshServiceEnvelope trace event turn
        fits.withinDeadline fresh action material (by
          rw [decided]
          exact congrArg ReactiveApplication.Action.transmission responseEq)
      rw [packetEq] at conforms
      exact conforms) }
  have recalled : start.recall owner = execution.recall owner ++ [entry] := by
    have actual := respond_submit_recall execution owner material
    rw [packetEq, ← responseEq] at actual
    exact actual
  obtain ⟨startTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler remaining
    execution owner response trace
  have accounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  change execution.environmentRecall.length + remaining = horizon at accounted
  obtain ⟨used, budget, rounds, _length⟩ := app.runUntil_runRounds scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - start.environmentRecall.length) start stopped reached
  have startLength : start.environmentRecall.length = execution.environmentRecall.length :=
    congrArg List.length (app.respond_environmentRecall execution owner response)
  have within : used ≤ remaining := by omega
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
    (remaining - used) used start stopped
    (by simpa only [Nat.sub_add_cancel within] using startTrace) rounds
  have retained : app.PolicyInvariant players
      (fun current => start.recall owner <+: current.recall owner) := {
    respond := fun current actor chosen holds _ =>
      holds.trans (app.respond_recall_prefix current actor owner chosen)
    environment := fun current next command holds moved => by
      rw [app.environmentStep_recall current next command moved]
      exact holds }
  obtain ⟨later, prefixEq⟩ := retained.runRounds scheduler used start stopped (by rfl) rounds
  have split : stopped.recall owner = execution.recall owner ++ entry :: later := by
    rw [← prefixEq, recalled, List.append_assoc]
    rfl
  have facts := legalFacts setup leaks horizon scheduler _ finalTrace
  have sole := sourceService_binding_first_packet setup leaks scheduler players bound turns timing
    profile owner follows horizon remaining execution trace event ready site.owned unrecorded
    site.payload value serial stopped reached
  have excludes : ∀ other ∈ execution.recall owner ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
    intro other member ⟨packet, emitted, authored, addressed, different⟩
    have memberFinal : other ∈ stopped.recall owner := by
      rw [split]
      rcases List.mem_append.mp member with earlier | after
      · exact List.mem_append_left _ earlier
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    have output : packet ∈ app.outputs (stopped.recall owner) :=
      List.mem_filterMap.mpr ⟨other, memberFinal, emitted⟩
    rw [← facts.inputs owner] at output
    have same := sole.inputs packet (List.mem_filter.mp output).1 authored addressed
    exact different (congrArg Message.id same)
  have settled := settlesFreshCalls_history setup leaks contract.inclusion owner event site.owned
    finalTrace (execution.recall owner) entry later message split call excludes
  have outcome := sourceService_binding_attempt_completion contract players timing profile execution
    event site trace fresh turn unrecorded fits.withinDeadline follows value stopped reached
  refine ⟨outcome.1, ?_⟩
  rcases outcome.2 with accepted | missed
  · exact accepted
  · exact (settled.2.2.2 missed.1).elim

end Vegas
