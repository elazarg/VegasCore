/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochStoppedCoupling

/-! # Original binding receipts cannot appear after physical retirement -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- On the literal initialized history, an old binding's eventual true receipt
already exists at any later namespace exit. A first new receipt after that exit
would require the handler to return to the original physical namespace. -/
theorem retired_binding_receipt_iff (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (start closed final : (app).Control)
    (startTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some start))
    (closedTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some closed))
    (finalTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some final))
    (toClosed : TracePrefix startTrace closedTrace)
    (afterClosed : TracePrefix closedTrace finalTrace)
    (retired : closed.execution.application.attempt ≠ start.execution.application.attempt)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ final.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (call : message.payload.packet.call = .commitment event candidate)
    (address : message.payload.attempt = start.execution.application.attempt) :
    ((message.id, true) ∈ final.execution.receipts ↔
      (message.id, true) ∈ closed.execution.receipts) := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  constructor
  · intro received
    by_contra absent
    obtain ⟨acceptingBefore, acceptingAfter, prior, joint, legal, realized, toAccepting,
      afterAccepting, noReceipt, _selected, moved, accepted⟩ :=
      prefix_accepting_receipt_boundary runtime leaks menu initial horizon scheduler closed final
        closedTrace finalTrace afterClosed message.id absent received
    have toFinal : TracePrefix prior finalTrace :=
      (TracePrefix.extend .refl joint legal realized).trans afterAccepting
    have rawAccepting := menu.toRawTrace initial horizon scheduler prior
    have rawFinal := menu.toRawTrace initial horizon scheduler finalTrace
    have found : acceptingBefore.execution.network.lookup message.id = some message := by
      cases lookup : acceptingBefore.execution.network.lookup message.id with
      | none =>
          have literal := moved
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at literal
          have equal := congrArg (fun execution : (app).Execution => execution.receipts)
            ((PMF.mem_support_pure_iff _ _).mp literal)
          have unchanged : acceptingAfter.execution.receipts =
              acceptingBefore.execution.receipts := by
            simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
              lookup] using equal
          exact (noReceipt (unchanged ▸ accepted)).elim
      | some actual =>
          have pending := List.mem_of_find?_eq_some lookup
          have actualInput := ((app).retained_envelopes_mem_inputs acceptingBefore.execution
            ((app).history_provenance initial horizon scheduler rawAccepting)
            ((app).history_inputRecall initial horizon scheduler rawAccepting)).pending actual
              pending
          have retainedInput := input_mem_prefix runtime leaks menu initial horizon scheduler
            acceptingBefore final prior finalTrace toFinal actual actualInput
          have sameId : actual.id = message.id := by
            simpa only [decide_eq_true_eq] using List.find?_some lookup
          have same := (app).input_identifier_injective_history initial horizon scheduler final
            rawFinal actual message retainedInput input sameId
          exact congrArg some same
    have pending := List.mem_of_find?_eq_some found
    have acceptingInput := ((app).retained_envelopes_mem_inputs acceptingBefore.execution
      ((app).history_provenance initial horizon scheduler rawAccepting)
      ((app).history_inputRecall initial horizon scheduler rawAccepting)).pending message pending
    obtain ⟨_native, following, handled, _nativeHandled⟩ := accepting_include_binding runtime leaks
      plan inputs horizon scheduler acceptingBefore rawAccepting acceptingAfter.execution message
        acceptingInput event candidate call noReceipt moved accepted
    have original := (PhaseRuntimeState.handle_attempt_eq runtime
      acceptingBefore.execution.application following message handled).symm.trans address
    have initialized : ∀ state ∈ initial.support, state.Ordered := by
      intro state positive
      obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan draw
    have orderedStart := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized (menu.toRawTrace initial horizon scheduler startTrace)
    have orderedClosed := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized (menu.toRawTrace initial horizon scheduler closedTrace)
    have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
      scheduler start closed startTrace closedTrace toClosed orderedStart
    have upper := phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
      scheduler closed acceptingBefore closedTrace prior toAccepting orderedClosed
    apply retired
    have generation := congrArg CommitAttemptId.generation original
    have phase := congrArg CommitAttemptId.phase original
    cases first : start.execution.application.attempt with
    | mk firstPhase firstGeneration =>
        cases second : closed.execution.application.attempt with
        | mk secondPhase secondGeneration =>
            simp only [first, second] at lower upper generation phase ⊢
            congr 1 <;> omega
  · intro received
    exact ((app).reaches_receipts_prefix initial horizon scheduler
      (menu.reaches_raw initial horizon scheduler afterClosed.reachesWithin)
        closed final rfl rfl).subset received

end Vegas.EventGraphRuntime.ReservedEpoch
