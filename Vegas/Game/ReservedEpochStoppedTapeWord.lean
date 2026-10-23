/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochRetiredReceipt

/-! # Old pending tape bits at the original physical attempt exit -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- Instantiate the existing behavioral evaluator at the actual starting
history, retaining its literal prefix when selecting a complete continuation. -/
theorem complete_rounds_extension [Finite Player] (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ menu.actions who past view)
    (remaining : Nat) (execution : (app).Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩)) :
    ∃ (final : (app).Execution)
      (finalTrace : (menu.protocol initial horizon scheduler).Trace
        (some ⟨0, none, final⟩)),
      final ∈ ((app).runRounds scheduler players remaining execution).support ∧
        TracePrefix trace finalTrace := by
  classical
  let _ : Fintype Player := Fintype.ofFinite Player
  let model := menu.information initial horizon scheduler
  let profile := fun who => menu.restrictPolicy initial horizon scheduler who (players who)
  let history : (menu.protocol initial horizon scheduler).History :=
    ⟨some ⟨remaining, none, execution⟩, trace⟩
  let fuel := (app).rank horizon history.state
  obtain ⟨last, supported⟩ := (model.runBehavioralFrom profile fuel history).support_nonempty
  have extended := model.runBehavioralFrom_reachesWithin profile fuel history last supported
  have mapped : last.state ∈
      ((model.runBehavioralFrom profile fuel history).map History.state).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨last, supported, rfl⟩
  have decoded : menu.decodeProfile initial horizon scheduler profile = players := by
    funext who
    exact menu.decode_restrictPolicy_of_covered initial horizon scheduler who (players who)
      (covered who)
  rw [menu.run_eq_finish initial horizon scheduler profile fuel history le_rfl, decoded] at mapped
  change last.state ∈ ((app).finish initial horizon scheduler players
    (some ⟨remaining, none, execution⟩)).support at mapped
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at mapped
  rcases last with ⟨state, finalTrace⟩
  obtain ⟨final, reached, equal⟩ := PMF.support_map .. ▸ mapped
  change some (⟨0, none, final⟩ : (app).Control) = state at equal
  subst state
  exact ⟨final, finalTrace, reached, extended.tracePrefix⟩

/-- The old pending certified packet's exact finite tape bit is already fixed at the
original namespace exit. The complete continuation is selected from the SAME
literal history, and retirement forbids a later first true receipt. -/
theorem stopped_pending_receipt_iff_epoch {length : Nat} (cycles : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (menu : (app).ResponseMenu) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (remaining closedRemaining used sentCycle slot : Nat)
    (before closed : (app).Execution)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (closedTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨closedRemaining, none, closed⟩))
    (kept : TracePrefix trace closedTrace)
    (retired : closed.application.attempt ≠ before.application.attempt)
    (path : closed ∈ ((app).runRounds
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) players used
        before).support)
    (admissible : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ menu.actions who past view)
    (cursor : before.environmentRecall.length = sentCycle *
      cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles) + slot)
    (afterProcessing : submissionBudget (Player := Player) cycles ≤ slot)
    (clock : before.application.current.native.clock = sentCycle)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (event : graph.EventId)
    (certificate : ReadyCall before.application message.payload.packet.call event)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (clean : PhaseCount.OwnCountClean runtime leaks message.sender before)
    (covered : ∀ past view action, action ∈ (players message.sender past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks message.sender past view action) :
    ((message.id, true) ∈ closed.receipts ↔
      ∃ epoch, tape.nextProcessingEpoch (sentCycle + 1) = some epoch ∧ epoch < cycles ∧
        epoch - entered < runtime.deadline event) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let bound := horizon (graph := graph) cycles
  let scheduler := family runtime leaks (submissionBudget (Player := Player) cycles) tape
  have rawStart := menu.toRawTrace initial bound scheduler trace
  have rawClosed := menu.toRawTrace initial bound scheduler closedTrace
  have firstBudget := (app).raw_trace_horizon initial bound scheduler rawStart
  have closedBudget := (app).raw_trace_horizon initial bound scheduler rawClosed
  have elapsed := (app).runRounds_environmentRecall_length scheduler players used before closed path
  have remainingSum : used + closedRemaining = remaining := by
    change before.environmentRecall.length + remaining = bound at firstBudget
    change closed.environmentRecall.length + closedRemaining = bound at closedBudget
    omega
  obtain ⟨final, finalTrace, future, extension⟩ := complete_rounds_extension runtime leaks menu
    initial bound scheduler players admissible closedRemaining closed closedTrace
  have whole : final ∈ ((app).runRounds scheduler players remaining before).support := by
    rw [← remainingSum, (app).runRounds_add scheduler players used closedRemaining before,
      PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨closed, path, future⟩
  have input := ((app).retained_envelopes_mem_inputs before
    ((app).history_provenance initial bound scheduler rawStart)
    ((app).history_inputRecall initial bound scheduler rawStart)).pending message pending
  have finalInput := input_mem_prefix runtime leaks menu initial bound scheduler
    ⟨remaining, none, before⟩ ⟨0, none, final⟩ trace finalTrace (kept.trans extension) message input
  have receipt := retired_event_receipt_iff runtime leaks menu plan inputs bound scheduler
    ⟨remaining, none, before⟩ ⟨closedRemaining, none, closed⟩ ⟨0, none, final⟩ trace closedTrace
      finalTrace kept extension retired message finalInput request.1
  exact receipt.symm.trans (pending_receipt_iff_timely_epoch runtime leaks cycles tape
    players plan ordered inputs remaining sentCycle slot before final rawStart cursor
      afterProcessing
      clock message pending event certificate request entered stamp clean covered
        whole)

end Vegas.EventGraphRuntime.ReservedEpoch
