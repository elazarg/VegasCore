/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochWaiting
import Vegas.Pending.ReservedEpochWaitingPackets
import Vegas.Pending.ReservedEpochAcceptingEpoch
import Vegas.Pending.ReservedEpochCompletion
import Vegas.Pending.ReservedEpochPendingBound
import Vegas.Pending.ReservedEpochOpportunity
import Vegas.Pending.PhaseOwnCount
import Vegas.Pending.ReservedEpochArrival

/-! # Protected current packets receive accepting receipts against raw opponents -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem receipt_at_processing_boundary {length : Nat} (cycles : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (remaining sentCycle slot cycle : Nat)
    (before final : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (orderedBefore : before.application.Ordered)
    (cursor : before.environmentRecall.length =
      sentCycle * cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles) + slot)
    (afterProcessing : submissionBudget (Player := Player) cycles ≤ slot)
    (quiet : ∀ later, sentCycle < later → later < cycle → tape.processes later = false)
    (later : sentCycle < cycle) (running : cycle < cycles) (epoch : tape.processes cycle = true)
    (clock : before.application.current.native.clock = sentCycle)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (event : graph.EventId)
    (certificate : ReadyCall before.application message.payload.packet.call event) (entered : Nat)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (stamp : before.application.current.native.activatedAt event = some entered)
    (timely : before.application.current.native.WithinDeadline runtime event)
    (inTime : cycle - entered < runtime.deadline event)
    (clean : PhaseCount.OwnCountClean runtime leaks message.sender before)
    (covered : ∀ past view action, action ∈ (players message.sender past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks message.sender past view action)
    (reached : final ∈ ((app).runRounds
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) players remaining
      before).support) : (message.id, true) ∈ final.receipts := by
  let capacity := submissionBudget (Player := Player) cycles
  let width := cycleWidth (graph := graph) capacity
  let scheduler := family runtime leaks capacity tape
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have accounted := (app).raw_trace_horizon initial (horizon (graph := graph) cycles) scheduler
    trace
  have clockEq := clock_history runtime leaks capacity tape plan inputs
    (horizon (graph := graph) cycles) ⟨remaining, none, before⟩ trace
  have starts : before.environmentRecall.length < cycle * width := by
    apply (Nat.div_lt_iff_lt_mul (cycleWidth_pos capacity)).mp
    rw [← clockEq, clock]
    exact later
  have scaled := Nat.mul_le_mul_right width (Nat.succ_le_of_lt running)
  change (cycle + 1) * width ≤ cycles * width at scaled
  rw [Nat.add_mul, Nat.one_mul] at scaled
  have capacityBound : capacity < width := by dsimp [width, cycleWidth]; omega
  let waitCount := cycle * width - before.environmentRecall.length
  have waitBound : waitCount ≤ remaining := by
    change before.environmentRecall.length + remaining = cycles * width at accounted
    omega
  have waitSum : waitCount + (remaining - waitCount) = remaining := by omega
  have waitLaw := (app).runRounds_add scheduler players waitCount (remaining - waitCount) before
  rw [waitSum] at waitLaw
  rw [waitLaw] at reached
  obtain ⟨atEpoch, waited, suffix⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have epochCursor : atEpoch.environmentRecall.length = cycle * width := by
    have lengthEq := (app).runRounds_environmentRecall_length scheduler players waitCount before
      atEpoch waited
    dsimp [waitCount] at lengthEq
    omega
  have prefixTrace : ((app).protocol initial (horizon (graph := graph) cycles) scheduler).Trace
      (some ⟨(remaining - waitCount) + waitCount, none, before⟩) := by
    simpa only [Nat.sub_add_cancel waitBound] using trace
  obtain ⟨epochTrace⟩ := (app).raw_trace_runRounds initial (horizon (graph := graph) cycles)
    scheduler players (remaining - waitCount) waitCount before atEpoch prefixTrace waited
  have waitRoom : before.environmentRecall.length + waitCount ≤ cycle * width := by
    dsimp [waitCount]
    omega
  obtain ⟨epochRequest, epochStamp⟩ := request_until_processing_boundary runtime leaks capacity tape
    players plan ordered inputs (horizon (graph := graph) cycles) (remaining - waitCount) waitCount
      before atEpoch prefixTrace orderedBefore sentCycle slot cycle cursor afterProcessing quiet
        waitRoom message.sender ⟨message.payload.attempt, event⟩ entered request stamp timely inTime
          waited
  have epochCertificate := ReadyCall.runRounds runtime leaks players scheduler waitCount before
    atEpoch orderedBefore waited (request.1.symm.trans epochRequest.1) message.payload.packet.call
      event certificate
  have epochPending := pending_until_processing_boundary runtime leaks capacity tape players
    sentCycle slot cycle waitCount before atEpoch cursor afterProcessing quiet waitRoom message
      pending waited
  have epochClean := PhaseCount.ownCountClean_runRounds runtime leaks message.sender players covered
    scheduler waitCount before atEpoch clean waited
  have epochOrdered := (ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_seedOrder runtime leaks) players).runRounds scheduler waitCount before
      atEpoch orderedBefore waited
  have epochClock : atEpoch.application.current.native.clock = cycle := by
    rw [clock_history runtime leaks capacity tape plan inputs (horizon (graph := graph) cycles)
      ⟨remaining - waitCount, none, atEpoch⟩ epochTrace, epochCursor]
    simpa only [Nat.add_zero] using cursor_div capacity cycle 0 (cycleWidth_pos capacity)
  have epochTimely : atEpoch.application.current.native.WithinDeadline runtime event := by
    simpa only [State.WithinDeadline, epochStamp, epochClock] using inTime
  have pendingBound : atEpoch.network.pending.length ≤ capacity :=
    pending_le_cycles runtime leaks capacity tape initial cycles _ epochTrace
  let processCount := atEpoch.network.pending.length
  have enough : processCount ≤ remaining - waitCount := by
    have epochAccounted := (app).raw_trace_horizon initial (horizon (graph := graph) cycles)
      scheduler epochTrace
    rw [epochCursor] at epochAccounted
    change cycle * width + (remaining - waitCount) = cycles * width at epochAccounted
    dsimp [processCount]
    omega
  have processSum : processCount + (remaining - waitCount - processCount) =
      remaining - waitCount := by omega
  have processLaw := (app).runRounds_add scheduler players processCount
    (remaining - waitCount - processCount) atEpoch
  rw [processSum] at processLaw
  rw [processLaw] at suffix
  obtain ⟨afterEpoch, processed, future⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffix)
  have actualEpochTrace : ((app).protocol initial (horizon (graph := graph) cycles) scheduler).Trace
      (some ⟨(remaining - waitCount - processCount) + atEpoch.network.pending.length,
        none, atEpoch⟩) := by
    have lengthEq : (remaining - waitCount - processCount) + atEpoch.network.pending.length =
        remaining - waitCount := by
      change (remaining - waitCount - processCount) + processCount = remaining - waitCount
      omega
    rw [lengthEq]
    exact epochTrace
  have accepted := processing_segment_receipt runtime leaks capacity tape players plan
    ordered inputs (horizon (graph := graph) cycles) (remaining - waitCount - processCount)
      cycle 0 atEpoch.network.pending atEpoch afterEpoch actualEpochTrace epochOrdered
        (by simpa only [Nat.add_zero] using epochCursor) (by simpa using pendingBound) epoch rfl
          message epochPending event epochCertificate epochRequest epochTimely epochClean.2
            processed
  exact ((app).receipt_policyInvariant players (message.id, true)).runRounds scheduler
    (remaining - waitCount - processCount) afterEpoch final accepted future

theorem protected_pending_receipt {length : Nat} (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (players : Player → (app).Policy) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (remaining : Nat) (before final : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) (family runtime leaks (packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (afterProcessing : packetCapacity runtime ≤ before.environmentRecall.length %
      cycleWidth (graph := graph) (packetCapacity runtime))
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (event : graph.EventId)
    (certificate : ReadyCall before.application message.payload.packet.call event) (entered : Nat)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (stamp : before.application.current.native.activatedAt event = some entered)
    (protection : before.application.current.native.clock - entered + (processingGap + 1) <
      runtime.deadline event)
    (clean : PhaseCount.OwnCountClean runtime leaks message.sender before)
    (covered : ∀ past view action, action ∈ (players message.sender past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks message.sender past view action)
    (reached : final ∈ ((app).runRounds (family runtime leaks (packetCapacity runtime) tape)
      players remaining before).support) : (message.id, true) ∈ final.receipts := by
  let capacity := packetCapacity runtime
  let width := cycleWidth (graph := graph) capacity
  let scheduler := family runtime leaks capacity tape
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let sentCycle := before.application.current.native.clock
  let slot := before.environmentRecall.length % width
  obtain ⟨draw, state⟩ := activation_state_history runtime leaks capacity tape plan ordered maximal
    inputs (executionHorizon runtime) ⟨remaining, none, before⟩ trace
  have orderedBefore := state.geometry.valid.2.1
  have started : entered ≤ sentCycle :=
    state.geometry.valid.1.active.activated_le event entered stamp
  have timely : before.application.current.native.WithinDeadline runtime event := by
    simp only [State.WithinDeadline, stamp]
    omega
  have cursor : before.environmentRecall.length = sentCycle * width + slot := by
    have divided := Nat.mod_add_div before.environmentRecall.length width
    rw [Nat.mul_comm width] at divided
    have clockEq := state.clock.2
    change sentCycle = 0 + before.environmentRecall.length / width at clockEq
    rw [Nat.zero_add] at clockEq
    rw [← clockEq] at divided
    dsimp [slot]
    omega
  have source : ((app).protocol initial (executionHorizon runtime) scheduler).Trace
      (some ⟨0 + remaining, none, before⟩) := by
    simpa only [Nat.zero_add] using trace
  obtain ⟨finalTrace⟩ := (app).raw_trace_runRounds initial (executionHorizon runtime) scheduler
    players 0 remaining before final source reached
  have complete := terminal_history_complete runtime leaks tape plan ordered maximal inputs
    ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
  have finalLost : ¬ final.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩ := by
    intro requested
    obtain ⟨phase, installed, _inside⟩ := requested.2.1
    rw [complete.1] at installed
    cases installed
  have accounted := (app).raw_trace_horizon initial (executionHorizon runtime) scheduler trace
  change before.environmentRecall.length + remaining = completionCycles runtime * width at accounted
  have runningBoundary : ∀ cycle,
      (∀ later, sentCycle < later → later < cycle → tape.processes later = false) →
      cycle - entered < runtime.deadline event → cycle < completionCycles runtime := by
    intro cycle quiet inTime
    by_contra exhausted
    have scaled := Nat.mul_le_mul_right width (Nat.le_of_not_gt exhausted)
    have room : before.environmentRecall.length + remaining ≤ cycle * width := by
      rw [accounted]
      exact scaled
    have retained := request_until_processing_boundary runtime leaks capacity tape players plan
      ordered inputs (executionHorizon runtime) 0 remaining before final source orderedBefore
        sentCycle slot cycle cursor afterProcessing quiet room message.sender
          ⟨message.payload.attempt, event⟩ entered request stamp timely inTime reached
    exact finalLost retained.1
  have nextRunning : sentCycle + 1 < completionCycles runtime := by
    apply runningBoundary (sentCycle + 1)
    · intro later after before
      omega
    · omega
  obtain ⟨cycle, selected, lower, upper, epoch⟩ := tape.nextProcessingEpoch_bounded
    (completionCycles runtime) activationGap processingGap (sentCycle + 1) gaps nextRunning
  have quiet : ∀ later, sentCycle < later → later < cycle → tape.processes later = false := by
    intro later after before
    cases marked : tape.processes later with
    | false => rfl
    | true =>
        have minimum := (tape.nextProcessingEpoch_spec _ cycle selected).2.2 later (by omega) marked
        omega
  have inTime : cycle - entered < runtime.deadline event := by omega
  have running := runningBoundary cycle quiet inTime
  exact receipt_at_processing_boundary runtime leaks (completionCycles runtime) tape
    players plan ordered inputs remaining sentCycle slot cycle before final trace orderedBefore
      cursor afterProcessing quiet (by omega) running epoch rfl message pending event certificate
        entered request stamp timely inTime clean covered reached

end Vegas.EventGraphRuntime.ReservedEpoch
