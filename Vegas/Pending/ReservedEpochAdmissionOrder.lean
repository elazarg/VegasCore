/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochAcceptingDelivery

/-! # Same-episode first processing order preserves timely binding acceptance -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem receipt_of_later_processing_deadline {length : Nat} (cycles : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (remaining sentCycle laterSend earlyEpoch laterEpoch : Nat)
    (before final : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (orderedBefore : before.application.Ordered)
    (afterProcessing : submissionBudget (Player := Player) cycles ≤
      before.environmentRecall.length %
        cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles))
    (sendOrder : sentCycle ≤ laterSend)
    (earlySelected : tape.nextProcessingEpoch (sentCycle + 1) = some earlyEpoch)
    (lateSelected : tape.nextProcessingEpoch (laterSend + 1) = some laterEpoch)
    (running : laterEpoch < cycles)
    (clock : before.application.current.native.clock = sentCycle)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (event : graph.EventId)
    (certificate : ReadyCall before.application message.payload.packet.call event) (entered : Nat)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (stamp : before.application.current.native.activatedAt event = some entered)
    (timely : before.application.current.native.WithinDeadline runtime event)
    (laterInTime : laterEpoch - entered < runtime.deadline event)
    (clean : PhaseCount.OwnCountClean runtime leaks message.sender before)
    (covered : ∀ past view action, action ∈ (players message.sender past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks message.sender past view action)
    (reached : final ∈ ((app).runRounds
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) players remaining
      before).support) : (message.id, true) ∈ final.receipts := by
  let capacity := submissionBudget (Player := Player) cycles
  let width := cycleWidth (graph := graph) capacity
  let slot := before.environmentRecall.length % width
  have earlySpec := tape.nextProcessingEpoch_spec (sentCycle + 1) earlyEpoch earlySelected
  have epochOrder := tape.nextProcessingEpoch_mono (sentCycle + 1) (laterSend + 1)
    earlyEpoch laterEpoch (by omega) earlySelected lateSelected
  have quiet : ∀ later, sentCycle < later → later < earlyEpoch →
      tape.processes later = false := by
    intro later lower upper
    cases marked : tape.processes later with
    | false => rfl
    | true =>
        have earliest := earlySpec.2.2 later (by omega) marked
        omega
  have clockEq := clock_history runtime leaks capacity tape plan inputs
    (horizon (graph := graph) cycles) ⟨remaining, none, before⟩ trace
  have cursor : before.environmentRecall.length = sentCycle * width + slot := by
    rw [clock] at clockEq
    have divided := Nat.mod_add_div before.environmentRecall.length width
    rw [Nat.mul_comm width, ← clockEq] at divided
    dsimp [slot]
    omega
  exact receipt_at_processing_boundary runtime leaks cycles tape players plan ordered
    inputs remaining sentCycle slot earlyEpoch before final trace orderedBefore cursor
      afterProcessing quiet (by omega) (by omega) earlySpec.2.1 clock message pending event
        certificate entered request stamp timely (by omega) clean covered reached

end Vegas.EventGraphRuntime.ReservedEpoch
