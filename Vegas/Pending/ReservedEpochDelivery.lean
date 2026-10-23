/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochProcessing
import Vegas.Pending.ReservedEpochSlots
import Interaction.ReactiveReceipts

/-! # Delivery of every envelope at a reserved processing epoch -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A whole epoch runs on the existing reactive evaluator, for arbitrary raw
players and arbitrary application results. Every initial pending occurrence is
delivered; no response or new packet is interleaved with the reserved slots. -/
theorem processing_segment {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (players : Player → (app).Policy) (cycle slot : Nat)
    (packets : List (Message Player (app).Payload))
    (execution next : (app).Execution)
    (cursor : execution.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + slot)
    (room : slot + packets.length ≤ packetBudget)
    (epoch : tape.processes cycle = true) (pending : execution.network.pending = packets)
    (reached : next ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      packets.length execution).support) :
    next.network.pending = [] ∧ next.network.ledger = execution.network.ledger ++ packets ∧
      execution.receipts <+: next.receipts ∧
      (∀ message ∈ packets, ∃ accepted, (message.id, accepted) ∈ next.receipts) ∧
      next.recall = execution.recall ∧
      next.environmentRecall.length = execution.environmentRecall.length + packets.length := by
  induction packets generalizing slot execution next with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨pending, by simp, by rfl, by simp, rfl, by simp⟩
  | cons message rest ih =>
      have reserved : slot < packetBudget := by simp only [List.length_cons] at room; omega
      have roundEq : (app).round (family runtime leaks packetBudget tape) players execution =
          (app).dispatch players (process runtime leaks (execution.observeEnvironment app))
            execution := by
        simp only [ReactiveApplication.round, family, PMF.pure_bind]
        rw [cursor, processing_at runtime leaks packetBudget tape cycle slot _ reserved epoch]
      simp only [List.length_cons, ReactiveApplication.runRounds, roundEq] at reached
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have step := process_step runtime leaks players execution middle message rest pending moved
      have receipts : execution.receipts <+: middle.receipts := by
        rw [process_dispatch runtime leaks players execution message rest pending] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact (app).includePending_receipts_prefix execution message.id
      have nextCursor : middle.environmentRecall.length =
          cycle * cycleWidth (graph := graph) packetBudget + (slot + 1) := by
        rw [step.2.2.2.2, cursor]
        omega
      have nextRoom : slot + 1 + rest.length ≤ packetBudget := by
        simp only [List.length_cons] at room
        omega
      have tail := ih (slot + 1) middle next nextCursor nextRoom step.1 continued
      refine ⟨tail.1, ?_, receipts.trans tail.2.2.1, ?_, ?_, ?_⟩
      · rw [tail.2.1, step.2.1]
        simp only [List.append_assoc, List.singleton_append]
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · obtain ⟨accepted, acceptedAtStep⟩ := step.2.2.1
          exact ⟨accepted, tail.2.2.1.subset acceptedAtStep⟩
        · exact tail.2.2.2.1 selected later
      · exact tail.2.2.2.2.1.trans step.2.2.2.1
      · rw [tail.2.2.2.2.2, step.2.2.2.2]
        simp only [List.length_cons]
        omega

end Vegas.EventGraphRuntime.ReservedEpoch
