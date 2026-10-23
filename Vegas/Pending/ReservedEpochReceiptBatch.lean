/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochEmptyProcessing
import Vegas.Pending.ReservedEpochTraceDelivery
import Interaction.ReactiveReceiptIdentity
import Vegas.Pending.ReservedEpochPendingBound

/-! # Every previously submitted raw envelope has a receipt after a full epoch -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem epoch_covers_submitted {length : Nat} (cycles : Nat) (tape : Tape Player length)
    (initial : PMF (app).State) (remaining cycle : Nat) (before after : (app).Execution)
    (trace : ((app).protocol initial (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (cursor : before.environmentRecall.length = cycle *
      cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles))
    (epoch : tape.processes cycle = true) (players : Player → (app).Policy)
    (reached : after ∈ ((app).runRounds
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) players
        (submissionBudget (Player := Player) cycles) before).support) :
    after.network.pending = [] ∧
      ∀ message ∈ before.network.inputs,
        message ∈ after.network.ledger ∧ ∃ accepted, (message.id, accepted) ∈ after.receipts := by
  have capacity := pending_le_cycles runtime leaks (submissionBudget (Player := Player) cycles)
    tape initial cycles _ trace
  obtain ⟨cleared, ledger, receipts, delivered⟩ := full_processing_epoch_clears runtime leaks
    (submissionBudget (Player := Player) cycles) tape players cycle before after cursor
      capacity epoch reached
  refine ⟨cleared, ?_⟩
  intro message submitted
  have retained := (app).pendingOrPublished_history
    (family runtime leaks (submissionBudget (Player := Player) cycles) tape) initial
      (horizon (graph := graph) cycles) trace
  rcases retained.inputs message submitted with pending | published
  · exact delivered message pending
  · refine ⟨?_, ?_⟩
    · rw [ledger]
      exact List.mem_append_left _ published
    · have identifiers := (app).receipt_identifiers_history initial
        (horizon (graph := graph) cycles)
          (family runtime leaks (submissionBudget (Player := Player) cycles) tape) _ trace
      have recorded : message.id ∈ before.receipts.map Prod.fst := by
        rw [identifiers]
        exact List.mem_map.mpr ⟨message, published, rfl⟩
      obtain ⟨receipt, member, equal⟩ := List.mem_map.mp recorded
      refine ⟨receipt.2, receipts.subset ?_⟩
      simpa only [← equal, Prod.mk.eta] using member

end Vegas.EventGraphRuntime.ReservedEpoch
