/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochDelivery
import Vegas.Pending.ReservedEpochPendingBound

/-! # Receipt coverage derived at every genuine processing prefix

The pending-length premise of the physical batching law is discharged from
the raw activation budget. No conformity of any owner's submissions is used.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def submissionBudget (cycles : Nat) : Nat := cycles * Fintype.card Player

def horizon (cycles : Nat) : Nat :=
  cycles * cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles)

theorem actual_epoch_clears {length : Nat} (cycles : Nat) (tape : Tape Player length)
    (initial : PMF (app).State) (remaining cycle : Nat) (before after : (app).Execution)
    (trace : ((app).protocol initial (horizon (graph := graph) cycles)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, none, before⟩))
    (cursor : before.environmentRecall.length = cycle *
      cycleWidth (graph := graph) (submissionBudget (Player := Player) cycles))
    (epoch : tape.processes cycle = true) (players : Player → (app).Policy)
    (reached : after ∈ ((app).runRounds
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) players
        before.network.pending.length before).support) :
    after.network.pending = [] ∧
      (∀ message ∈ before.network.pending,
        message ∈ after.network.ledger ∧ ∃ accepted, (message.id, accepted) ∈ after.receipts) := by
  have capacity := pending_le_cycles runtime leaks (submissionBudget (Player := Player) cycles)
    tape initial cycles _ trace
  exact processing_epoch_clears runtime leaks (submissionBudget (Player := Player) cycles) tape
    players cycle before after cursor capacity epoch reached

end Vegas.EventGraphRuntime.ReservedEpoch
