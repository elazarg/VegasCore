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

end Vegas.EventGraphRuntime.ReservedEpoch
