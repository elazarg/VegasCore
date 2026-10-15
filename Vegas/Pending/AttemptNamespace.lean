/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime

/-! # Physical attempt addresses and authenticated packet namespaces

Stable source event identities are paired with their phase and global retry
generation. Retired native outcomes remain available for public projection.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A phase and its retry number identify one physical event namespace. -/
structure CommitAttemptId where
  phase : Nat
  generation : Nat
  deriving DecidableEq

/-- Physical event identity includes the semantic graph event. -/
structure CommitAttemptEvent (graph : Vegas.EventGraph Player L) where
  attempt : CommitAttemptId
  event : graph.EventId
  deriving DecidableEq

/-- An authentic emitted envelope keeps the attempt in which it was made. -/
structure CommitAttemptPacket (graph : Vegas.EventGraph Player L) where
  attempt : CommitAttemptId
  packet : WitnessedPacket graph

/-- Readiness authorizes one particular physical attempt, not only a source name. -/
def CommitAttemptPacket.tokenValid (packet : CommitAttemptPacket graph)
    (current : CommitAttemptId) : Bool :=
  decide (packet.attempt = current) && packet.packet.tokenValid

omit [DecidableEq Player] in
theorem CommitAttemptPacket.tokenValid_retired (packet : CommitAttemptPacket graph)
    (current : CommitAttemptId) (retired : packet.attempt ≠ current) :
    packet.tokenValid current = false := by
  simp only [tokenValid, retired, decide_false, Bool.false_and]

/-- Each retired record retains the complete semantic result of that attempt.
Only its public projection is exposed by the application. -/
structure RetiredCommitAttempt (graph : Vegas.EventGraph Player L) where
  attempt : CommitAttemptId
  state : State graph

end Vegas.EventGraphRuntime
