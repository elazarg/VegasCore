/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedScheduler

/-! # Value-erased local calendar queries

The complete clocked packet word remains available for recall provenance. The
actual calendar receives only elapsed clocks, message identifiers and immutable
readiness authorization, so opening values and evidence never enter its query.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

structure PhaseSeedEmission (graph : Vegas.EventGraph Player L) where
  clock : Nat
  identifier : MessageId Player
  authorized : Bool
  deriving DecidableEq

structure PhaseSeedOperationalInput (graph : Vegas.EventGraph Player L) where
  elapsed : Nat
  activationClocks : List Nat
  emissions : List (PhaseSeedEmission graph)
  deriving DecidableEq

namespace PhaseSeedInput

def operationalEmission (current : CommitAttemptId)
    (emission : Nat × Message Player (CommitAttemptPacket graph)) : PhaseSeedEmission graph :=
  ⟨emission.1, emission.2.id, emission.2.payload.tokenValid current⟩

def operational (current : CommitAttemptId) (input : PhaseSeedInput graph) :
    PhaseSeedOperationalInput graph :=
  ⟨input.elapsed, input.activationClocks, input.emissions.map (operationalEmission current)⟩

omit [DecidableEq Player] in
/-- Replacing the declared opening and its evidence leaves every calendar-visible
field unchanged, with the complete raw message still retained in actual recall. -/
theorem operationalEmission_opening (current attempt : CommitAttemptId) (clock : Nat)
    (identifier : MessageId Player) (event : graph.EventId) (handle : Handle graph)
    (first second : Raw L) (firstEvidence secondEvidence : Option (OpeningFact graph))
    (token : Option (ReadinessToken graph)) :
    operationalEmission current
      (clock, ⟨identifier, ⟨attempt, ⟨.opening event handle first, firstEvidence, token⟩⟩⟩) =
      operationalEmission current
        (clock, ⟨identifier,
          ⟨attempt, ⟨.opening event handle second, secondEvidence, token⟩⟩⟩) := by
  rfl

omit [DecidableEq Player] in
/-- Commit evidence is also omitted from the actual calendar query. -/
theorem operationalEmission_commitment (current attempt : CommitAttemptId) (clock : Nat)
    (identifier : MessageId Player) (event : graph.EventId) (handle : Handle graph)
    (firstEvidence secondEvidence : Option (OpeningFact graph))
    (token : Option (ReadinessToken graph)) :
    operationalEmission current
      (clock, ⟨identifier, ⟨attempt, ⟨.commitment event handle, firstEvidence, token⟩⟩⟩) =
      operationalEmission current
        (clock, ⟨identifier, ⟨attempt, ⟨.commitment event handle, secondEvidence, token⟩⟩⟩) := by
  rfl

end PhaseSeedInput

end Vegas.EventGraphRuntime
