/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization

/-! # The deviator's choice in its own phase

In a phase of its own binding or guarded disclosure, a deviator within the
permitted menu chooses at some roster visit, from its complete native input.
Every other player is silent. The phase leaves the decoded source
configuration at a source successor of the phase's entry configuration, and the
deviator's native traffic at the end of the phase determines its new source
view. Its traffic at the end of the phase has a law that depends on the native
execution only through its traffic at the start.

Together with an entry factorization of that traffic through the deviator's
source view, this makes the deviator's source choice a behavioral choice of
its source view, and restores the factorization at the successor.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- The owner's view after its guarded disclosure determines its view before
and its choice, which it records in its own history. -/
theorem reveal_owner_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {who : Player} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment who payload))
    (left right : Config Player L Γ) (first second : Bool)
    (same : (revealSuccessor published selected left first).view who =
      (revealSuccessor published selected right second).view who) :
    left.view who = right.view who ∧ first = second := by
  refine ⟨reveal_view_reflects who published selected left right first second same, ?_⟩
  have last := congrArg (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
    view.2.getLast?) same
  simp only [Config.view, revealSuccessor, Function.update_self, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.some.injEq, OwnAction.reveal.injEq,
    true_and] at last
  exact last

end Vegas
