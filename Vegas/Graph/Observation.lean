/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.PublicEvaluation

/-! # Information retained by immutable graph observations -/

namespace Vegas.Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : VCtx Player L}

/-- Equal player observations include equality of every public field. -/
theorem publicValues_eq_of_observe_eq (who : Player) (left right : VEnv L Γ)
    (visible : observe who left = observe who right) :
    (PublicValues.ofVEnv left : PublicValues Γ) =
      (PublicValues.ofVEnv right : PublicValues Γ) := by
  funext name ty source
  exact congrArg (fun observation => observation.cells.get source) visible

/-- Extending a context by a foreign sealed field reveals neither its value
nor whether that value represents failure. -/
theorem observe_cons_sealed_congr (who owner : Player) (different : owner ≠ who)
    (name : VarId) (ty : L.Ty) (leftValue rightValue : L.Val ty)
    (left right : VEnv L Γ) (visible : observe who left = observe who right) :
    observe who (VEnv.cons (x := name) (τ := .sealed owner ty) leftValue left) =
      observe who (VEnv.cons (x := name) (τ := .sealed owner ty) rightValue right) := by
  change Observation.mk _ = Observation.mk _
  congr 1
  funext field binding source
  cases source with
  | here => simp [different]
  | there source =>
      have cell := congrArg (fun observation => observation.cells.get source) visible
      rcases binding with ⟨ty, visibility⟩
      cases visibility <;> exact cell

/-- Equality of observations after an immutable extension implies equality
on the preceding context. Thus later graph information retains earlier fields. -/
theorem observe_tail_eq (who : Player) (name : VarId) (binding : BindTy Player L)
    (left right : VEnv L ((name, binding) :: Γ))
    (visible : observe who left = observe who right) :
    observe who (VEnv.tail left) = observe who (VEnv.tail right) := by
  change Observation.mk _ = Observation.mk _
  congr 1
  funext field ty source
  have cell := congrArg (fun observation => observation.cells.get (.there source)) visible
  rcases ty with ⟨ty, visibility⟩
  cases visibility <;> exact cell

end Vegas.Graph
