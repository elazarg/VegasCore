/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureBehavioral

/-! # Authentic source disclosure support

Normalized source policies prescribe true only when the owner's binding can be opened.
Deferred guards still determine the publication result.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported authentic source choice either withholds or opens a successful binding.
The publication itself may fail its deferred guards. -/
theorem authentic_reveal_supported
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (source : Config Player L Γ)
    (authentic : (profile owner).AuthenticDisclosures
      (.reveal published owner name fresh binding unresolved next))
    (active : owner ∉ source.defaulted)
    (disclose : Bool)
    (supported : disclose ∈ (revealKernel profile (source.view owner) active).support) :
    disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ source.state.get binding = .success value := by
  cases disclose with
  | false => exact Or.inl rfl
  | true =>
      have fixed := authentic.1 rfl (source.view owner) active true supported
      change (true &&
        (((sourceObserve owner source.state).cells.get binding).getD .failure).isSuccess) = true
        at fixed
      simp only [sourceObserve, Env.get, ite_true, Option.getD_some, Bool.true_and] at fixed
      change (source.state.get binding).isSuccess = true at fixed
      cases result : source.state.get binding with
      | failure => simp only [result, PublicationResult.isSuccess, Bool.false_eq_true] at fixed
      | success value => exact Or.inr ⟨value, rfl, rfl⟩

end Vegas
