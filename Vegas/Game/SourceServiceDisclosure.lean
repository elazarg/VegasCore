/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Game.SourceServiceStep
import Vegas.Game.RevealServiceRosterPolicy

/-! # Effective guarded source disclosures in the native service

The actual deferred-check result decides whether an authentic opening exists.
Normalized source policies prescribe true only in the successful branch. No
assumption that every initialized or newly committed value passes its future
guard is needed for these local correspondences.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported effective source choice either withholds or has a
successful deferred-check result. This applies to the actual behavioral
normalization, including its posterior at unreachable source observations. -/
theorem effective_reveal_supported
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (source : Config Player L Γ)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (disclose : Bool) (supported : disclose ∈ (revealKernel profile (source.view owner)).support) :
    disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ disclosureResult published binding source true = .success value := by
  cases disclose with
  | false => exact Or.inl rfl
  | true =>
      have fixed := effective.1 rfl (source.view owner) true supported
      change effectiveDisclosureView published binding source.registry source.revelations
        (sourceObserve owner source.state) true = true at fixed
      rw [effectiveDisclosureView_observe] at fixed
      cases result : disclosureResult published binding source true with
      | failure => simp only [effectiveDisclosure, result, Bool.false_eq_true] at fixed
      | success value => exact Or.inr ⟨value, rfl, rfl⟩

end Vegas
