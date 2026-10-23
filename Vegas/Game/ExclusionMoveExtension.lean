/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ExclusionMoveGame

/-! # Intended equilibrium extension through mandatory moves

The mandatory-move game embeds the intended game and restricts the exclusion
game. Voluntary failures can be restored by a local comparator once the fixed
exclusion payoff bounds all nonexcluded terminal utilities from below.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Intended actions bind a value or open, and never voluntarily fail. -/
theorem ProtocolView.intendedAvailable_not_failure (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
    (action : OwnAction Player L) → action ∈ ProtocolView.intendedAvailable who program view →
      ¬ action.IsFailure
  | _, _, .ret _, _, _, impossible => impossible.elim
  | _, _, .sample _ _ _ next, view, action, offered => by
      cases view with
      | inl _ => exact offered.elim
      | inr later => exact intendedAvailable_not_failure who next later action offered
  | _, _, .commit _ _ _ _ next, view, action, offered => by
      cases view with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := offered
          simp [OwnAction.IsFailure]
      | inr later => exact intendedAvailable_not_failure who next later action offered
  | _, _, .reveal _ _ _ _ _ _ next, view, action, offered => by
      cases view with
      | inl _ =>
          subst offered
          simp [OwnAction.IsFailure]
      | inr later => exact intendedAvailable_not_failure who next later action offered

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem intendedMenu_not_failure (who : Player) (view : setup.ProtocolView who)
    (choice : Option (OwnAction Player L)) (offered : choice ∈ setup.intendedMenu who view)
    (action : OwnAction Player L) (selected : choice = some action) : ¬ action.IsFailure := by
  subst selected
  cases view with
  | none => cases offered
  | some view =>
      exact ProtocolView.intendedAvailable_not_failure who setup.program view action offered.2

end Setup
end Vegas.SourceProgram
