/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryPreparationMenu

/-! # Actual binding-cursor and omission bits of a generated source failure -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A generated unusable declaration has the accepted, nonmissing failure
marker. Typed values that later fail a guard are excluded from this event. -/
theorem ProposalRecoveryMove.generatedPreparationFailure_flags
    (move : CommitRecoveryMove Player L)
    (bad : GeneratedPreparationFailure (some (ordinary move))) :
    move.missing = false ∧ move.action.IsFailure := by
  cases move with | mk action missing =>
    cases action with
    | commit owner name payload result =>
        cases result with
        | failure => simpa only [GeneratedPreparationFailure, ordinary, Option.elim_some,
            OwnAction.IsFailure, and_true] using bad
        | success => exact bad.2.elim
    | reveal => exact bad.2.elim

/-- The actual source menu locates a generated failure at a binding cursor. -/
theorem ProtocolView.atCommit_of_generatedPreparationFailure (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
      (move : CommitRecoveryMove Player L),
      move ∈ ProtocolView.recoveryAvailable who program view →
      ProposalRecoveryMove.GeneratedPreparationFailure
        (some (ProposalRecoveryMove.ordinary move)) →
      ProtocolView.atCommit who program view = true := by
  intro Γ O program
  induction program with
  | ret => intro view move offered; cases offered.1
  | sample name fresh law next ih =>
      intro view move offered bad
      cases view with
      | inl => cases offered.1
      | inr view => exact ih view move offered bad
  | commit name owner fresh guard next ih =>
      intro view move offered bad
      cases view with
      | inl => rfl
      | inr view => exact ih view move offered bad
  | reveal published owner name fresh source unresolved next ih =>
      intro view move offered bad
      cases view with
      | inr view => exact ih view move offered bad
      | inl view =>
          obtain ⟨bit, action⟩ := offered.1
          cases move with | mk original missing =>
            dsimp only at action
            cases action
            exact bad.2.elim

end Vegas.SourceProgram
