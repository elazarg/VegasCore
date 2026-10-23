/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryPreparationRepairMoves

/-! # Generated preparation failures in the actual source menu -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The proposal label does not change whether a literal move is a generated
unusable declaration. -/
theorem ProposalRecoveryMove.generatedPreparationFailure_ordinary
    (choice : Option (ProposalRecoveryMove Player L)) :
    GeneratedPreparationFailure (choice.map fun move => ordinary move.semantic) ↔
      GeneratedPreparationFailure choice := by
  cases choice <;> rfl

/-- At a binding cursor a nonmissing failed menu action is exactly a
generated unusable preparation. Withholding is a distinct publication case. -/
theorem ProtocolView.generatedPreparationFailure_of_binding_failure (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
      (move : CommitRecoveryMove Player L),
      move ∈ ProtocolView.recoveryAvailable who program view →
      ProtocolView.atCommit who program view = true → move.missing = false →
      move.action.IsFailure → ProposalRecoveryMove.GeneratedPreparationFailure
        (some (ProposalRecoveryMove.ordinary move)) := by
  intro Γ O program
  induction program with
  | ret => intro view move offered; cases offered.1
  | sample name fresh law next ih =>
      intro view move offered committing missing failed
      cases view with
      | inl => cases committing
      | inr view => exact ih view move offered committing missing failed
  | commit name owner fresh guard next ih =>
      intro view move offered committing missing failed
      cases view with
      | inr view => exact ih view move offered committing missing failed
      | inl view =>
          obtain ⟨value, _admitted, action⟩ := offered.1
          cases move with | mk original marker =>
            dsimp only at action missing failed
            cases action
            change value = .failure at failed
            subst value
            simp [ProposalRecoveryMove.GeneratedPreparationFailure,
              ProposalRecoveryMove.ordinary, missing]
  | reveal published owner name fresh source unresolved next ih =>
      intro view move offered committing missing failed
      cases view with
      | inl => cases committing
      | inr view => exact ih view move offered committing missing failed

end Vegas.SourceProgram
