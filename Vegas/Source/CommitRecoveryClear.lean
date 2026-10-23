/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryInformation

/-! # Exact source-step projection before recovery exclusion -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Before any owner is excluded, the semantic marginal of an actual recovery
instruction is exactly the original typed source instruction. -/
theorem recoveryStep_empty_point : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (joint : Player → Option (CommitRecoveryMove Player L)),
    (recoveryStep program point ∅ joint).map Prod.fst =
      step program point (fun who => (joint who).map (·.action))
  | _, _, .ret _, _, _ => by simp [recoveryStep, step, PMF.pure_map]
  | _, _, .sample _ _ _ next, point, joint => by
      cases point with
      | inl _ => simp only [recoveryStep, step, Sum.elim_inl, PMF.map_comp]; rfl
      | inr later =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [PMF.map_comp, ← recoveryStep_empty_point next later joint, PMF.map_comp]
          rfl
  | _, _, .commit _ _ _ _ next, point, joint => by
      cases point with
      | inl _ => simp [recoveryStep, step, PMF.pure_map]
      | inr later =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [PMF.map_comp, ← recoveryStep_empty_point next later joint, PMF.map_comp]
          rfl
  | _, _, .reveal _ _ _ _ _ _ next, point, joint => by
      cases point with
      | inl _ => simp [recoveryStep, step, PMF.pure_map]
      | inr later =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [PMF.map_comp, ← recoveryStep_empty_point next later joint, PMF.map_comp]
          rfl

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem close_point_of_no_new_failure (state : CommitRecoveryState program)
    (clear : ¬ state.NewFailure) : state.close.point = state.point := by
  unfold close
  split
  · simp only [atPoint]
  · split <;> rfl

theorem close_generation_of_no_new_failure (state : CommitRecoveryState program)
    (clear : ¬ state.NewFailure) : state.close.generation = state.generation := by
  unfold close
  split
  · simp only [atPoint]
  · split <;> rfl

end CommitRecoveryState
end Vegas.SourceProgram
