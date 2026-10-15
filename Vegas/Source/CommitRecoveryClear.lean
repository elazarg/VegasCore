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

/-- If the actual raw step has no exclusion, its automatically closed source
point has the original source transition law, including its nature draw. -/
theorem step_empty_point (state : CommitRecoveryState program) (empty : state.excluded = ∅)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (clear : ∀ result ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support,
      result.2 = ∅) :
    (state.step joint).map (·.point) =
      ProtocolState.step program state.point (fun who => (joint who).map (·.action)) := by
  let raw := ProtocolState.recoveryStep program state.point state.excluded joint
  let monotone := fun result (supported : result ∈ raw.support) =>
    ProtocolState.recoveryStep_excluded_monotone program state.point state.excluded joint
      result supported
  change ((pmfToSubtype raw monotone).map
    (fun result => (state.install result.1 result.2).close)).map (·.point) = _
  rw [PMF.map_comp]
  have agrees : ∀ result ∈ (pmfToSubtype raw monotone).support,
      (state.install result.1 result.2).close.point = result.1.1 := by
    intro result member
    have rawMember : result.1 ∈ raw.support := by
      rw [← map_val_pmfToSubtype raw monotone]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
    apply close_point_of_no_new_failure
    simp only [NewFailure, install, clear result.1 rawMember, Finset.empty_sdiff,
      Finset.not_nonempty_empty, not_false_eq_true]
  trans (pmfToSubtype raw monotone).map (fun result => result.1.1)
  · apply GameTheory.Math.Probability.map_congr_on_support
    exact agrees
  · rw [map_pmfToSubtype raw monotone Prod.fst]
    simpa only [raw, empty] using ProtocolState.recoveryStep_empty_point program state.point joint

end CommitRecoveryState
end Vegas.SourceProgram
