/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryLift

/-! # Reconstructing the whole clear successor from its source point -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- At every actual clear step, even after an accepted unusable binding, the
next source point determines the complete automatically closed checkpoint. -/
theorem clear_step_reconstruct (before : CommitRecoveryState program)
    (clear : before.excluded = ∅) (joint : Player → Option (CommitRecoveryMove Player L))
    (after : CommitRecoveryState program) (supported : after ∈ (before.step joint).support)
    (afterClear : after.excluded = ∅) :
    after = before.advanceClear clear after.point := by
  obtain ⟨result, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have resultClear : result.1.2 = ∅ := by
    simpa only [close_excluded, install] using afterClear
  have noFailure : ¬ (before.install result.1 result.2).NewFailure := by
    simp only [NewFailure, install, resultClear, Finset.empty_sdiff,
      Finset.not_nonempty_empty, not_false_eq_true]
  rw [close_point_of_no_new_failure _ noFailure]
  unfold advanceClear
  congr 1
  congr 1
  exact Prod.ext rfl resultClear

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem commitRecovery_clear_step_reconstruct
    {before after : setup.commitRecoveryProtocol.State}
    (draw : {joint // setup.commitRecoveryProtocol.Legal before joint})
    (supported : after ∈ (setup.commitRecoveryProtocol.step before draw).support)
    (clear : setup.CommitRecoveryClear after) :
    after = setup.commitRecoveryLiftSuccessor before
      (setup.commitRecoveryClear_before draw supported clear)
      (setup.commitRecoverySourceState after) := by
  cases before with
  | none =>
      obtain ⟨inputs, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      rfl
  | some before =>
      obtain ⟨after, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact congrArg some (before.clear_step_reconstruct
        (before.clear_before draw.1 after member clear) draw.1 after member clear)

end Setup
end Vegas.SourceProgram
