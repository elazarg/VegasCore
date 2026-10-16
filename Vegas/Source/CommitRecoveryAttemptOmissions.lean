/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryInstructions

/-! # The literal omission word of an original typed commitment attempt -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix.Attempt

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
  {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
  {after : Finset Player}

/-- An attempt has no newly excluded owners exactly when its actual raw
instruction word contains no omission, including automatic excluded slots. -/
theorem failedOwners_eq_empty_iff_no_missed
    (attempt : block.Attempt entry excluded finished after) :
    attempt.failedOwners = ∅ ↔ ∀ joint ∈ attempt.joints, ∀ who,
      CommitRecoveryMove.missed (joint who) = false := by
  induction attempt with
  | nil => simp [failedOwners, joints]
  | @active Γ Δ O P name owner payload fresh guard rest config excluded finished after
      active choice missed missingFailure later ih =>
      cases missed with
      | false =>
          constructor
          · intro empty joint member who
            rcases List.mem_cons.mp member with rfl | kept
            · by_cases same : who = owner <;> simp [CommitRecoveryMove.missed, same]
            · exact ih.mp empty joint kept who
          · intro safe
            exact ih.mpr (fun joint member who =>
              safe joint (List.mem_cons_of_mem _ member) who)
      | true =>
          constructor
          · intro empty
            simp [failedOwners] at empty
          · intro safe
            have impossible := safe _ (List.mem_cons_self ..) owner
            simp [CommitRecoveryMove.missed] at impossible
  | excluded inactive later ih =>
      simpa [failedOwners, joints, CommitRecoveryMove.missed] using ih

end Vegas.SourceProgram.CommitPrefix.Attempt
