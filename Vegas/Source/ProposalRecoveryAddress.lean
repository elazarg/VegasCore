/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryProtocol

/-! # Static maximal publication-block addresses in source syntax -/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Whether an absolute source instruction rank is a publication. -/
def publicationAt : ∀ {Γ : SourceCtx Player L} {O : Finset VarId},
    SourceProgram Player L Γ O → Nat → Bool
  | _, _, .ret _, _ => false
  | _, _, .sample _ _ _ _, 0 => false
  | _, _, .sample _ _ _ next, rank + 1 => publicationAt next rank
  | _, _, .commit _ _ _ _ _, 0 => false
  | _, _, .commit _ _ _ _ next, rank + 1 => publicationAt next rank
  | _, _, .reveal _ _ _ _ _ _ _, 0 => true
  | _, _, .reveal _ _ _ _ _ _ next, rank + 1 => publicationAt next rank

/-- The first rank of the consecutive publication interval immediately before
and including a publication at `rank`. No dynamic checkpoint is consulted. -/
def publicationBlockLow {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : Nat → Nat
  | 0 => 0
  | rank + 1 => if program.publicationAt rank then publicationBlockLow program rank else rank + 1

theorem publicationBlockLow_le {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (rank : Nat) :
    program.publicationBlockLow rank ≤ rank := by
  induction rank with
  | zero => exact le_rfl
  | succ rank ih =>
      change (if program.publicationAt rank then _ else rank + 1) ≤ rank + 1
      split
      · exact ih.trans (Nat.le_succ _)
      · exact le_rfl

/-- The scan agrees with any maximal contiguous publication interval. -/
theorem publicationBlockLow_eq_of_interval {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (low rank : Nat) (bounded : low ≤ rank)
    (inside : ∀ index, low ≤ index → index < rank → program.publicationAt index = true)
    (boundary : low = 0 ∨ program.publicationAt (low - 1) = false) :
    program.publicationBlockLow rank = low := by
  induction rank with
  | zero =>
      have equal : low = 0 := by omega
      subst low
      rfl
  | succ rank ih =>
      by_cases equal : low = rank + 1
      · subst low
        have prior : program.publicationAt rank = false := by
          rcases boundary with impossible | prior
          · omega
          · simpa only [Nat.add_sub_cancel] using prior
        simp only [publicationBlockLow, prior, Bool.false_eq_true, ite_false]
      · have earlier : low ≤ rank := by omega
        have current := inside rank earlier (Nat.lt_succ_self rank)
        rw [publicationBlockLow, current]
        exact ih earlier (fun index lower upper => inside index lower (by omega))

end Vegas.SourceProgram
