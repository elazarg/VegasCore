/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Epistemic

/-!
# The source schedule

`VegasCore` is a straight-line language: control never branches on a sampled or
committed value. Consequently the small-step semantics defines a *single*
schedule — the sequence of program points a run visits is fixed by the program
text alone, and only the *values* bound along the way vary between runs.

This module makes that precise. `SourceProgramPoint.successor?` is the next
program point as a pure function of the current one, with no reference to the
environment. The labeled small step refines it (`LStep.programPoint_successor`),
and two steps from the same configuration — differing only in the value drawn,
chosen, or disclosed — land on the *same* successor program point
(`LStep.programPoint_eq_of_cofired`). That is the source-level statement that
the schedule is value-independent.

Because the successor is a function of the program point, and players already
know the program point (`SourceConfig.Knows.programPoint_eq`), the next point of
the schedule is common knowledge (`SourceConfig.Knows.successor?_eq`). This is
the source side of the confluent-coarsening picture: the event graph is free to
permute this single deterministic schedule precisely because the schedule it
permutes is already pinned down — and known — by the program.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SourceProgramPoint

/-- The next source program point, as a pure function of the current point.

This is independent of the environment: in a straight-line language the control
trajectory is fixed by the program text. It is `none` exactly at a terminal
`ret`, and otherwise drops the head instruction and advances to its
continuation, pushing the bound variable onto the context. -/
def successor? : SourceProgramPoint P L → Option (SourceProgramPoint P L)
  | ⟨_, .ret _⟩ => none
  | ⟨_, .sample _ _ tail⟩ => some ⟨_, tail⟩
  | ⟨_, .commit _ _ _ tail⟩ => some ⟨_, tail⟩
  | ⟨_, .reveal _ _ _ _ tail⟩ => some ⟨_, tail⟩

@[simp] theorem successor?_ret
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    successor? ({ ctx := Γ, cont := VegasCore.ret payoffs } :
      SourceProgramPoint P L) = none := rfl

@[simp] theorem successor?_sample
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) b)
    (tail : VegasCore P L ((x, .pub b) :: Γ)) :
    successor? ({ ctx := Γ, cont := VegasCore.sample x dist tail } :
      SourceProgramPoint P L) =
      some { ctx := (x, .pub b) :: Γ, cont := tail } := rfl

@[simp] theorem successor?_commit
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((x, .sealed who b) :: Γ)) :
    successor? ({ ctx := Γ, cont := VegasCore.commit x who guard tail } :
      SourceProgramPoint P L) =
      some { ctx := (x, .sealed who b) :: Γ, cont := tail } := rfl

@[simp] theorem successor?_reveal
    {Γ : VCtx P L} {y x : VarId} {who : P} {b : L.Ty}
    (hx : VHasVar Γ x (.sealed who b))
    (tail : VegasCore P L ((y, .pub b) :: Γ)) :
    successor? ({ ctx := Γ, cont := VegasCore.reveal y who x hx tail } :
      SourceProgramPoint P L) =
      some { ctx := (y, .pub b) :: Γ, cont := tail } := rfl

/-- A program point is terminal exactly when it has no successor. -/
theorem successor?_eq_none_iff (pt : SourceProgramPoint P L) :
    pt.successor? = none ↔ ∃ payoffs, pt.cont = VegasCore.ret payoffs := by
  rcases pt with ⟨Γ, cont⟩
  cases cont with
  | ret payoffs => simp
  | sample x dist tail => simp
  | commit x who guard tail => simp
  | reveal y who x hx tail => simp

end SourceProgramPoint

/-! ## The labeled step refines the program-point successor -/

/-- A labeled small step advances the program point along `successor?`. The
label — hence the value drawn, chosen, or disclosed — does not affect which
program point comes next. -/
theorem LStep.programPoint_successor
    {cfg cfg' : SourceConfig P L} {ℓ : Label P L}
    (h : LStep cfg ℓ cfg') :
    cfg.programPoint.successor? = some cfg'.programPoint := by
  cases h <;> rfl

/-- Schedule determinism: two labeled steps out of the same configuration land
on the same successor program point, whatever values they carry. This is the
source-level statement that the schedule is value-independent — the only
nondeterminism in a `VegasCore` run is in the values, never the control. -/
theorem LStep.programPoint_eq_of_cofired
    {cfg a b : SourceConfig P L} {ℓ₁ ℓ₂ : Label P L}
    (h₁ : LStep cfg ℓ₁ a) (h₂ : LStep cfg ℓ₂ b) :
    a.programPoint = b.programPoint :=
  Option.some.inj (h₁.programPoint_successor.symm.trans h₂.programPoint_successor)

/-- The unlabeled step likewise advances the program point along `successor?`. -/
theorem SmallStep.programPoint_successor
    {cfg cfg' : SourceConfig P L}
    (h : SmallStep cfg cfg') :
    cfg.programPoint.successor? = some cfg'.programPoint := by
  obtain ⟨ℓ, hℓ⟩ := smallStep_iff_exists_label.mp h
  exact hℓ.programPoint_successor

/-- Schedule determinism for unlabeled steps. -/
theorem SmallStep.programPoint_eq_of_cofired
    {cfg a b : SourceConfig P L}
    (h₁ : SmallStep cfg a) (h₂ : SmallStep cfg b) :
    a.programPoint = b.programPoint :=
  Option.some.inj
    (h₁.programPoint_successor.symm.trans h₂.programPoint_successor)

namespace SourceConfig

/-- The next point of the schedule is common knowledge: every player knows the
successor program point, because it is a function of the program point they
already know. -/
theorem Knows.successor?_eq (who : P) (cfg : SourceConfig P L) :
    SourceConfig.Knows (L := L) who cfg
      { other | other.programPoint.successor? = cfg.programPoint.successor? } :=
  SourceConfig.Knows.mono (SourceConfig.Knows.programPoint_eq who cfg)
    (fun {_other} h => congrArg SourceProgramPoint.successor? h)

end SourceConfig

end Vegas
