/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding

/-! # Guard verdicts predicted from the author's observation

A guard reads only public data, publications and its author's own commitments
(`Vegas.SourceGuardRead`), and the author observes all of them when it commits.
`Vegas.SourceGuard.predicts` computes from that observation alone the verdict the
guard gives a candidate subject value, reading each own commitment as its
binding. The prediction is unchanged as the context grows
(`Vegas.SourceGuard.predicts_weaken`). When the author's published commitments
carry their bindings, a completed obligation accepts exactly when its
prediction holds for the bound subject value
(`Vegas.SourceProgram.Obligation.accepts_eq_predicts`).
-/

namespace Vegas

variable {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : SourceCtx Player L}

namespace SourceGuardRead

variable {author : Player} {τ : L.Ty}

/-- A guard input as its author observes it: public data as a success, a
publication as observed, and an own commitment as its binding. -/
def predicted (observation : SourceObservation L author Γ) :
    SourceGuardRead Γ author τ → PublicationResult (L.Val τ)
  | .publicData h => .success (observation.cells.get h)
  | .publication h => observation.cells.get h
  | .commitment h => (observation.cells.get h).getD .failure

@[simp] theorem predicted_weaken {x : VarId} {cell : CellTy Player L}
    (read : SourceGuardRead Γ author τ) (head : CellVal L cell) (state : State L Γ) :
    (read.weaken (x := x) (cell := cell)).predicted
        (sourceObserve author (Env.cons head state)) =
      read.predicted (sourceObserve author state) := by
  cases read <;> rfl

/-- A revealed input's published result is its prediction, provided the
author's revealed commitments publish their bindings. -/
theorem result_eq_predicted (read : SourceGuardRead Γ author τ)
    (revelations : Revelations Γ) (state : State L Γ)
    (revealed : read.revealed revelations = true)
    (published : ∀ {x σ} (h : HasVar Γ x (.commitment author σ)),
      (revelations h).isRevealed = true → (revelations h).result state = state.get h) :
    read.result revelations state = read.predicted (sourceObserve author state) := by
  cases read with
  | publicData h => rfl
  | publication h => rfl
  | commitment h =>
      change (revelations h).result state =
        ((sourceObserve author state).cells.get h).getD .failure
      rw [published h revealed]
      change _ = (if author = author then some (state.get h) else none).getD .failure
      rw [ite_eq_left rfl, Option.getD_some]

end SourceGuardRead

namespace SourceGuard

variable {author : Player} {subject : VarId} {payload : L.Ty}

/-- The verdict a guard gives a candidate subject value, computed from its
author's observation. -/
def predicts (guard : SourceGuard L Γ author subject payload)
    (observation : SourceObservation L author Γ) (value : L.Val payload) : Bool :=
  guard.toGuardCode.accepts (.success value) fun h _ => (guard.reads h).predicted observation

@[simp] theorem predicts_weaken {name : VarId} {cell : CellTy Player L}
    (guard : SourceGuard L Γ author subject payload) (head : CellVal L cell)
    (state : State L Γ) (value : L.Val payload) :
    (guard.weaken (name := name) (cell := cell)).predicts
        (sourceObserve author (Env.cons head state)) value =
      guard.predicts (sourceObserve author state) value := by
  simp only [predicts, weaken, SourceGuardRead.predicted_weaken]

end SourceGuard

namespace SourceProgram.Obligation

/-- **Prediction is exact.** Once an obligation is completed, it accepts exactly
when its guard's prediction from the author's observation holds for the bound
subject value, provided the author's revealed commitments publish their
bindings. -/
theorem accepts_eq_predicts
    (obligation : Obligation (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (state : State L Γ)
    (revealed : obligation.revealed revelations = true)
    (published : ∀ {x σ} (h : HasVar Γ x (.commitment obligation.owner σ)),
      (revelations h).isRevealed = true → (revelations h).result state = state.get h)
    {value : L.Val obligation.payload} (bound : state.get obligation.source = .success value) :
    obligation.accepts revelations state =
      obligation.guard.predicts (sourceObserve obligation.owner state) value := by
  simp only [Obligation.revealed, Bool.and_eq_true] at revealed
  have subject : (revelations obligation.source).result state = .success value :=
    (published obligation.source revealed.1).trans bound
  simp only [Obligation.accepts, SourceGuard.accepts, SourceGuard.predicts, subject]
  apply GuardCode.accepts_congr
  intro x τ h hx
  apply SourceGuardRead.result_eq_predicted _ _ _ _ published
  exact (GuardCode.allReads_iff _ _).mp revealed.2 h hx

end SourceProgram.Obligation

end Vegas
