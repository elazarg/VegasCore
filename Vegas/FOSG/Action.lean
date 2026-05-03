import Vegas.FOSG.Runtime

/-!
# Program-local FOSG actions

This file defines the finite-by-construction action alphabet used by the
executable cursor-keyed FOSG target. It sits above the broad runtime action
alphabet from `Vegas.FOSG.Runtime`.
-/

namespace Vegas
namespace FOSGBridge

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Program-local action cursors

The broad `Action L who` alphabet is useful for the first structural bridge,
but finite FOSG execution should not quantify over every type in `L`. The
following cursor describes exactly the commit sites of one program owned by
one player; `ProgramAction` is the corresponding finite-by-construction target
alphabet once value types are finite.
-/

/-- A cursor to a commit site owned by `who` inside a fixed Vegas program. -/
inductive CommitCursor (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      CommitCursor who (.commit x who R k)
  | letExpr
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.letExpr x e k)
  | sample
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.sample x D k)
  | commit
      {Γ : VCtx P L} {x : VarId} {owner : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.commit x owner R k)
  | reveal
      {Γ : VCtx P L} {y : VarId} {owner : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden owner b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (c : CommitCursor who k) :
      CommitCursor who (.reveal y owner x hx k)

namespace CommitCursor

/-- The value type chosen at the pointed commit site. -/
def ty {who : P} :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      CommitCursor who p → L.Ty
  | _, .commit _ _ (b := b) _ _, .here => b
  | _, .letExpr _ _ _, .letExpr c => ty c
  | _, .sample _ _ _, .sample c => ty c
  | _, .commit _ _ _ _, .commit c => ty c
  | _, .reveal _ _ _ _ _, .reveal c => ty c

/-- Enumerate the commit sites owned by `who` in a fixed program. -/
def enumerate (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      List (CommitCursor who p)
  | _, .ret _ => []
  | _, .letExpr _ _ k => (enumerate who k).map .letExpr
  | _, .sample _ _ k => (enumerate who k).map .sample
  | Γ, .commit x owner (b := b) R k =>
      if h : owner = who then
        by
          have head :
              CommitCursor who
                (.commit x owner (b := b) R k) := by
            cases h
            exact .here
          exact head :: (enumerate who k).map .commit
      else
        (enumerate who k).map .commit
  | _, .reveal _ _ _ _ k => (enumerate who k).map .reveal

/-- `enumerate` is complete: every cursor appears in the generated list. -/
theorem mem_enumerate {who : P} :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (c : CommitCursor who p) →
        c ∈ enumerate who p
  | _, _, .here => by
      simp [enumerate]
  | _, _, .letExpr c => by
      simp [enumerate, mem_enumerate c]
  | _, _, .sample c => by
      simp [enumerate, mem_enumerate c]
  | _, _, .commit c => by
      simp only [enumerate]
      split
      · right
        exact List.mem_map.mpr ⟨c, mem_enumerate c, rfl⟩
      · exact List.mem_map.mpr ⟨c, mem_enumerate c, rfl⟩
  | _, _, .reveal c => by
      simp [enumerate, mem_enumerate c]

/-- The set of owned commit cursors is finite without assuming all language
types are finite. -/
@[reducible] noncomputable def instFintype
    (who : P) {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (CommitCursor who p) := by
  classical
  exact Fintype.ofList (enumerate who p)
    (fun c => mem_enumerate c)

end CommitCursor

/-- Program-local action alphabet: choose one owned commit site and a value of
that site's type. This is the intended replacement alphabet for finite FOSG
execution, avoiding any global finiteness assumption on `L.Ty`. -/
structure ProgramAction {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) where
  cursor : CommitCursor who p
  value : L.Val (CommitCursor.ty cursor)

namespace ProgramAction

/-- Erase a program-local action to the broad structural action alphabet. -/
def toAction {Γ : VCtx P L} {p : VegasCore P L Γ} {who : P}
    (a : ProgramAction p who) : Action (P := P) L who :=
  Sigma.mk (CommitCursor.ty a.cursor) a.value

/-- Local decidable equality helper for program actions. Kept as an explicit
definition rather than a global instance because it is classical over the
dependent cursor proof shape. -/
@[reducible] noncomputable def instDecidableEq
    {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) :
    DecidableEq (ProgramAction p who) :=
  Classical.decEq _

/-- Program-local actions are finite when the value types that occur in the
language are finite. This avoids the stronger and usually wrong requirement
that the global sigma alphabet `Action L who` be finite. -/
@[reducible] noncomputable def instFintype
    (LF : FiniteValuation L) {Γ : VCtx P L}
    (p : VegasCore P L Γ) (who : P) :
    Fintype (ProgramAction p who) := by
  classical
  let _ : Fintype (CommitCursor who p) :=
    CommitCursor.instFintype who p
  have hVal : ∀ c : CommitCursor who p,
      Fintype (L.Val (CommitCursor.ty c)) :=
    fun c => LF.fintypeVal (CommitCursor.ty c)
  let e :
      ProgramAction p who ≃
        Sigma (fun c : CommitCursor who p =>
          L.Val (CommitCursor.ty c)) :=
    { toFun := fun a => ⟨a.cursor, a.value⟩
      invFun := fun a => { cursor := a.1, value := a.2 }
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro a
        cases a
        rfl }
  let _ : ∀ c : CommitCursor who p,
      Fintype (L.Val (CommitCursor.ty c)) := hVal
  exact Fintype.ofEquiv
    (Sigma (fun c : CommitCursor who p =>
      L.Val (CommitCursor.ty c))) e.symm

end ProgramAction

end FOSGBridge
end Vegas
