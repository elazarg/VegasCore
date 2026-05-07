import Vegas.EventGraph.ToMachine
import Vegas.Core.Program
import Vegas.Core.Config

/-!
# Program Event Graph

This file elaborates a checked Vegas program to its canonical `EventGraph`.

`ProgramNode` names protocol events introduced by the source term, and
`ProgramField` names storage fields in the final protocol state. These are not
runtime cursors: runtime state remains the extensional result assignment from
`EventGraph.Configuration`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- A field occurrence in a visibility context. -/
inductive VCtxField (P : Type) (L : IExpr) :
    VCtx P L → Type where
  | mk {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
      (h : VHasVar Γ x τ) : VCtxField P L Γ

namespace VCtxField

variable {Γ : VCtx P L}

/-- Variable name of a context field. -/
def name : VCtxField P L Γ → VarId
  | .mk (x := x) _ => x

/-- Visibility-aware binding type of a context field. -/
def bindTy : VCtxField P L Γ → BindTy P L
  | .mk (τ := τ) _ => τ

/-- Semantic value type of a context field. -/
def ty (field : VCtxField P L Γ) : L.Ty :=
  field.bindTy.base

/-- Owner of a context field, if hidden. Public fields have no owner. -/
def owner (field : VCtxField P L Γ) : Option P :=
  field.bindTy.owner

/-- Look up this context field in a visibility environment. -/
def value (env : VEnv L Γ) :
    (field : VCtxField P L Γ) → L.Val field.ty
  | .mk h => env _ _ h

/-- Weaken a field through a new context head. -/
def weakenHead {x : VarId} {τ : BindTy P L}
    (field : VCtxField P L Γ) :
    VCtxField P L ((x, τ) :: Γ) :=
  match field with
  | .mk h => .mk (.there h)

omit [DecidableEq P] in
@[simp] theorem ty_weakenHead {x : VarId} {τ : BindTy P L}
    (field : VCtxField P L Γ) :
    (field.weakenHead (x := x) (τ := τ)).ty = field.ty := by
  cases field with
  | mk h =>
      cases h <;> rfl

omit [DecidableEq P] in
@[simp] theorem owner_weakenHead {x : VarId} {τ : BindTy P L}
  (field : VCtxField P L Γ) :
    (field.weakenHead (x := x) (τ := τ)).owner = field.owner := by
  cases field with
  | mk h =>
      rfl

/-- Enumerate all fields in a visibility context. -/
def enumerate : (Γ : VCtx P L) → List (VCtxField P L Γ)
  | [] => []
  | (x, τ) :: Γ =>
      .mk (x := x) (τ := τ) .here ::
        (enumerate Γ).map (weakenHead (x := x) (τ := τ))

omit [DecidableEq P] in
theorem mem_enumerate :
    {Γ : VCtx P L} → (field : VCtxField P L Γ) →
      field ∈ enumerate Γ
  | _xτ :: _Γ, .mk .here => by
      simp [enumerate]
  | (x, τ) :: Γ, .mk (.there h) => by
      exact List.mem_cons_of_mem _ <|
        List.mem_map.mpr
          ⟨.mk h, mem_enumerate (.mk h), rfl⟩

@[reducible] noncomputable instance instDecidableEq
    (Γ : VCtx P L) : DecidableEq (VCtxField P L Γ) :=
  Classical.decEq _

@[reducible] noncomputable instance instFintype
    (Γ : VCtx P L) : Fintype (VCtxField P L Γ) :=
  Fintype.ofList (enumerate Γ) mem_enumerate

@[reducible] noncomputable def finiteTypeOfProof
    {Γ : VCtx P L} (hΓ : FiniteVCtxProof Γ)
    (field : VCtxField P L Γ) : FiniteType L field.ty := by
  cases field with
  | mk h =>
      exact ⟨FiniteVCtxProof.fintypeOfHasVar hΓ h⟩

end VCtxField

/-- Source protocol-event occurrence. There is one node for every non-`ret`
constructor in the source term. -/
inductive ProgramNode :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | letHere
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)} :
      ProgramNode (.letExpr x e k)
  | letTail
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (node : ProgramNode k) :
      ProgramNode (.letExpr x e k)
  | sampleHere
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)} :
      ProgramNode (.sample x D k)
  | sampleTail
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (node : ProgramNode k) :
      ProgramNode (.sample x D k)
  | commitHere
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      ProgramNode (.commit x who R k)
  | commitTail
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (node : ProgramNode k) :
      ProgramNode (.commit x who R k)
  | revealHere
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)} :
      ProgramNode (.reveal y who x hx k)
  | revealTail
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (node : ProgramNode k) :
      ProgramNode (.reveal y who x hx k)

namespace ProgramNode

/-- Source-order rank of a program node. This is an acyclicity certificate for
the compiler; it is not runtime state. -/
def rank : {Γ : VCtx P L} → {p : VegasCore P L Γ} → ProgramNode p → Nat
  | _, _, .letHere => 0
  | _, _, .letTail node => node.rank + 1
  | _, _, .sampleHere => 0
  | _, _, .sampleTail node => node.rank + 1
  | _, _, .commitHere => 0
  | _, _, .commitTail node => node.rank + 1
  | _, _, .revealHere => 0
  | _, _, .revealTail node => node.rank + 1

/-- Actor of a source node. Only commits are player actions. -/
def actor : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramNode p → Option P
  | _, _, .letHere => none
  | _, _, .letTail node => node.actor
  | _, _, .sampleHere => none
  | _, _, .sampleTail node => node.actor
  | _, _, .commitHere (who := who) => some who
  | _, _, .commitTail node => node.actor
  | _, _, .revealHere => none
  | _, _, .revealTail node => node.actor

/-- Enumerate source nodes. -/
def enumerate :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → List (ProgramNode p)
  | _, .ret _ => []
  | _, .letExpr _ _ k => .letHere :: (enumerate k).map .letTail
  | _, .sample _ _ k => .sampleHere :: (enumerate k).map .sampleTail
  | _, .commit _ _ _ k => .commitHere :: (enumerate k).map .commitTail
  | _, .reveal _ _ _ _ k => .revealHere :: (enumerate k).map .revealTail

theorem mem_enumerate :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (node : ProgramNode p) → node ∈ enumerate p
  | _, _, .letHere => by simp [enumerate]
  | _, _, .letTail node => by
      exact List.mem_cons_of_mem _ <|
        List.mem_map.mpr ⟨node, mem_enumerate node, rfl⟩
  | _, _, .sampleHere => by simp [enumerate]
  | _, _, .sampleTail node => by
      exact List.mem_cons_of_mem _ <|
        List.mem_map.mpr ⟨node, mem_enumerate node, rfl⟩
  | _, _, .commitHere => by simp [enumerate]
  | _, _, .commitTail node => by
      exact List.mem_cons_of_mem _ <|
        List.mem_map.mpr ⟨node, mem_enumerate node, rfl⟩
  | _, _, .revealHere => by simp [enumerate]
  | _, _, .revealTail node => by
      exact List.mem_cons_of_mem _ <|
        List.mem_map.mpr ⟨node, mem_enumerate node, rfl⟩

/-- The source-node enumeration has one entry for each non-`ret` constructor. -/
theorem length_enumerate :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (enumerate p).length = syntaxSteps p
  | _, .ret _ => rfl
  | _, .letExpr _ _ k => by
      simp [enumerate, syntaxSteps, length_enumerate k]
  | _, .sample _ _ k => by
      simp [enumerate, syntaxSteps, length_enumerate k]
  | _, .commit _ _ _ k => by
      simp [enumerate, syntaxSteps, length_enumerate k]
  | _, .reveal _ _ _ _ k => by
      simp [enumerate, syntaxSteps, length_enumerate k]

@[reducible] noncomputable instance instDecidableEq
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    DecidableEq (ProgramNode p) :=
  Classical.decEq _

@[reducible] noncomputable instance instFintype
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (ProgramNode p) :=
  Fintype.ofList (enumerate p) mem_enumerate

/-- Finset of source nodes. -/
noncomputable def finset {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Finset (ProgramNode p) := by
  classical
  exact (enumerate p).toFinset

@[simp] theorem mem_finset
    {Γ : VCtx P L} (p : VegasCore P L Γ) (node : ProgramNode p) :
    node ∈ finset p := by
  classical
  exact List.mem_toFinset.mpr (mem_enumerate node)

/-- The source-node finset is bounded by the syntactic length of the source
program. -/
theorem finset_card_le_syntaxSteps
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    (finset p).card ≤ syntaxSteps p := by
  classical
  calc
    (finset p).card = (enumerate p).toFinset.card := rfl
    _ ≤ (enumerate p).length := by
      exact List.toFinset_card_le (enumerate p)
    _ = syntaxSteps p := length_enumerate p

end ProgramNode

end Vegas
