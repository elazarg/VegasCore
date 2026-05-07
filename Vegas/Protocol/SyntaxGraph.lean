import Vegas.Protocol.GraphMachine
import Vegas.WFProgram

/-!
# Syntax occurrence graph

This file introduces source-occurrence identifiers used by the compiler from
checked Vegas syntax to `ProtocolGraph`.

These are not runtime cursors. `ProgramNode` names protocol events introduced
by the source term. `ProgramField` names storage fields in the final protocol
state. Runtime state remains the extensional result assignment from
`ProtocolGraph.Configuration`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] ProtocolGraph.nodeDecEq
attribute [local instance] ProtocolGraph.fieldDecEq

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

end ProgramNode

/-- Storage field occurrence in the final state of a source program. -/
inductive ProgramField :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | retField
      {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
      (field : VCtxField P L Γ) :
      ProgramField (.ret payoffs)
  | letTail
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.letExpr x e k)
  | sampleTail
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.sample x D k)
  | commitTail
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.commit x who R k)
  | revealTail
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.reveal y who x hx k)

namespace ProgramField

/-- Variable name of a final program field. -/
def name : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramField p → VarId
  | _, _, .retField field => field.name
  | _, _, .letTail field => field.name
  | _, _, .sampleTail field => field.name
  | _, _, .commitTail field => field.name
  | _, _, .revealTail field => field.name

/-- Semantic type of a final program field. -/
def ty : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramField p → L.Ty
  | _, _, .retField field => field.ty
  | _, _, .letTail field => field.ty
  | _, _, .sampleTail field => field.ty
  | _, _, .commitTail field => field.ty
  | _, _, .revealTail field => field.ty

/-- Owner of a final program field, if hidden. -/
def owner : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramField p → Option P
  | _, _, .retField field => field.owner
  | _, _, .letTail field => field.owner
  | _, _, .sampleTail field => field.owner
  | _, _, .commitTail field => field.owner
  | _, _, .revealTail field => field.owner

/-- A field is observable by a player when it is public or owned by that player. -/
abbrev VisibleTo {Γ : VCtx P L} {p : VegasCore P L Γ}
    (who : P) (field : ProgramField p) : Prop :=
  field.owner = none ∨ field.owner = some who

/-- Embed a field from the current context into the final field set of a
program. -/
def ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      VCtxField P L Γ → ProgramField p
  | _, .ret _, field => .retField field
  | _, .letExpr x _ k, field =>
      .letTail (ofCurrent k (field.weakenHead (x := x) (τ := .pub _)))
  | _, .sample x _ k, field =>
      .sampleTail (ofCurrent k (field.weakenHead (x := x) (τ := .pub _)))
  | _, .commit x who _ k, field =>
      .commitTail
        (ofCurrent k (field.weakenHead (x := x) (τ := .hidden who _)))
  | _, .reveal y _ _ _ k, field =>
      .revealTail (ofCurrent k (field.weakenHead (x := y) (τ := .pub _)))

@[simp] theorem ty_ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L Γ) →
        (ofCurrent p field).ty = field.ty
  | _, .ret _, field => rfl
  | _, .letExpr _ _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .sample _ _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .commit _ who _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .hidden who _))
  | _, .reveal _ _ _ _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .pub _))

@[simp] theorem owner_ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L Γ) →
        (ofCurrent p field).owner = field.owner
  | _, .ret _, field => rfl
  | _, .letExpr _ _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .sample _ _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .commit _ who _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .hidden who _))
  | _, .reveal _ _ _ _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .pub _))

theorem owner_eq_none_or_some_of_visible
    {Γ : VCtx P L} (hctx : WFCtx Γ) {who : P}
    (field : VCtxField P L Γ)
    (hvisible : field.name ∈ visibleVars (L := L) who Γ) :
    field.owner = none ∨ field.owner = some who := by
  cases field with
  | mk h =>
      induction h with
      | here =>
          rename_i Γ x τ
          match τ with
          | ⟨_, .pub⟩ =>
              left
              rfl
          | ⟨b, .hidden owner⟩ =>
              by_cases hwho : who = owner
              · subst owner
                right
                rfl
              · have hfresh : Fresh x Γ := WFCtx.fresh_head hctx
                have hnot := not_mem_visibleVars_hidden_other (L := L)
                  (Γ := Γ) (x := x) (who := who) (owner := owner)
                  (τ := b) hfresh hwho
                exact False.elim (hnot hvisible)
      | there h ih =>
          rename_i Γ x y τ τ'
          have htail : WFCtx Γ := WFCtx.tail hctx
          have hfresh : Fresh y Γ := WFCtx.fresh_head hctx
          have hvisibleTail : x ∈ visibleVars (L := L) who Γ := by
            match τ' with
            | ⟨_, .pub⟩ =>
                simp only [visibleVars] at hvisible
                rcases Finset.mem_insert.mp hvisible with hxy | htailVisible
                · exact False.elim
                    (hfresh (by simpa [← hxy] using HasVar.mem_map_fst h))
                · exact htailVisible
            | ⟨_, .hidden owner⟩ =>
                by_cases hwho : who = owner
                · subst owner
                  simp only [visibleVars, ↓reduceIte] at hvisible
                  rcases Finset.mem_insert.mp hvisible with hxy | htailVisible
                  · exact False.elim
                      (hfresh (by simpa [← hxy] using HasVar.mem_map_fst h))
                  · exact htailVisible
                · simp only [visibleVars, hwho, ↓reduceIte] at hvisible
                  exact hvisible
          exact ih htail hvisibleTail

/-- Current-context fields embedded into a program's final field set. -/
noncomputable def currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) : Finset (ProgramField p) := by
  classical
  exact ((VCtxField.enumerate Γ).map (fun field => ofCurrent p field)).toFinset

/-- Current-context fields visible to a player. -/
noncomputable def visibleCurrentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) :
    Finset (ProgramField p) := by
  classical
  exact (currentFields p).filter
    (fun field => field.VisibleTo who)

theorem ofCurrent_mem_currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (field : VCtxField P L Γ) :
    ofCurrent p field ∈ currentFields p := by
  classical
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨field, VCtxField.mem_enumerate field, rfl⟩)

/-- Build the full current `VEnv` from a graph read environment over all
current fields. -/
noncomputable def currentReadEnvToVEnv
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (ρ : ProtocolGraph.ReadEnv L (ProgramField p)
      (fun field => field.ty) (currentFields p)) :
    VEnv L Γ :=
  fun x τ h =>
    by
      let field : VCtxField P L Γ := .mk h
      have hmem : ofCurrent p field ∈ currentFields p :=
        ofCurrent_mem_currentFields p field
      simpa [field, VCtxField.ty] using
        (ρ.value (ofCurrent p field) hmem)

/-- Field written by a source node. -/
def writtenBy :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramNode p → ProgramField p
  | _, _, .letHere (x := x) (k := k) =>
      .letTail (ofCurrent k (.mk (x := x) (τ := .pub _) .here))
  | _, _, .letTail node => .letTail (writtenBy node)
  | _, _, .sampleHere (x := x) (k := k) =>
      .sampleTail (ofCurrent k (.mk (x := x) (τ := .pub _) .here))
  | _, _, .sampleTail node => .sampleTail (writtenBy node)
  | _, _, .commitHere (x := x) (who := who) (k := k) =>
      .commitTail (ofCurrent k (.mk (x := x) (τ := .hidden who _) .here))
  | _, _, .commitTail node => .commitTail (writtenBy node)
  | _, _, .revealHere (y := y) (k := k) =>
      .revealTail (ofCurrent k (.mk (x := y) (τ := .pub _) .here))
  | _, _, .revealTail node => .revealTail (writtenBy node)

/-- Structural source of a final program field: either it is an initial field
from the program's input context, or it is written by a unique source node.

This follows the syntax tree instead of searching completed result slices, so
field lookup is stable under unrelated frontier updates. -/
def source :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramField p → VCtxField P L Γ ⊕ ProgramNode p
  | _, .ret _, .retField field => .inl field
  | _, .letExpr _ _ _, .letTail field =>
      match source field with
      | .inl (.mk .here) => .inr .letHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.letTail node)
  | _, .sample _ _ _, .sampleTail field =>
      match source field with
      | .inl (.mk .here) => .inr .sampleHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.sampleTail node)
  | _, .commit _ _ _ _, .commitTail field =>
      match source field with
      | .inl (.mk .here) => .inr .commitHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.commitTail node)
  | _, .reveal _ _ _ _ _, .revealTail field =>
      match source field with
      | .inl (.mk .here) => .inr .revealHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.revealTail node)

/-- The unique source node that writes this field, if the field is not part of
the program's input context. -/
def writer? :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramField p → Option (ProgramNode p)
  | _, _, field =>
      match source field with
      | .inl _ => none
      | .inr node => some node

@[simp] theorem source_ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L Γ) →
        ProgramField.source (ProgramField.ofCurrent p field) = Sum.inl field
  | _, .ret _, field => by
      rfl
  | _, .letExpr _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]
  | _, .sample _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]
  | _, .commit _ _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]
  | _, .reveal _ _ _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]

@[simp] theorem source_writtenBy :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (node : ProgramNode p) →
        ProgramField.source (ProgramField.writtenBy node) = Sum.inr node
  | _, .letExpr _ _ _, .letHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .letExpr _ _ _, .letTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]
  | _, .sample _ _ _, .sampleHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .sample _ _ _, .sampleTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]
  | _, .commit _ _ _ _, .commitHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .commit _ _ _ _, .commitTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]
  | _, .reveal _ _ _ _ _, .revealHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .reveal _ _ _ _ _, .revealTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]

@[simp] theorem writer?_writtenBy
    {Γ : VCtx P L} {p : VegasCore P L Γ} (node : ProgramNode p) :
    ProgramField.writer? (ProgramField.writtenBy node) = some node := by
  simp [ProgramField.writer?]

theorem writer?_eq_none_of_mem_currentFields
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {field : ProgramField p}
    (hmem : field ∈ currentFields p) :
    ProgramField.writer? field = none := by
  classical
  unfold currentFields at hmem
  have hlist :
      field ∈
        (VCtxField.enumerate Γ).map (fun current => ofCurrent p current) :=
    List.mem_toFinset.mp hmem
  rcases List.mem_map.mp hlist with ⟨current, _hcurrent, rfl⟩
  simp [ProgramField.writer?]

private theorem tail_currentFields_or_eq_writtenBy_here
    {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    {p : VegasCore P L Γ} {k : VegasCore P L ((x, τ) :: Γ)}
    (tail : ProgramField k → ProgramField p)
    (head : ProgramNode p)
    (tail_there :
      ∀ {y σ} (h : VHasVar Γ y σ),
        tail (ofCurrent k (.mk (VHasVar.there h))) =
          ofCurrent p (.mk h))
    (tail_here :
      tail (ofCurrent k (.mk (x := x) (τ := τ) VHasVar.here)) =
        ProgramField.writtenBy head)
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    tail field ∈ currentFields p ∨
      tail field = ProgramField.writtenBy head := by
  classical
  unfold currentFields at h ⊢
  simp only [List.mem_toFinset, List.mem_map] at h ⊢
  rcases h with ⟨current, _hcurrent, hfield⟩
  cases current with
  | mk hvar =>
      cases hvar with
      | here =>
          right
          rw [← hfield]
          exact tail_here
      | there htail =>
          left
          refine ⟨.mk htail, VCtxField.mem_enumerate (.mk htail), ?_⟩
          rw [← hfield]
          exact (tail_there htail).symm

theorem letTail_currentFields_or_eq_writtenBy_letHere
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.letTail (e := e) field ∈
        currentFields (.letExpr x e k) ∨
      ProgramField.letTail (e := e) field =
        ProgramField.writtenBy
          (.letHere (x := x) (e := e) (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .letExpr x e k) (k := k) ProgramField.letTail
    (ProgramNode.letHere (x := x) (e := e) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

theorem sampleTail_currentFields_or_eq_writtenBy_sampleHere
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.sampleTail (D := D) field ∈
        currentFields (.sample x D k) ∨
      ProgramField.sampleTail (D := D) field =
        ProgramField.writtenBy
          (.sampleHere (x := x) (D := D) (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .sample x D k) (k := k) ProgramField.sampleTail
    (ProgramNode.sampleHere (x := x) (D := D) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

theorem commitTail_currentFields_or_eq_writtenBy_commitHere
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.commitTail (R := R) field ∈
        currentFields (.commit x who R k) ∨
      ProgramField.commitTail (R := R) field =
        ProgramField.writtenBy
          (.commitHere (x := x) (who := who) (R := R) (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .commit x who R k) (k := k) ProgramField.commitTail
    (ProgramNode.commitHere (x := x) (who := who) (R := R) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

theorem revealTail_currentFields_or_eq_writtenBy_revealHere
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.revealTail (x := x) (hx := hx) field ∈
        currentFields (.reveal y who x hx k) ∨
      ProgramField.revealTail (x := x) (hx := hx) field =
        ProgramField.writtenBy
          (.revealHere (y := y) (who := who) (x := x) (hx := hx)
            (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .reveal y who x hx k) (k := k) ProgramField.revealTail
    (ProgramNode.revealHere (y := y) (who := who) (x := x)
      (hx := hx) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

/-- Hidden field read by a reveal node. For non-reveal nodes this is `none`. -/
def revealSource? :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramNode p → Option (ProgramField p)
  | _, _, .letHere => none
  | _, _, .letTail node => Option.map .letTail (revealSource? node)
  | _, _, .sampleHere => none
  | _, _, .sampleTail node => Option.map .sampleTail (revealSource? node)
  | _, _, .commitHere => none
  | _, _, .commitTail node => Option.map .commitTail (revealSource? node)
  | _, _, .revealHere (hx := hx) (k := k) =>
      some (.revealTail (ofCurrent k (.mk (VHasVar.there hx))))
  | _, _, .revealTail node => Option.map .revealTail (revealSource? node)

/-- Enumerate final fields of a source program. -/
def enumerate :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → List (ProgramField p)
  | Γ, .ret payoffs =>
      (VCtxField.enumerate Γ).map (fun field => .retField (payoffs := payoffs) field)
  | _, .letExpr _ _ k => (enumerate k).map .letTail
  | _, .sample _ _ k => (enumerate k).map .sampleTail
  | _, .commit _ _ _ k => (enumerate k).map .commitTail
  | _, .reveal _ _ _ _ k => (enumerate k).map .revealTail

theorem mem_enumerate :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (field : ProgramField p) → field ∈ enumerate p
  | _, _, .retField field => by
      exact List.mem_map.mpr
        ⟨field, VCtxField.mem_enumerate field, rfl⟩
  | _, _, .letTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩
  | _, _, .sampleTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩
  | _, _, .commitTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩
  | _, _, .revealTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩

@[reducible] noncomputable instance instDecidableEq
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    DecidableEq (ProgramField p) :=
  Classical.decEq _

@[reducible] noncomputable instance instFintype
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (ProgramField p) :=
  Fintype.ofList (enumerate p) mem_enumerate

@[reducible] noncomputable def finiteTypeOfProof :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      FiniteVCtxProof Γ → FiniteProgramProof p →
        (field : ProgramField p) → FiniteType L field.ty
  | _, .ret _, hΓ, .ret, .retField field =>
      VCtxField.finiteTypeOfProof hΓ field
  | _, .letExpr (x := x) (b := b) _ _k,
      hΓ, .letExpr head tail, .letTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((x, .pub b) :: _) from
          .cons head hΓ)
        tail field
  | _, .sample (x := x) (b := b) _ _k,
      hΓ, .sample head tail, .sampleTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((x, .pub b) :: _) from
          .cons head hΓ)
        tail field
  | _, .commit (x := x) (who := who) (b := b) _ _k,
      hΓ, .commit head tail, .commitTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((x, .hidden who b) :: _) from
          .cons head hΓ)
        tail field
  | _, .reveal (y := y) (b := b) _ _ _ _k,
      hΓ, .reveal head tail, .revealTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((y, .pub b) :: _) from
          .cons head hΓ)
        tail field

@[reducible] noncomputable def instFintypeValue
    (g : WFProgram P L) [hfinite : FiniteDomains g]
    (field : ProgramField g.prog) :
    Fintype (L.Val field.ty) :=
  (finiteTypeOfProof hfinite.context.proof hfinite.program.proof field).fintype

/-- Finset of final fields. -/
noncomputable def finset {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Finset (ProgramField p) := by
  classical
  exact (enumerate p).toFinset

@[simp] theorem mem_finset
    {Γ : VCtx P L} (p : VegasCore P L Γ) (field : ProgramField p) :
    field ∈ finset p := by
  classical
  exact List.mem_toFinset.mpr (mem_enumerate field)

/-- Interpret a source expression over the public current context as a
graph-local expression. The read set is the current source scope; this is
intentionally conservative until source-expression dependency projection is
made explicit. -/
noncomputable def publicGraphExpr
    {Γ : VCtx P L} (p : VegasCore P L Γ) {b : L.Ty}
    (e : L.Expr (erasePubVCtx Γ) b) :
    ProtocolGraph.GraphExpr L (ProgramField p)
      (fun field => field.ty) b where
  reads := currentFields p
  eval := fun ρ =>
    L.eval e (VEnv.erasePubEnv (currentReadEnvToVEnv p ρ))

/-- Interpret a source distribution over the public current context as a
graph-local PMF kernel. Normalization is supplied by the checked program. -/
noncomputable def publicGraphDist
    {Γ : VCtx P L} (p : VegasCore P L Γ) {b : L.Ty}
    (D : L.DistExpr (erasePubVCtx Γ) b)
    (normalized :
      ∀ env : VEnv L Γ,
        FWeight.totalWeight (L.evalDist D (VEnv.eraseSampleEnv env)) = 1) :
    ProtocolGraph.GraphDist L (ProgramField p)
      (fun field => field.ty) b where
  reads := currentFields p
  eval := fun ρ =>
    (L.evalDist D
        (VEnv.eraseSampleEnv (currentReadEnvToVEnv p ρ))).toPMF
      (normalized (currentReadEnvToVEnv p ρ))

/-- Interpret a source commit guard as a graph-local guard. The proposed
commit value is supplied separately from the current graph environment. -/
noncomputable def commitGraphGuard
    {Γ : VCtx P L} (p : VegasCore P L Γ) {x : VarId} {b : L.Ty}
    {who : P} (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (field : ProgramField p) (hty : field.ty = b)
    (hctx : WFCtx Γ)
    (hfresh : Fresh x Γ)
    (hguard : GuardUsesOnly (L := L) (Γ := Γ) (x := x)
      (who := who) R)
    (hlegal :
      ∀ env : Env L.Val (eraseVCtx Γ),
        ∃ a : L.Val b,
          evalGuard (Player := P) (L := L) R a env = true) :
    ProtocolGraph.GraphGuard L (ProgramField p)
      (fun field => field.ty) field where
  reads := currentFields p
  visibleReads := visibleCurrentFields p who
  visibleReads_subset_reads := by
    intro read hread
    exact (Finset.mem_filter.mp hread).1
  eval := fun value ρ =>
    evalGuard (Player := P) (L := L) R
      (cast (by rw [hty]) value)
      (VEnv.eraseEnv (currentReadEnvToVEnv p ρ))
  eval_eq_of_visible_eq := by
    intro value ρ₁ ρ₂ hvisible
    apply evalGuard_eq_of_obsEq hfresh hguard
    intro y τ hy hyvisible
    rcases HasVar.toVHasVar (Γ := Γ) hy with
      ⟨σ, hv, ⟨hτ⟩⟩
    cases hτ
    let current : VCtxField P L Γ := .mk hv
    let read := ofCurrent p current
    have hmem : read ∈ currentFields p := by
      exact ofCurrent_mem_currentFields p current
    have hvisibleRead : read ∈ visibleCurrentFields p who := by
      have howner :=
        owner_eq_none_or_some_of_visible hctx current hyvisible
      exact Finset.mem_filter.mpr
        ⟨hmem, by
          simpa [ProgramField.VisibleTo, read, current,
            ProgramField.owner_ofCurrent] using howner⟩
    have heq := hvisible read hmem hmem hvisibleRead
    have hnodup : ((eraseVCtx Γ).map Prod.fst).Nodup := by
      simpa [eraseVCtx_map_fst] using hctx
    have hy_eq : hy = hv.toErased := HasVar.eq_of_nodup hnodup hy hv.toErased
    rw [hy_eq]
    simp [read, current, currentReadEnvToVEnv, heq]
  satisfiable := by
    intro ρ
    rcases hlegal (VEnv.eraseEnv (currentReadEnvToVEnv p ρ)) with
      ⟨value, hvalue⟩
    refine ⟨cast (by rw [hty]) value, ?_⟩
    simpa [evalGuard] using hvalue

/-- Transport a graph expression across an equality of result types. -/
noncomputable def castGraphExpr
    {Γ : VCtx P L} {p : VegasCore P L Γ} {src dst : L.Ty}
    (h : src = dst)
    (expr : ProtocolGraph.GraphExpr L (ProgramField p)
      (fun field => field.ty) src) :
    ProtocolGraph.GraphExpr L (ProgramField p)
      (fun field => field.ty) dst where
  reads := expr.reads
  eval := fun ρ => cast (by rw [h]) (expr.eval ρ)

/-- Transport a graph distribution across an equality of result types. -/
noncomputable def castGraphDist
    {Γ : VCtx P L} {p : VegasCore P L Γ} {src dst : L.Ty}
    (h : src = dst)
    (dist : ProtocolGraph.GraphDist L (ProgramField p)
      (fun field => field.ty) src) :
    ProtocolGraph.GraphDist L (ProgramField p)
      (fun field => field.ty) dst where
  reads := dist.reads
  eval := fun ρ => cast (by rw [h]) (dist.eval ρ)

/-- A write slice over the final field set of a source program. -/
abbrev WriteSlice {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  (field : ProgramField p) →
    Option (ProtocolGraph.StoredValue (L.Val field.ty))

/-- Empty source write slice. -/
def emptySlice {Γ : VCtx P L} (p : VegasCore P L Γ) :
    WriteSlice p :=
  fun _ => none

/-- Singleton source write slice. -/
noncomputable def singleSlice
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (field : ProgramField p)
    (value : ProtocolGraph.StoredValue (L.Val field.ty)) :
    WriteSlice p :=
  fun other =>
    if h : other = field then
      some (cast (by rw [h]) value)
    else
      none

@[simp] theorem singleSlice_self
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (field : ProgramField p)
    (value : ProtocolGraph.StoredValue (L.Val field.ty)) :
    singleSlice field value field = some value := by
  simp [singleSlice]

/-- Initial value of a final field, if it comes from the initial context. -/
noncomputable def initialValue?
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    (field : ProgramField p) :
    Option (L.Val field.ty) := by
  classical
  exact
    if h : ∃ current : VCtxField P L Γ, ofCurrent p current = field then
      let current := Classical.choose h
      let hfield : ofCurrent p current = field := Classical.choose_spec h
      some (cast (by rw [← hfield, ty_ofCurrent]) (current.value env))
    else
      none

/-- Current-context fields are available from the initial source environment. -/
theorem initialValue?_isSome_of_mem_currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    {field : ProgramField p}
    (hmem : field ∈ currentFields p) :
    (initialValue? p env field).isSome := by
  classical
  unfold currentFields at hmem
  have hlist :
      field ∈
        (VCtxField.enumerate Γ).map (fun current => ofCurrent p current) :=
    List.mem_toFinset.mp hmem
  rcases List.mem_map.mp hlist with ⟨current, _hcurrent, hfield⟩
  unfold initialValue?
  rw [dif_pos ⟨current, hfield⟩]
  simp

/-- Value of a final field under a partial node-result assignment. Written
fields are read from their writer's completed slice; initial fields are read
from the initial environment. -/
noncomputable def value?
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (result : ProgramNode p → Option (WriteSlice p))
    (field : ProgramField p) :
    Option (L.Val field.ty) := by
  exact
    match writer? field with
    | some node =>
        match result node with
        | some slice =>
            match slice field with
            | some stored => some stored.raw
            | none => initialValue? p env field
        | none => initialValue? p env field
    | none => initialValue? p env field

theorem value?_isSome_of_result_slice
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p} {node : ProgramNode p} {slice : WriteSlice p}
    {stored : ProtocolGraph.StoredValue (L.Val field.ty)}
    (hwriter : writer? field = some node)
    (hresult : result node = some slice)
    (hslice : slice field = some stored) :
    (value? env result field).isSome := by
  simp [value?, hwriter, hresult, hslice]

theorem value?_isSome_of_initialValue?
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p}
    (hinitial : (initialValue? p env field).isSome) :
    (value? env result field).isSome := by
  cases hwriter : writer? field with
  | none =>
      simpa [value?, hwriter] using hinitial
  | some node =>
      cases hresult : result node with
      | none =>
          simpa [value?, hwriter, hresult] using hinitial
      | some slice =>
          cases hslice : slice field with
          | none =>
              simpa [value?, hwriter, hresult, hslice] using hinitial
          | some stored =>
              simp [value?, hwriter, hresult, hslice]

theorem value?_update_of_writer?_ne
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p} {node : ProgramNode p}
    {slice : WriteSlice p}
    (hne : ProgramField.writer? field ≠ some node) :
    ProgramField.value? env
        (fun candidate => if candidate = node then some slice else result candidate)
        field =
      ProgramField.value? env result field := by
  classical
  cases hwriter : ProgramField.writer? field with
  | none =>
      simp [ProgramField.value?, hwriter]
  | some writer =>
      have hwriter_ne : writer ≠ node := by
        intro heq
        subst writer
        exact hne hwriter
      simp [ProgramField.value?, hwriter, hwriter_ne]

/-- A read environment assembled from a result assignment and a proof that all
declared reads are already available. -/
noncomputable def readEnvOfResult
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (result : ProgramNode p → Option (WriteSlice p))
    (reads : Finset (ProgramField p))
    (available :
      ∀ field, field ∈ reads → (value? env result field).isSome) :
    ProtocolGraph.ReadEnv L (ProgramField p) (fun field => field.ty) reads where
  value field hmem :=
    Classical.choose
      (Option.isSome_iff_exists.mp (available field hmem))

theorem readEnvOfResult_value_eq_of_value?_eq
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {left right : ProgramNode p → Option (WriteSlice p)}
    {reads : Finset (ProgramField p)}
    {availableLeft :
      ∀ field, field ∈ reads → (value? env left field).isSome}
    {availableRight :
      ∀ field, field ∈ reads → (value? env right field).isSome}
    {field : ProgramField p} {hleft : field ∈ reads}
    {hright : field ∈ reads}
    (heq : value? env left field = value? env right field) :
    (readEnvOfResult env left reads availableLeft).value field hleft =
      (readEnvOfResult env right reads availableRight).value field hright := by
  classical
  let leftValue :=
    (readEnvOfResult env left reads availableLeft).value field hleft
  let rightValue :=
    (readEnvOfResult env right reads availableRight).value field hright
  have hleftValue :
      value? env left field = some leftValue :=
    Classical.choose_spec
      (Option.isSome_iff_exists.mp (availableLeft field hleft))
  have hrightValue :
      value? env right field = some rightValue :=
    Classical.choose_spec
      (Option.isSome_iff_exists.mp (availableRight field hright))
  have hsome : some leftValue = some rightValue := by
    rw [heq] at hleftValue
    rw [hrightValue] at hleftValue
    exact hleftValue.symm
  exact Option.some.inj hsome

/-- Final visibility context reached after all source nodes of a program have
executed. -/
def finalVCtx : {Γ : VCtx P L} → VegasCore P L Γ → VCtx P L
  | Γ, .ret _ => Γ
  | _, .letExpr _ _ k => finalVCtx k
  | _, .sample _ _ k => finalVCtx k
  | _, .commit _ _ _ k => finalVCtx k
  | _, .reveal _ _ _ _ k => finalVCtx k

/-- Terminal payoff expressions of a source program, typed over its final
context. -/
def finalPayoffs :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      List (P × L.Expr (erasePubVCtx (finalVCtx p)) L.int)
  | _, .ret payoffs => payoffs
  | _, .letExpr _ _ k => finalPayoffs k
  | _, .sample _ _ k => finalPayoffs k
  | _, .commit _ _ _ k => finalPayoffs k
  | _, .reveal _ _ _ _ k => finalPayoffs k

/-- Embed a final context field into the final field set of the source
program. -/
def ofFinal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      VCtxField P L (finalVCtx p) → ProgramField p
  | _, .ret _, field => .retField field
  | _, .letExpr _ _ k, field => .letTail (ofFinal k field)
  | _, .sample _ _ k, field => .sampleTail (ofFinal k field)
  | _, .commit _ _ _ k, field => .commitTail (ofFinal k field)
  | _, .reveal _ _ _ _ k, field => .revealTail (ofFinal k field)

@[simp] theorem ty_ofFinal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L (finalVCtx p)) →
        (ofFinal p field).ty = field.ty
  | _, .ret _, _ => rfl
  | _, .letExpr _ _ k, field => by
      exact ty_ofFinal k field
  | _, .sample _ _ k, field => by
      exact ty_ofFinal k field
  | _, .commit _ _ _ k, field => by
      exact ty_ofFinal k field
  | _, .reveal _ _ _ _ k, field => by
      exact ty_ofFinal k field

/-- Assemble the final `VEnv` when every final field has a value. -/
noncomputable def finalEnv?
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (value? : (field : ProgramField p) → Option (L.Val field.ty)) :
    Option (VEnv L (finalVCtx p)) := by
  classical
  exact
    if available :
        ∀ field : VCtxField P L (finalVCtx p),
          (value? (ofFinal p field)).isSome then
      some fun x τ h =>
        cast (by
          rw [ty_ofFinal p (.mk h)]
          rfl)
          (Classical.choose
            (Option.isSome_iff_exists.mp (available (.mk h))))
    else
      none

end ProgramField

namespace ProgramNode

/-- Semantic payload of a source occurrence, expressed over the final field set
of the enclosing program. -/
noncomputable def sem :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      WFCtx Γ → FreshBindings p → ViewScoped p →
      Legal p → NormalizedDists p → ProgramNode p →
      ProtocolGraph.NodeSem P (ProgramField p) L
        (fun field => field.ty)
  | _, .letExpr x (b := b) e k, _hctx, _fresh, _scoped,
      _legal, normalized, .letHere =>
      let target : ProgramField (.letExpr x e k) :=
        ProgramField.writtenBy (.letHere (x := x) (e := e) (k := k))
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := x) (τ := .pub b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .assign target
        (ProgramField.castGraphExpr htarget.symm
          (ProgramField.publicGraphExpr (.letExpr x e k) e))
  | _, .letExpr x e k, hctx, fresh, hscoped, legal, normalized,
      .letTail node =>
      (sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped legal normalized node).mapFields
        ProgramField.letTail (fun _ => rfl)
  | _, .sample x (b := b) D k, _hctx, _fresh, _scoped,
      _legal, normalized, .sampleHere =>
      let target : ProgramField (.sample x D k) :=
        ProgramField.writtenBy (.sampleHere (x := x) (D := D) (k := k))
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := x) (τ := .pub b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .sample target
        (ProgramField.castGraphDist htarget.symm
          (ProgramField.publicGraphDist (.sample x D k) D normalized.1))
  | _, .sample x D k, hctx, fresh, hscoped, legal, normalized,
      .sampleTail node =>
      (sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
        legal normalized.2 node).mapFields ProgramField.sampleTail
          (fun _ => rfl)
  | _, .commit x who (b := b) R k, hctx, fresh, hscoped,
      legal, normalized, .commitHere =>
      let target : ProgramField (.commit x who R k) :=
        ProgramField.writtenBy (.commitHere (x := x) (who := who)
          (R := R) (k := k))
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := x) (τ := .hidden who b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .commit who target
        (ProgramField.commitGraphGuard (.commit x who R k) R
          target htarget hctx fresh.1 hscoped.1 legal.1)
  | _, .commit x who R k, hctx, fresh, hscoped, legal, normalized,
      .commitTail node =>
      (sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped.2
        legal.2 normalized node).mapFields ProgramField.commitTail
          (fun _ => rfl)
  | _, .reveal y who x (b := b) hx k, _hctx, _fresh, _scoped,
      _legal, normalized, .revealHere =>
      let source : ProgramField (.reveal y who x hx k) :=
        .revealTail (ProgramField.ofCurrent k (.mk (VHasVar.there hx)))
      let target : ProgramField (.reveal y who x hx k) :=
        ProgramField.writtenBy (.revealHere (y := y) (who := who)
          (x := x) (hx := hx) (k := k))
      have hsource : source.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (VHasVar.there hx))).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := y) (τ := .pub b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .reveal source target (hsource.trans htarget.symm)
  | _, .reveal y who x hx k, hctx, fresh, hscoped, legal, normalized,
      .revealTail node =>
      (sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
        legal normalized node).mapFields ProgramField.revealTail
          (fun _ => rfl)

/-- Every source node semantically writes its syntactic result field. -/
theorem writtenBy_mem_writeFields :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (hctx : WFCtx Γ) → (fresh : FreshBindings p) →
      (hscoped : ViewScoped p) →
      (legal : Legal p) → (normalized : NormalizedDists p) →
      (node : ProgramNode p) →
        ProgramField.writtenBy node ∈
          (ProgramNode.sem hctx fresh hscoped legal normalized node).writeFields
  | _, .letExpr x e k, hctx, fresh, hscoped, legal, normalized, .letHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .letExpr _ _ k, hctx, fresh, hscoped, legal, normalized, .letTail node => by
      exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.letTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped legal normalized node)
  | _, .sample x D k, hctx, fresh, hscoped, legal, normalized, .sampleHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .sample _ _ k, hctx, fresh, hscoped, legal, normalized, .sampleTail node => by
      exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.sampleTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
          legal normalized.2 node)
  | _, .commit x who R k, hctx, fresh, hscoped, legal, normalized, .commitHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .commit _ _ _ k, hctx, fresh, hscoped, legal, normalized, .commitTail node => by
      exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.commitTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped.2
          legal.2 normalized node)
  | _, .reveal y who x hx k, hctx, fresh, hscoped, legal, normalized, .revealHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .reveal _ _ _ _ k, hctx, fresh, hscoped, legal, normalized, .revealTail node => by
      exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.revealTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
          legal normalized node)

/-- Every generated source node writes exactly its structural result field. -/
theorem eq_writtenBy_of_mem_writeFields
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx Γ) (fresh : FreshBindings p)
    (hscoped : ViewScoped p) (legal : Legal p)
    (normalized : NormalizedDists p)
    (node : ProgramNode p) {field : ProgramField p}
    (hwrite :
      field ∈
        (ProgramNode.sem hctx fresh hscoped legal normalized node).writeFields) :
    field = ProgramField.writtenBy node := by
  have hfield :=
    (ProtocolGraph.NodeSem.mem_writeFields_iff_eq_writeTarget _ _).mp hwrite
  have hwritten :=
    (ProtocolGraph.NodeSem.mem_writeFields_iff_eq_writeTarget _ _).mp
      (writtenBy_mem_writeFields hctx fresh hscoped legal normalized node)
  exact hfield.trans hwritten.symm

/-- Membership in a generated node's write set identifies the field's
structural writer. -/
theorem writer?_eq_some_of_mem_writeFields
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx Γ) (fresh : FreshBindings p)
    (hscoped : ViewScoped p) (legal : Legal p)
    (normalized : NormalizedDists p)
    (node : ProgramNode p) {field : ProgramField p}
    (hwrite :
      field ∈
        (ProgramNode.sem hctx fresh hscoped legal normalized node).writeFields) :
    ProgramField.writer? field = some node := by
  have hfield :
      field = ProgramField.writtenBy node :=
    eq_writtenBy_of_mem_writeFields
      hctx fresh hscoped legal normalized node hwrite
  subst field
  exact ProgramField.writer?_writtenBy node

/-- Source reads are causally available: a node reads either an initial current
field of the enclosing program or a field written by an earlier source node. -/
theorem read_current_or_prior_write :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (hctx : WFCtx Γ) → (fresh : FreshBindings p) →
      (hscoped : ViewScoped p) →
      (legal : Legal p) → (normalized : NormalizedDists p) →
      (node : ProgramNode p) → {field : ProgramField p} →
      field ∈ (ProgramNode.sem hctx fresh hscoped legal normalized node).reads →
        field ∈ ProgramField.currentFields p ∨
          ∃ prior : ProgramNode p,
            prior.rank < node.rank ∧
              field ∈
                (ProgramNode.sem hctx fresh hscoped legal normalized prior).writeFields
  | _, .letExpr x e k, hctx, fresh, hscoped, legal, normalized,
      .letHere, field, hread => by
      left
      simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads,
        ProgramField.castGraphExpr, ProgramField.publicGraphExpr] using hread
  | _, .letExpr x e k, hctx, fresh, hscoped, legal, normalized,
      .letTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.letTail (e := e) field).ty = field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k)
            (WFCtx.cons fresh.1 hctx) fresh.2 hscoped legal normalized
            node).mapFields ProgramField.letTail hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases ProtocolGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
          legal normalized node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.letTail_currentFields_or_eq_writtenBy_letHere
            (e := e) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.letHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields hctx fresh hscoped legal normalized
                  (.letHere (x := x) (e := e) (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.letTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.letTail) (hty := hty) hwrite
  | _, .sample x D k, hctx, fresh, hscoped, legal, normalized,
      .sampleHere, field, hread => by
      left
      simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads,
        ProgramField.castGraphDist, ProgramField.publicGraphDist] using hread
  | _, .sample x D k, hctx, fresh, hscoped, legal, normalized,
      .sampleTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.sampleTail (D := D) field).ty = field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k)
            (WFCtx.cons fresh.1 hctx) fresh.2 hscoped legal
            normalized.2 node).mapFields ProgramField.sampleTail
              hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases ProtocolGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
          legal normalized.2 node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.sampleTail_currentFields_or_eq_writtenBy_sampleHere
            (D := D) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.sampleHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields hctx fresh hscoped legal normalized
                  (.sampleHere (x := x) (D := D) (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.sampleTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.sampleTail) (hty := hty) hwrite
  | _, .commit x who R k, hctx, fresh, hscoped, legal, normalized,
      .commitHere, field, hread => by
      left
      simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads,
        ProgramField.commitGraphGuard] using hread
  | _, .commit x who R k, hctx, fresh, hscoped, legal, normalized,
      .commitTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.commitTail (R := R) field).ty = field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k)
            (WFCtx.cons fresh.1 hctx) fresh.2 hscoped.2 legal.2
            normalized node).mapFields ProgramField.commitTail
              hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases ProtocolGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped.2
          legal.2 normalized node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.commitTail_currentFields_or_eq_writtenBy_commitHere
            (R := R) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.commitHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields hctx fresh hscoped legal normalized
                  (.commitHere (x := x) (who := who) (R := R) (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.commitTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.commitTail) (hty := hty) hwrite
  | _, .reveal y who x hx k, hctx, fresh, hscoped, legal, normalized,
      .revealHere, field, hread => by
      left
      have hfield :
          field = ProgramField.ofCurrent (.reveal y who x hx k) (.mk hx) := by
        simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads] using hread
      rw [hfield]
      exact ProgramField.ofCurrent_mem_currentFields
        (.reveal y who x hx k) (.mk hx)
  | _, .reveal y who x hx k, hctx, fresh, hscoped, legal, normalized,
      .revealTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.revealTail (x := x) (hx := hx) field).ty =
              field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k)
            (WFCtx.cons fresh.1 hctx) fresh.2 hscoped legal normalized
            node).mapFields ProgramField.revealTail hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases ProtocolGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k)
          (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
          legal normalized node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.revealTail_currentFields_or_eq_writtenBy_revealHere
            (x := x) (hx := hx) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.revealHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields hctx fresh hscoped legal normalized
                  (.revealHere (y := y) (who := who) (x := x) (hx := hx)
                    (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.revealTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact ProtocolGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.revealTail) (hty := hty) hwrite

/-- Causal prerequisites of a source node.

A source node depends on earlier source nodes whose writes it reads. Source
order remains only as the acyclicity certificate: unrelated source occurrences
are allowed to share a frontier. -/
noncomputable def prereqs
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx Γ) (fresh : FreshBindings p)
    (hscoped : ViewScoped p) (legal : Legal p)
    (normalized : NormalizedDists p) (node : ProgramNode p) :
    Finset (ProgramNode p) := by
  classical
  exact (finset p).filter fun prior =>
    prior.rank < node.rank ∧
      ∃ field,
        field ∈ (ProgramNode.sem hctx fresh hscoped legal normalized node).reads ∧
          field ∈
            (ProgramNode.sem hctx fresh hscoped legal normalized prior).writeFields

/-- The source graph's prerequisites are exactly the causal read dependencies:
if a node reads a field written by another source node, that writer is a
prerequisite of the reader. -/
theorem writer_mem_prereqs_of_read_write
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx Γ) (fresh : FreshBindings p)
    (hscoped : ViewScoped p) (legal : Legal p)
    (normalized : NormalizedDists p)
    {reader writer : ProgramNode p} {field : ProgramField p}
    (hread :
      field ∈
        (ProgramNode.sem hctx fresh hscoped legal normalized reader).reads)
    (hwrite :
      field ∈
        (ProgramNode.sem hctx fresh hscoped legal normalized writer).writeFields) :
    writer ∈
      ProgramNode.prereqs hctx fresh hscoped legal normalized reader := by
  classical
  rcases ProgramNode.read_current_or_prior_write
      hctx fresh hscoped legal normalized reader hread with
    hcurrent | hprior
  · have hnone :
        ProgramField.writer? field = none :=
      ProgramField.writer?_eq_none_of_mem_currentFields hcurrent
    have hsome :
        ProgramField.writer? field = some writer :=
      ProgramNode.writer?_eq_some_of_mem_writeFields
        hctx fresh hscoped legal normalized writer hwrite
    rw [hsome] at hnone
    simp at hnone
  · rcases hprior with ⟨prior, hrank, hpriorWrite⟩
    have hpriorWriter :
        ProgramField.writer? field = some prior :=
      ProgramNode.writer?_eq_some_of_mem_writeFields
        hctx fresh hscoped legal normalized prior hpriorWrite
    have hwriterWriter :
        ProgramField.writer? field = some writer :=
      ProgramNode.writer?_eq_some_of_mem_writeFields
        hctx fresh hscoped legal normalized writer hwrite
    have hwriter_eq : writer = prior := by
      rw [hwriterWriter] at hpriorWriter
      exact Option.some.inj hpriorWriter
    subst writer
    exact Finset.mem_filter.mpr
      ⟨ProgramNode.mem_finset p prior, hrank, ⟨field, hread, hpriorWrite⟩⟩

/-- A source graph slice is well-formed for a node when it has the storage
shape prescribed by the node semantics. Dynamic guard checks are handled by
`actionLegal`. -/
noncomputable def sliceLegal
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx Γ) (fresh : FreshBindings p) (hscoped : ViewScoped p)
    (legal : Legal p) (normalized : NormalizedDists p)
    (node : ProgramNode p) (slice : ProgramField.WriteSlice p) : Prop :=
  match sem hctx fresh hscoped legal normalized node with
  | .assign field _ =>
      ∃ value : L.Val field.ty,
        slice = ProgramField.singleSlice field (.clear value)
  | .sample field _ =>
      ∃ value : L.Val field.ty,
        slice = ProgramField.singleSlice field (.clear value)
  | .commit _ field _ =>
      ∃ value : L.Val field.ty,
        slice = ProgramField.singleSlice field (.hidden value)
  | .reveal _ target _ =>
      ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value)

/-- A legal slice contains a stored value for every semantic field written by
the node. -/
theorem sliceLegal_writeField_isSome
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx Γ) (fresh : FreshBindings p) (hscoped : ViewScoped p)
    (legal : Legal p) (normalized : NormalizedDists p)
    (node : ProgramNode p) {slice : ProgramField.WriteSlice p}
    {field : ProgramField p}
    (hlegal : sliceLegal hctx fresh hscoped legal normalized node slice)
    (hwrite :
      field ∈
        (ProgramNode.sem hctx fresh hscoped legal normalized node).writeFields) :
    ∃ stored : ProtocolGraph.StoredValue (L.Val field.ty),
      slice field = some stored := by
  classical
  cases hsem : ProgramNode.sem hctx fresh hscoped legal normalized node with
  | assign target expr =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value) at hlegal
      rw [ProtocolGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = ProtocolGraph.FieldWrite.clear target := by
        simpa [ProtocolGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [ProtocolGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.clear value, by simp⟩
  | sample target dist =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value) at hlegal
      rw [ProtocolGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = ProtocolGraph.FieldWrite.clear target := by
        simpa [ProtocolGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [ProtocolGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.clear value, by simp⟩
  | commit owner target guard =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.hidden value) at hlegal
      rw [ProtocolGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = ProtocolGraph.FieldWrite.hidden owner target := by
        simpa [ProtocolGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [ProtocolGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.hidden value, by simp⟩
  | reveal source target hty =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value) at hlegal
      rw [ProtocolGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = ProtocolGraph.FieldWrite.clear target := by
        simpa [ProtocolGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [ProtocolGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.clear value, by simp⟩

/-- Dynamic legality for player-chosen source graph slices. Only commit nodes
have an actor, so only commits admit legal player slices. -/
noncomputable def actionLegal
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (hctx : WFCtx Γ) (fresh : FreshBindings p) (hscoped : ViewScoped p)
    (legal : Legal p) (normalized : NormalizedDists p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p))
    (node : ProgramNode p) (slice : ProgramField.WriteSlice p) : Prop :=
  match sem hctx fresh hscoped legal normalized node with
  | .assign _ _ => False
  | .sample _ _ => False
  | .commit _ field guard =>
      ∃ available :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? env result read).isSome,
        ∃ value : L.Val field.ty,
          guard.eval value
              (ProgramField.readEnvOfResult env result guard.reads available) =
            true ∧
          slice = ProgramField.singleSlice field (.hidden value)
  | .reveal _ _ _ => False

/-- If the declared reads of a player-owned node are available, then that
node has a legal concrete graph action. -/
theorem exists_actionLegal_of_reads_available
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (hctx : WFCtx Γ) (fresh : FreshBindings p) (hscoped : ViewScoped p)
    (legal : Legal p) (normalized : NormalizedDists p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p))
    (node : ProgramNode p) {who : P}
    (hactor :
      (sem hctx fresh hscoped legal normalized node).actor = some who)
    (hreads :
      ∀ read, read ∈
        (sem hctx fresh hscoped legal normalized node).reads →
        (ProgramField.value? env result read).isSome) :
    ∃ slice,
      sliceLegal hctx fresh hscoped legal normalized node slice ∧
        actionLegal env hctx fresh hscoped legal normalized result node slice := by
  cases hsem : sem hctx fresh hscoped legal normalized node with
  | assign field expr =>
      simp [ProtocolGraph.NodeSem.actor, hsem] at hactor
  | sample field dist =>
      simp [ProtocolGraph.NodeSem.actor, hsem] at hactor
  | reveal source target hty =>
      simp [ProtocolGraph.NodeSem.actor, hsem] at hactor
  | commit owner field guard =>
      have havailable :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? env result read).isSome := by
        intro read hread
        exact hreads read (by simpa [ProtocolGraph.NodeSem.reads, hsem] using hread)
      let ρ :=
        ProgramField.readEnvOfResult env result guard.reads havailable
      rcases guard.satisfiable ρ with ⟨value, hvalue⟩
      let slice := ProgramField.singleSlice field (.hidden value)
      refine ⟨slice, ?_, ?_⟩
      · rw [sliceLegal, hsem]
        exact ⟨value, rfl⟩
      · rw [actionLegal, hsem]
        exact ⟨havailable, value, hvalue, rfl⟩

/-- Visible reads of a generated commit guard are exactly fields visible to the
committing player.  This is the bridge from graph-local guard invariance to
the FOSG player's private observation. -/
theorem guard_visibleReads_owner_of_sem_commit :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (hctx : WFCtx Γ) → (fresh : FreshBindings p) →
      (hscoped : ViewScoped p) →
      (legal : Legal p) → (normalized : NormalizedDists p) →
      (node : ProgramNode p) →
      {commitWho : P} → {target : ProgramField p} →
      {guard : ProtocolGraph.GraphGuard L (ProgramField p)
        (fun field => field.ty) target} →
      sem hctx fresh hscoped legal normalized node =
        .commit commitWho target guard →
      ∀ read, read ∈ guard.visibleReads →
        read.VisibleTo commitWho
  | _, .letExpr x e k, hctx, fresh, hscoped, legal, normalized,
      .letHere, _, _, _, hsem => by
      simp [sem] at hsem
  | _, .letExpr x e k, hctx, fresh, hscoped, legal, normalized,
      .letTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
            legal normalized node with
      | assign field expr =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              ProtocolGraph.NodeSem.commit owner (.letTail innerTarget)
                  (innerGuard.mapFields ProgramField.letTail
                    (fun _ => rfl)) =
                ProtocolGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, ProtocolGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
              legal normalized node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner
  | _, .sample x D k, hctx, fresh, hscoped, legal, normalized,
      .sampleHere, _, _, _, hsem => by
      simp [sem] at hsem
  | _, .sample x D k, hctx, fresh, hscoped, legal, normalized,
      .sampleTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
            legal normalized.2 node with
      | assign field expr =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              ProtocolGraph.NodeSem.commit owner (.sampleTail innerTarget)
                  (innerGuard.mapFields ProgramField.sampleTail
                    (fun _ => rfl)) =
                ProtocolGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, ProtocolGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
              legal normalized.2 node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner
  | _, .commit x who R k, hctx, fresh, hscoped, legal, normalized,
      .commitHere, commitWho, target, guard, hsem => by
      intro read hread
      have hsem' := by
        simpa [sem, ProgramField.commitGraphGuard] using hsem
      rcases hsem' with ⟨howner, htarget, hguard⟩
      subst commitWho
      subst target
      cases hguard
      exact (Finset.mem_filter.mp hread).2
  | _, .commit x who R k, hctx, fresh, hscoped, legal, normalized,
      .commitTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped.2
            legal.2 normalized node with
      | assign field expr =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              ProtocolGraph.NodeSem.commit owner (.commitTail innerTarget)
                  (innerGuard.mapFields ProgramField.commitTail
                    (fun _ => rfl)) =
                ProtocolGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, ProtocolGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) (WFCtx.cons fresh.1 hctx) fresh.2 hscoped.2
              legal.2 normalized node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner
  | _, .reveal y who x hx k, hctx, fresh, hscoped, legal, normalized,
      .revealHere, _, _, _, hsem => by
      simp [sem] at hsem
  | _, .reveal y who x hx k, hctx, fresh, hscoped, legal, normalized,
      .revealTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
            legal normalized node with
      | assign field expr =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, ProtocolGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              ProtocolGraph.NodeSem.commit owner (.revealTail innerTarget)
                  (innerGuard.mapFields ProgramField.revealTail
                    (fun _ => rfl)) =
                ProtocolGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, ProtocolGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) (WFCtx.cons fresh.1 hctx) fresh.2 hscoped
              legal normalized node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner

/-- A completed source node makes every field it semantically writes available
in the source-level extensional value lookup. -/
theorem value?_isSome_of_completed_write
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (hctx : WFCtx Γ) (fresh : FreshBindings p) (hscoped : ViewScoped p)
    (legal : Legal p) (normalized : NormalizedDists p)
    {result : ProgramNode p → Option (ProgramField.WriteSlice p)}
    {writer : ProgramNode p} {field : ProgramField p}
    (hdone : (result writer).isSome)
    (hcfgLegal :
      ∀ {node slice},
        result node = some slice →
          ProgramNode.sliceLegal hctx fresh hscoped legal normalized node slice)
    (hwrite :
      field ∈
        (ProgramNode.sem hctx fresh hscoped legal normalized writer).writeFields) :
    (ProgramField.value? env result field).isSome := by
  rcases Option.isSome_iff_exists.mp hdone with ⟨slice, hresult⟩
  have hsliceLegal :
      ProgramNode.sliceLegal hctx fresh hscoped legal normalized writer slice :=
    hcfgLegal hresult
  rcases ProgramNode.sliceLegal_writeField_isSome hctx fresh hscoped
      legal normalized writer hsliceLegal hwrite with ⟨stored, hstored⟩
  have hfield :
      field = ProgramField.writtenBy writer :=
    ProgramNode.eq_writtenBy_of_mem_writeFields
      hctx fresh hscoped legal normalized writer hwrite
  subst field
  exact ProgramField.value?_isSome_of_result_slice env
    (ProgramField.writer?_writtenBy writer) hresult hstored

/-- Internal kernel for source graph nodes. Assignment and reveal nodes are
deterministic; sample nodes use the checked PMF distribution; commit nodes are
not internal. -/
noncomputable def internalKernel
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (hctx : WFCtx Γ) (fresh : FreshBindings p) (hscoped : ViewScoped p)
    (legal : Legal p) (normalized : NormalizedDists p)
    (node : ProgramNode p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p)) :
    PMF (ProgramField.WriteSlice p) := by
  classical
  exact
    match hsem : sem hctx fresh hscoped legal normalized node with
    | .assign field expr =>
        if available :
            ∀ read, read ∈ expr.reads →
              (ProgramField.value? env result read).isSome then
          PMF.pure
            (ProgramField.singleSlice field
              (.clear (expr.eval
                (ProgramField.readEnvOfResult env result expr.reads available))))
        else
          PMF.pure (ProgramField.emptySlice p)
    | .sample field dist =>
        if available :
            ∀ read, read ∈ dist.reads →
              (ProgramField.value? env result read).isSome then
          PMF.map
            (fun value => ProgramField.singleSlice field (.clear value))
            (dist.eval
              (ProgramField.readEnvOfResult env result dist.reads available))
        else
          PMF.pure (ProgramField.emptySlice p)
    | .commit _ _ _ =>
        PMF.pure (ProgramField.emptySlice p)
    | .reveal source target hty =>
        if available :
            ∀ read, read ∈ ({source} : Finset (ProgramField p)) →
              (ProgramField.value? env result read).isSome then
          let ρ :=
            ProgramField.readEnvOfResult env result
              ({source} : Finset (ProgramField p)) available
          PMF.pure
            (ProgramField.singleSlice target
              (.clear (cast (by rw [hty]) (ρ.value source (by simp)))))
        else
          PMF.pure (ProgramField.emptySlice p)

end ProgramNode

/-- Checked Vegas syntax compiled to the graph-native protocol graph.

This is the graph-native semantic object.  Source occurrences become graph
nodes, and prerequisites are the causal read dependencies between them; source
order is retained only as the rank function proving acyclicity. -/
noncomputable def syntaxProtocolGraph
    (g : WFProgram P L) : ProtocolGraph P L where
  Node := ProgramNode g.prog
  Field := ProgramField g.prog
  nodeDecEq := ProgramNode.instDecidableEq g.prog
  fieldDecEq := ProgramField.instDecidableEq g.prog
  nodes := ProgramNode.finset g.prog
  fields := ProgramField.finset g.prog
  fieldTy := fun field => field.ty
  fieldOwner := fun field => field.owner
  initial := ProgramField.initialValue? g.prog g.env
  sem := ProgramNode.sem g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized
  prereqs := ProgramNode.prereqs g.wctx g.wf.1 g.wf.2.2
    g.legal g.normalized
  rank := fun node => node.rank
  prereqs_subset_nodes := by
    intro node prereq _hnode hpre
    exact (Finset.mem_filter.mp hpre).1
  prereq_rank_lt := by
    intro node prereq _hnode hpre
    exact (Finset.mem_filter.mp hpre).2.1
  read_fields_mem := by
    intro node field _hnode _hfield
    exact ProgramField.mem_finset g.prog field
  write_fields_mem := by
    intro node write _hnode hwrite
    exact ProgramField.mem_finset g.prog write.field
  no_duplicate_writes := by
    intro node field left right _hnode hleft hright hleftField hrightField
    cases hsem : ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
        g.legal g.normalized node with
    | assign target expr =>
        simp [ProtocolGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
    | sample target dist =>
        simp [ProtocolGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
    | commit who target guard =>
        simp [ProtocolGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
    | reveal source target hty =>
        simp [ProtocolGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
  sliceLegal := ProgramNode.sliceLegal g.wctx g.wf.1 g.wf.2.2
    g.legal g.normalized
  actionLegal := ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
    g.legal g.normalized
  internalKernel := ProgramNode.internalKernel g.env g.wctx g.wf.1 g.wf.2.2
    g.legal g.normalized

/-- Static read-availability invariant needed by the graph FOSG view: every
declared read of every frontier node has a value in the extensional graph
configuration. -/
def syntaxReadsAvailableAtFrontier
    (g : WFProgram P L) : Prop :=
  ∀ (cfg : (syntaxProtocolGraph g).Configuration) {node : ProgramNode g.prog},
    node ∈ cfg.frontier →
      ∀ read, read ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized node).reads →
        (ProgramField.value? g.env cfg.result read).isSome

/-- Source graph frontier reads are available in every configuration. -/
theorem syntaxReadsAvailableAtFrontier_of_wfProgram
    (g : WFProgram P L) :
    syntaxReadsAvailableAtFrontier g := by
  intro cfg node hfrontier read hread
  rcases ProgramNode.read_current_or_prior_write
      g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized node hread with
    hcurrent | hprior
  · exact ProgramField.value?_isSome_of_initialValue? g.env
      (ProgramField.initialValue?_isSome_of_mem_currentFields
        g.prog g.env hcurrent)
  · rcases hprior with ⟨prior, hrank, hwrite⟩
    have hpre : prior ∈ (syntaxProtocolGraph g).prereqs node := by
      change prior ∈
        ProgramNode.prereqs g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized node
      exact Finset.mem_filter.mpr
        ⟨ProgramNode.mem_finset g.prog prior, hrank,
          ⟨read, hread, hwrite⟩⟩
    have hdone : (cfg.result prior).isSome :=
      cfg.result_some_of_prereq_of_mem_frontier hfrontier hpre
    have hcfgLegal :
        ∀ {node slice},
          cfg.result node = some slice →
            ProgramNode.sliceLegal g.wctx g.wf.1 g.wf.2.2
              g.legal g.normalized node slice := by
      intro node slice hresult
      simpa [syntaxProtocolGraph] using cfg.legal hresult
    exact ProgramNode.value?_isSome_of_completed_write
      g.env g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized
      hdone hcfgLegal hwrite

/-- Two syntax-graph configurations agree on every read that can affect a
generated commit guard. -/
def AgreeOnGuardVisibleReads
    (g : WFProgram P L)
    (left right : (syntaxProtocolGraph g).Configuration)
    (node : ProgramNode g.prog) : Prop :=
  ∀ {owner : P} {target : ProgramField g.prog}
    {guard : ProtocolGraph.GraphGuard L (ProgramField g.prog)
      (fun field => field.ty) target},
    ProgramNode.sem g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized node =
        .commit owner target guard →
      ∀ read, read ∈ guard.visibleReads →
        ProgramField.value? g.env left.result read =
          ProgramField.value? g.env right.result read

theorem AgreeOnGuardVisibleReads.symm
    {g : WFProgram P L}
    {left right : (syntaxProtocolGraph g).Configuration}
    {node : ProgramNode g.prog}
    (h : AgreeOnGuardVisibleReads g left right node) :
    AgreeOnGuardVisibleReads g right left node := by
  intro owner target guard hsem read hread
  exact (h hsem read hread).symm

/-- Dynamic commit legality transfers across syntax-graph configurations that
agree on the visible reads of the guard attached to the node. The frontier
hypothesis supplies availability of the guard reads in the target
configuration. -/
theorem syntaxGraph_actionLegal_of_guardVisibleValue_eq
    (g : WFProgram P L)
    {left right : (syntaxProtocolGraph g).Configuration}
    {node : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    (hfrontierRight : node ∈ right.frontier)
    (hvisible : AgreeOnGuardVisibleReads g left right node)
    (haction :
      (syntaxProtocolGraph g).actionLegal left.result node slice) :
    (syntaxProtocolGraph g).actionLegal right.result node slice := by
  classical
  change
    ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized left.result node slice at haction
  change
    ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized right.result node slice
  cases hsem :
      ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
        g.legal g.normalized node with
  | assign field expr =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | sample field dist =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | reveal source target hty =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | commit owner field guard =>
      rw [ProgramNode.actionLegal, hsem] at haction ⊢
      rcases haction with
        ⟨availableLeft, value, hguardEval, hslice⟩
      have availableRight :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? g.env right.result read).isSome := by
        intro read hread
        exact syntaxReadsAvailableAtFrontier_of_wfProgram g
          right hfrontierRight read
          (by simpa [ProtocolGraph.NodeSem.reads, hsem] using hread)
      refine ⟨availableRight, value, ?_, hslice⟩
      let ρleft :=
        ProgramField.readEnvOfResult g.env left.result
          guard.reads availableLeft
      let ρright :=
        ProgramField.readEnvOfResult g.env right.result
          guard.reads availableRight
      have hguardEq :
          guard.eval value ρleft = guard.eval value ρright := by
        apply guard.eval_eq_of_visible_eq
        intro read hleft hright hreadVisible
        have hvalueEq :
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read := by
          exact hvisible (owner := owner) (target := field)
            (guard := guard) hsem read hreadVisible
        simpa [ρleft, ρright] using
          (ProgramField.readEnvOfResult_value_eq_of_value?_eq
            g.env (left := left.result) (right := right.result)
            (availableLeft := availableLeft)
            (availableRight := availableRight)
            (field := read) (hleft := hleft) (hright := hright)
            hvalueEq)
      rw [← hguardEq]
      exact hguardEval

/-- A current frontier node cannot be the structural writer of a field read by
another current frontier node.  If it were, the writer would be a prerequisite
of the reader, contradicting simultaneous frontier membership. -/
theorem syntaxGraph_writer?_ne_of_frontier_read
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {writer reader : ProgramNode g.prog} {field : ProgramField g.prog}
    (hwriterFrontier : writer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader).reads) :
    ProgramField.writer? field ≠ some writer := by
  intro hfieldWriter
  rcases ProgramNode.read_current_or_prior_write
      g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized reader hread with
    hcurrent | hprior
  · have hnone :
        ProgramField.writer? field = none :=
      ProgramField.writer?_eq_none_of_mem_currentFields hcurrent
    rw [hfieldWriter] at hnone
    simp at hnone
  · rcases hprior with ⟨prior, hrank, hpriorWrite⟩
    have hpriorWriter :
        ProgramField.writer? field = some prior :=
      ProgramNode.writer?_eq_some_of_mem_writeFields
        g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized prior hpriorWrite
    rw [hfieldWriter] at hpriorWriter
    have hwriter_eq_prior : writer = prior :=
      Option.some.inj hpriorWriter
    subst prior
    have hpre :
        writer ∈ (syntaxProtocolGraph g).prereqs reader := by
      change writer ∈
        ProgramNode.prereqs g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader
      exact Finset.mem_filter.mpr
        ⟨ProgramNode.mem_finset g.prog writer, hrank,
          ⟨field, hread, hpriorWrite⟩⟩
    exact
      (ProtocolGraph.Configuration.not_prereq_of_mem_frontier
        hwriterFrontier hreaderFrontier) hpre

/-- A frontier node cannot share the frontier with a node that reads one of the
fields it writes.  This packages the `writer?` formulation in terms of the
semantic write set exposed by `NodeSem.writeFields`. -/
theorem syntaxGraph_writer_not_frontier_with_reader_of_read_write
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {writer reader : ProgramNode g.prog} {field : ProgramField g.prog}
    (hwriterFrontier : writer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader).reads)
    (hwrite :
      field ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized writer).writeFields) :
    False := by
  have hwriter :
      ProgramField.writer? field = some writer :=
    ProgramNode.writer?_eq_some_of_mem_writeFields
      g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized writer hwrite
  exact
    (syntaxGraph_writer?_ne_of_frontier_read g
      hwriterFrontier hreaderFrontier hread) hwriter

/-- A reveal node and a later node that reads the reveal target cannot share a
frontier.  In the current alias-writing reveal semantics, the reveal event is
the writer of the public alias; any post-reveal use must wait for that write.

This is the regression guard for the reveal-ordering invariant: changing reveal
so it no longer writes a value field must replace this dependency with an
equally explicit reveal-token dependency. -/
theorem syntaxGraph_reveal_not_frontier_with_reader_of_target
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {revealer reader : ProgramNode g.prog}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    (hrevealFrontier : revealer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hsem :
      ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
        g.legal g.normalized revealer =
        ProtocolGraph.NodeSem.reveal source target hty)
    (hread :
      target ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader).reads) :
    False := by
  apply syntaxGraph_writer_not_frontier_with_reader_of_read_write
    g hrevealFrontier hreaderFrontier hread
  rw [hsem]
  simp [ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
    ProtocolGraph.FieldWrite.field]

/-- Executing one frontier node leaves every read of another current frontier
node unchanged. -/
theorem syntaxGraph_value?_withResult_eq_of_frontier_read
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {writer reader : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    {hwriterFrontier : writer ∈ cfg.frontier}
    {hwriterLegal : (syntaxProtocolGraph g).sliceLegal writer slice}
    {field : ProgramField g.prog}
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader).reads) :
    ProgramField.value? g.env
        ((cfg.withResult slice hwriterFrontier hwriterLegal).result) field =
      ProgramField.value? g.env cfg.result field := by
  classical
  have hne :
      ProgramField.writer? field ≠ some writer :=
    syntaxGraph_writer?_ne_of_frontier_read g
      hwriterFrontier hreaderFrontier hread
  simpa [ProtocolGraph.Configuration.withResult,
    ProtocolGraph.Configuration.updateResult] using
    (ProgramField.value?_update_of_writer?_ne
      (env := g.env) (result := cfg.result) (field := field)
      (node := writer) (slice := slice) hne)

/-- Dynamic commit legality for one frontier node is stable after executing a
different frontier node. -/
theorem syntaxGraph_actionLegal_after_frontier_withResult_of_ne
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstSlice secondSlice : ProgramField.WriteSlice g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (syntaxProtocolGraph g).sliceLegal first firstSlice)
    (hsecondAction :
      (syntaxProtocolGraph g).actionLegal cfg.result second secondSlice) :
    (syntaxProtocolGraph g).actionLegal
      ((cfg.withResult firstSlice hfirst hfirstLegal).result)
      second secondSlice := by
  classical
  have hsecondAfter :
      second ∈ (cfg.withResult firstSlice hfirst hfirstLegal).frontier :=
    cfg.withResult_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
  refine
    syntaxGraph_actionLegal_of_guardVisibleValue_eq
      g hsecondAfter ?_ hsecondAction
  intro owner target guard hsem read hreadVisible
  have hread :
      read ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized second).reads := by
    rw [hsem]
    exact guard.visibleReads_subset_reads hreadVisible
  exact
    (syntaxGraph_value?_withResult_eq_of_frontier_read
      g (writer := first) (reader := second)
      (slice := firstSlice) hsecond hread).symm

/-- A player primitive event for a frontier node remains available after a
different frontier node has executed. -/
theorem syntaxGraph_available_after_frontier_withResult_of_ne
    (g : WFProgram P L) (who : P)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {first : ProgramNode g.prog}
    {firstSlice : ProgramField.WriteSlice g.prog}
    {action : ProtocolGraph.PlayerAction (syntaxProtocolGraph g) who}
    (hfirst : first ∈ cfg.frontier)
    (hne : action.node ≠ first)
    (hfirstLegal : (syntaxProtocolGraph g).sliceLegal first firstSlice)
    (haction :
      action ∈ ProtocolGraph.available (syntaxProtocolGraph g) cfg who) :
    action ∈ ProtocolGraph.available (syntaxProtocolGraph g)
      (cfg.withResult firstSlice hfirst hfirstLegal) who := by
  rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
  exact ⟨
    cfg.withResult_mem_frontier_of_ne hfirst hfrontier hne hfirstLegal,
    hactor,
    hslice,
    syntaxGraph_actionLegal_after_frontier_withResult_of_ne
      g hfirst hfrontier hne hfirstLegal hlegal⟩

/-- Source graph commits cannot deadlock: the generated guard carries a
satisfying action for the available read environment. -/
theorem syntaxProtocolGraph_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasAvailablePlayerActions := by
  intro cfg node who hfrontier hactor
  rcases ProgramNode.exists_actionLegal_of_reads_available
      g.env g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized cfg.result node
      (who := who)
      (by simpa [syntaxProtocolGraph] using hactor)
      (syntaxReadsAvailableAtFrontier_of_wfProgram g cfg hfrontier) with
    ⟨slice, hslice, haction⟩
  exact ⟨slice, hslice, haction⟩

/-- Source graph frontier rounds are stable: executing one frontier node cannot
invalidate a player action for another current frontier node. -/
theorem syntaxProtocolGraph_hasStableFrontierRounds
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasStableFrontierRounds where
  availablePlayerActions := syntaxProtocolGraph_hasAvailablePlayerActions g
  actionStable := by
    intro cfg first firstSlice hfirst who action hfrontier hne
      hfirstLegal haction
    exact syntaxGraph_available_after_frontier_withResult_of_ne
      g who hfirst hne hfirstLegal haction

/-- Public observation of the graph-native syntax machine.

This is the protocol transcript that every player may use for legality:
which graph nodes have already produced a result, together with public field
values. It deliberately does not expose hidden field values. -/
@[ext]
structure SyntaxPublicObs (g : WFProgram P L) where
  done : ProgramNode g.prog → Bool
  value? : (field : ProgramField g.prog) → Option (L.Val field.ty)

/-- Private observation of the graph-native syntax machine: the visible part
of the extensional field assignment. -/
@[ext]
structure SyntaxPrivateObs (g : WFProgram P L) (who : P) where
  value? : (field : ProgramField g.prog) → Option (L.Val field.ty)

/-- Recover a field value from a graph-native syntax configuration. -/
noncomputable def syntaxGraphConfigValue?
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration)
    (field : ProgramField g.prog) :
    Option (L.Val field.ty) :=
  ProgramField.value? g.env cfg.result field

/-- Public observation for the graph-native syntax machine. -/
noncomputable def syntaxGraphPublicView
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration) :
    SyntaxPublicObs g where
  done := fun node => (cfg.result node).isSome
  value? := fun field =>
    if field.owner = none then
      syntaxGraphConfigValue? g cfg field
    else
      none

/-- Player observation for the graph-native syntax machine. -/
noncomputable def syntaxGraphObserve
    (g : WFProgram P L) (who : P)
    (cfg : (syntaxProtocolGraph g).Configuration) :
    SyntaxPrivateObs g who where
  value? := fun field =>
    if field.VisibleTo who then
      syntaxGraphConfigValue? g cfg field
    else
      none

theorem syntaxGraphPublicView_done_eq_of_eq
    (g : WFProgram P L)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hobs : syntaxGraphPublicView g left = syntaxGraphPublicView g right)
    (node : ProgramNode g.prog) :
    (left.result node).isSome = (right.result node).isSome := by
  have h := congrArg (fun obs => obs.done node) hobs
  simpa [syntaxGraphPublicView] using h

theorem syntaxGraphPublicView_frontier_eq_of_eq
    (g : WFProgram P L)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hobs : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    left.frontier = right.frontier := by
  classical
  apply Finset.ext
  intro node
  constructor
  · intro hnode
    rw [ProtocolGraph.Configuration.mem_frontier_iff] at hnode ⊢
    refine ⟨hnode.1, ?_, ?_⟩
    · have hsome :=
        syntaxGraphPublicView_done_eq_of_eq g hobs node
      have hnone :
          (left.result node).isNone = (right.result node).isNone := by
        cases hleft : left.result node <;>
          cases hright : right.result node <;>
            simp [hleft, hright] at hsome ⊢
      simpa [hnone] using hnode.2.1
    · intro prereq hpre
      have hdone := hnode.2.2 hpre
      have hdoneData :=
        ((syntaxProtocolGraph g).mem_done_iff left.result prereq).mp hdone
      have hsome :=
        syntaxGraphPublicView_done_eq_of_eq g hobs prereq
      have hsomeRight : (right.result prereq).isSome := by
        simpa [hsome] using hdoneData.2
      exact ((syntaxProtocolGraph g).mem_done_iff right.result prereq).mpr
        ⟨hdoneData.1, hsomeRight⟩
  · intro hnode
    rw [ProtocolGraph.Configuration.mem_frontier_iff] at hnode ⊢
    refine ⟨hnode.1, ?_, ?_⟩
    · have hsome :=
        syntaxGraphPublicView_done_eq_of_eq g hobs node
      have hnone :
          (left.result node).isNone = (right.result node).isNone := by
        cases hleft : left.result node <;>
          cases hright : right.result node <;>
            simp [hleft, hright] at hsome ⊢
      simpa [hnone] using hnode.2.1
    · intro prereq hpre
      have hdone := hnode.2.2 hpre
      have hdoneData :=
        ((syntaxProtocolGraph g).mem_done_iff right.result prereq).mp hdone
      have hsome :=
        syntaxGraphPublicView_done_eq_of_eq g hobs prereq
      have hsomeLeft : (left.result prereq).isSome := by
        simpa [hsome] using hdoneData.2
      exact ((syntaxProtocolGraph g).mem_done_iff left.result prereq).mpr
        ⟨hdoneData.1, hsomeLeft⟩

theorem syntaxGraphObserve_value?_eq_of_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hobs : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    {field : ProgramField g.prog}
    (hvisible : field.VisibleTo who) :
    syntaxGraphConfigValue? g left field =
      syntaxGraphConfigValue? g right field := by
  have h := congrArg (fun obs => obs.value? field) hobs
  simpa [syntaxGraphObserve, hvisible] using h

/-- Dynamic action legality for a commit transfers across configurations that
agree on the committing player's observation, provided the target node is still
on the frontier.  The only nontrivial case is a commit guard: generated graph
guards are invariant under changes to hidden reads outside the player's view. -/
theorem syntaxGraph_actionLegal_of_observe_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    {node : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    (hfrontierRight : node ∈ right.frontier)
    (hactor :
      ((syntaxProtocolGraph g).sem node).actor = some who)
    (hobs : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (haction :
      (syntaxProtocolGraph g).actionLegal left.result node slice) :
    (syntaxProtocolGraph g).actionLegal right.result node slice := by
  classical
  change
    (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized node).actor = some who at hactor
  change
    ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized left.result node slice at haction
  change
    ProgramNode.actionLegal g.env g.wctx g.wf.1 g.wf.2.2
      g.legal g.normalized right.result node slice
  cases hsem :
      ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
        g.legal g.normalized node with
  | assign field expr =>
      simp [ProtocolGraph.NodeSem.actor, hsem] at hactor
  | sample field dist =>
      simp [ProtocolGraph.NodeSem.actor, hsem] at hactor
  | reveal source target hty =>
      simp [ProtocolGraph.NodeSem.actor, hsem] at hactor
  | commit owner field guard =>
      have howner : owner = who := by
        simpa [ProtocolGraph.NodeSem.actor, hsem] using hactor
      subst owner
      rw [ProgramNode.actionLegal, hsem] at haction ⊢
      rcases haction with
        ⟨availableLeft, value, hguardEval, hslice⟩
      have availableRight :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? g.env right.result read).isSome := by
        intro read hread
        exact syntaxReadsAvailableAtFrontier_of_wfProgram g
          right hfrontierRight read
          (by simpa [ProtocolGraph.NodeSem.reads, hsem] using hread)
      refine ⟨availableRight, value, ?_, hslice⟩
      let ρleft :=
        ProgramField.readEnvOfResult g.env left.result
          guard.reads availableLeft
      let ρright :=
        ProgramField.readEnvOfResult g.env right.result
          guard.reads availableRight
      have hguardEq :
          guard.eval value ρleft = guard.eval value ρright := by
        apply guard.eval_eq_of_visible_eq
        intro read hleft hright hvisible
        have hreadVisible :
            read.VisibleTo who :=
          ProgramNode.guard_visibleReads_owner_of_sem_commit
            g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized
            node hsem read hvisible
        have hvalueEq :
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read := by
          have hsyntax :=
            syntaxGraphObserve_value?_eq_of_eq g who hobs hreadVisible
          simpa [syntaxGraphConfigValue?, syntaxProtocolGraph,
            ProtocolGraph.value?, ProgramField.value?] using hsyntax
        simpa [ρleft, ρright] using
          (ProgramField.readEnvOfResult_value_eq_of_value?_eq
            g.env (left := left.result) (right := right.result)
            (availableLeft := availableLeft)
            (availableRight := availableRight)
            (field := read) (hleft := hleft) (hright := hright)
            hvalueEq)
      rw [← hguardEq]
      exact hguardEval

/-- Player action availability in the syntax graph is determined by the public
transcript together with the acting player's private observation. -/
theorem syntaxGraph_available_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    ProtocolGraph.available (syntaxProtocolGraph g) left who =
      ProtocolGraph.available (syntaxProtocolGraph g) right who := by
  classical
  ext action
  constructor
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierRight : action.node ∈ right.frontier := by
      simpa [syntaxGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierRight, hactor, hslice,
      syntaxGraph_actionLegal_of_observe_eq g who hfrontierRight
        hactor hpriv hlegal⟩
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierLeft : action.node ∈ left.frontier := by
      simpa [syntaxGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierLeft, hactor, hslice,
      syntaxGraph_actionLegal_of_observe_eq g who hfrontierLeft
        hactor hpriv.symm hlegal⟩

/-- Outcome projection for the graph-native syntax machine. Nonterminal or
ill-assembled configurations project to the default zero outcome. -/
noncomputable def syntaxGraphOutcome
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration) : Outcome P :=
  match ProgramField.finalEnv? g.prog (syntaxGraphConfigValue? g cfg) with
  | some env => evalPayoffs (ProgramField.finalPayoffs g.prog) env
  | none => 0

/-- Observation/outcome interface for the graph-native syntax machine. -/
noncomputable def syntaxGraphMachineInterface
    (g : WFProgram P L) :
    ProtocolGraph.MachineInterface (syntaxProtocolGraph g) where
  Public := SyntaxPublicObs g
  Obs := fun who => SyntaxPrivateObs g who
  Outcome := Outcome P
  publicView := syntaxGraphPublicView g
  observe := syntaxGraphObserve g
  outcome := syntaxGraphOutcome g
  utility := fun outcome who => (outcome who : ℝ)

/-- Graph-native machine obtained directly from checked Vegas syntax. -/
noncomputable def syntaxGraphMachine
    (g : WFProgram P L) : Machine P :=
  (syntaxProtocolGraph g).toMachine (syntaxGraphMachineInterface g)

/-- FOSG view of the graph-native syntax machine. -/
noncomputable def syntaxGraphFOSGView
    (g : WFProgram P L) :
    (syntaxGraphMachine g).FOSGView :=
  (syntaxProtocolGraph g).toFOSGView (syntaxGraphMachineInterface g)
    (syntaxProtocolGraph_hasStableFrontierRounds g)

/-- Primitive machine event blocks extracted from a bounded syntax-graph FOSG
history. Each block is one frontier round of the public FOSG view. -/
noncomputable def syntaxGraphFOSGHistoryEventBlocks
    (g : WFProgram P L) (horizon : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)) :
    List (List (syntaxGraphMachine g).Event) :=
  ProtocolGraph.boundedFOSGHistoryEventBlocks
    (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
    (syntaxProtocolGraph_hasStableFrontierRounds g) horizon h

/-- Primitive machine events represented by one syntax-graph FOSG frontier
round. -/
noncomputable def syntaxGraphRoundPrimitiveEvents
    (g : WFProgram P L)
    (cfg : (syntaxGraphMachine g).State)
    (joint : GameTheory.JointAction (syntaxGraphFOSGView g).Act) :
    List (syntaxGraphMachine g).Event := by
  simpa [syntaxGraphMachine, syntaxGraphFOSGView] using
    (ProtocolGraph.roundPrimitiveEvents (syntaxProtocolGraph g)
      (syntaxGraphMachineInterface g) cfg joint)

/-- Every bounded syntax-graph FOSG history is backed by a primitive machine
blocked run whose support contains the same checkpoint state. -/
theorem syntaxGraphFOSGHistory_state_mem_runEventBlocksFrom_support
    (g : WFProgram P L) (horizon : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((syntaxGraphMachine g).runEventBlocksFrom
        (syntaxGraphFOSGHistoryEventBlocks g horizon h)
        (syntaxGraphMachine g).init).support := by
  simpa [syntaxGraphFOSGHistoryEventBlocks, syntaxGraphMachine,
    syntaxGraphFOSGView] using
    (ProtocolGraph.boundedFOSGHistory_state_mem_runEventBlocksFrom_support
      (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
      (syntaxProtocolGraph_hasStableFrontierRounds g) horizon h)

/-- One bounded syntax-graph FOSG transition, projected to the history's
extracted event-block prefix and successor checkpoint state, is exactly the
corresponding primitive machine blocked run. -/
theorem syntaxGraphFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
    (g : WFProgram P L) (horizon : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History))
    (action :
      (((syntaxGraphFOSGView g).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          (syntaxGraphFOSGHistoryEventBlocks g horizon h ++
              [syntaxGraphRoundPrimitiveEvents g h.lastState.state action.1],
            dst.state))
        (((syntaxGraphFOSGView g).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (syntaxGraphFOSGHistoryEventBlocks g horizon h ++
              [syntaxGraphRoundPrimitiveEvents g h.lastState.state action.1],
            next))
        ((syntaxGraphMachine g).runEventBlocksFrom
          [syntaxGraphRoundPrimitiveEvents g h.lastState.state action.1]
          h.lastState.state) := by
  simpa [syntaxGraphFOSGHistoryEventBlocks, syntaxGraphMachine,
    syntaxGraphFOSGView, syntaxGraphRoundPrimitiveEvents] using
    (ProtocolGraph.boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
      (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
      (syntaxProtocolGraph_hasStableFrontierRounds g) horizon h action)

/-- Continuation form of one syntax-graph FOSG transition: binding over the
bounded FOSG transition is the same as binding over the primitive blocked
machine run and reattaching the bounded presentation depth. -/
theorem syntaxGraphFOSG_transition_bind_eq_runEventBlocksFrom_bind
    (g : WFProgram P L) (horizon : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History))
    (action :
      (((syntaxGraphFOSGView g).toBoundedFOSG horizon).LegalAction
        h.lastState))
    {α : Type}
    (K : (syntaxGraphMachine g).BoundedState horizon → PMF α) :
    ((((syntaxGraphFOSGView g).toBoundedFOSG horizon).transition
          h.lastState action).bind K) =
      ((syntaxGraphMachine g).runEventBlocksFrom
          [syntaxGraphRoundPrimitiveEvents g h.lastState.state action.1]
          h.lastState.state).bind
        (fun next =>
          K (h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next)) := by
  simpa [syntaxGraphMachine, syntaxGraphFOSGView,
    syntaxGraphRoundPrimitiveEvents] using
    (ProtocolGraph.boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
      (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
      (syntaxProtocolGraph_hasStableFrontierRounds g) horizon h action K)

/-- One-step form matching `FOSG.History.runDistFrom` for syntax graphs:
extend the FOSG history by the sampled bounded destination, then project to
the extracted primitive event blocks and checkpoint state. -/
theorem syntaxGraphFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
    (g : WFProgram P L) (horizon : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History))
    (action :
      (((syntaxGraphFOSGView g).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          let h' := h.extendByOutcome action dst
          (syntaxGraphFOSGHistoryEventBlocks g horizon h',
            h'.lastState.state))
        (((syntaxGraphFOSGView g).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (syntaxGraphFOSGHistoryEventBlocks g horizon h ++
              [syntaxGraphRoundPrimitiveEvents g h.lastState.state action.1],
            next))
        ((syntaxGraphMachine g).runEventBlocksFrom
          [syntaxGraphRoundPrimitiveEvents g h.lastState.state action.1]
          h.lastState.state) := by
  simpa [syntaxGraphFOSGHistoryEventBlocks, syntaxGraphMachine,
    syntaxGraphFOSGView, syntaxGraphRoundPrimitiveEvents] using
    (ProtocolGraph.boundedFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
      (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
      (syntaxProtocolGraph_hasStableFrontierRounds g) horizon h action)

/-- Player round-action availability in the syntax graph is determined by the
public transcript together with the acting player's private observation. -/
theorem syntaxGraph_roundAvailable_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    ProtocolGraph.roundAvailable (syntaxProtocolGraph g) left who =
      ProtocolGraph.roundAvailable (syntaxProtocolGraph g) right who := by
  classical
  have hfrontierEq := syntaxGraphPublicView_frontier_eq_of_eq g hpub
  ext action
  constructor
  · intro haction node hfrontier hactor
    have hfrontierLeft : node ∈ left.frontier := by
      simpa [hfrontierEq] using hfrontier
    rcases haction hfrontierLeft hactor with ⟨hslice, hlegal⟩
    exact ⟨hslice,
      syntaxGraph_actionLegal_of_observe_eq g who hfrontier
        hactor hpriv hlegal⟩
  · intro haction node hfrontier hactor
    have hfrontierRight : node ∈ right.frontier := by
      simpa [hfrontierEq] using hfrontier
    rcases haction hfrontierRight hactor with ⟨hslice, hlegal⟩
    exact ⟨hslice,
      syntaxGraph_actionLegal_of_observe_eq g who hfrontier
        hactor hpriv.symm hlegal⟩

/-- The active-player set of a syntax-graph frontier round is determined by
the public transcript. -/
theorem syntaxGraph_roundActive_eq_of_publicView_eq
    (g : WFProgram P L)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    ProtocolGraph.roundActive (syntaxProtocolGraph g) left =
      ProtocolGraph.roundActive (syntaxProtocolGraph g) right := by
  classical
  have hfrontier := syntaxGraphPublicView_frontier_eq_of_eq g hpub
  unfold ProtocolGraph.roundActive
  rw [hfrontier]

/-- Player-facing frontier-round menus in the syntax graph are determined by
the public transcript together with the player's private observation.

This is the protocol-level "the player knows what they can do" invariant:
two configurations indistinguishable to `who` offer the same optional menu to
`who`, including whether `who` is called at all. -/
theorem syntaxGraph_roundMenu_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    ProtocolGraph.roundMenu (syntaxProtocolGraph g) left who =
      ProtocolGraph.roundMenu (syntaxProtocolGraph g) right who := by
  have hactive :=
    syntaxGraph_roundActive_eq_of_publicView_eq g hpub
  have havailable :=
    syntaxGraph_roundAvailable_eq_of_observation_eq g who hpriv hpub
  simp [ProtocolGraph.roundMenu, hactive, havailable]

/-- At a bounded syntax-graph FOSG state before the cutoff, legal optional
moves are determined by the player's latest private observation and the public
transcript. -/
theorem syntaxGraph_boundedAvailableMovesAtState_eq_of_observation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {left right : (syntaxGraphMachine g).BoundedState horizon}
    (hcut : ¬ horizon ≤ left.depth)
    (hcut' : ¬ horizon ≤ right.depth)
    (hpriv :
      syntaxGraphObserve g who left.state =
        syntaxGraphObserve g who right.state)
    (hpub :
      syntaxGraphPublicView g left.state =
        syntaxGraphPublicView g right.state) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtState
        left who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtState
        right who := by
  classical
  have hroundActive :
      ProtocolGraph.roundActive (syntaxProtocolGraph g) left.state =
        ProtocolGraph.roundActive (syntaxProtocolGraph g) right.state :=
    syntaxGraph_roundActive_eq_of_publicView_eq g hpub
  have hroundAvailable :
      ProtocolGraph.roundAvailable (syntaxProtocolGraph g) left.state who =
        ProtocolGraph.roundAvailable (syntaxProtocolGraph g) right.state who :=
    syntaxGraph_roundAvailable_eq_of_observation_eq g who hpriv hpub
  have hactive :
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active left =
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active right := by
    ext player
    simp [Machine.FOSGView.boundedActive, hcut, hcut',
      syntaxGraphFOSGView, ProtocolGraph.toFOSGView, hroundActive]
  have hactions :
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActions
          left who =
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActions
          right who := by
    ext action
    simp [Machine.FOSGView.boundedAvailableActions, hcut, hcut',
      syntaxGraphFOSGView, ProtocolGraph.toFOSGView, hroundAvailable]
  ext move
  cases move with
  | none =>
      change
        who ∉ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active left ↔
          who ∉ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active right
      rw [hactive]
  | some action =>
      change
        who ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active left ∧
            action ∈
              ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActions
                left who ↔
          who ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active right ∧
            action ∈
              ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActions
                right who
      rw [hactive, hactions]

/-- Bounded graph-native syntax FOSGs satisfy the legal-observability
condition required by Kuhn's theorem. -/
theorem syntaxGraphFOSGView_toBoundedFOSG_legalObservable
    (g : WFProgram P L) (horizon : Nat) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).LegalObservable := by
  intro who h h' hInfo
  let G := (syntaxGraphFOSGView g).toBoundedFOSG horizon
  have hobsLen :
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h.playerView who)).length =
        h.steps.length := by
    simpa [G] using
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_history_playerView_observationEvents_length
          horizon h who
  have hobsLen' :
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h'.playerView who)).length =
        h'.steps.length := by
    simpa [G] using
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_history_playerView_observationEvents_length
          horizon h' who
  have hlenEq : h.steps.length = h'.steps.length := by
    have hlen :=
      congrArg
        (fun s =>
          (GameTheory.FOSG.InfoState.observationEvents
            (G := G) (i := who) s).length)
        hInfo
    change
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h.playerView who)).length =
        (GameTheory.FOSG.InfoState.observationEvents
          (G := G) (i := who) (h'.playerView who)).length at hlen
    rw [hobsLen, hobsLen'] at hlen
    exact hlen
  by_cases hnil : h.steps = []
  · have hnil' : h'.steps = [] := by
      have hlen0 : h'.steps.length = 0 := by
        rw [← hlenEq, hnil]
        rfl
      exact List.eq_nil_of_length_eq_zero hlen0
    have hh : h = GameTheory.FOSG.History.nil G := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    have hh' : h' = GameTheory.FOSG.History.nil G := by
      cases h' with
      | mk steps chain =>
          cases hnil'
          rfl
    subst hh
    subst hh'
    rfl
  · have hnil' : h'.steps ≠ [] := by
      intro hnil'
      have hlen0 : h.steps.length = 0 := by
        rw [hlenEq, hnil']
        rfl
      exact hnil (List.eq_nil_of_length_eq_zero hlen0)
    have hdepthLen :=
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_history_depth horizon h
    have hdepthLen' :=
      (syntaxGraphFOSGView g)
        |>.toBoundedFOSG_history_depth horizon h'
    have hcutEq :
        (horizon ≤ h.lastState.depth) ↔
          (horizon ≤ h'.lastState.depth) := by
      have heqDepth :
          h.lastState.depth = h'.lastState.depth := by
        calc
          h.lastState.depth = h.steps.length := hdepthLen
          _ = h'.steps.length := hlenEq
          _ = h'.lastState.depth := hdepthLen'.symm
      constructor
      · intro hle
        exact heqDepth ▸ hle
      · intro hle
        exact heqDepth.symm ▸ hle
    by_cases hcut : horizon ≤ h.lastState.depth
    · have hcut' : horizon ≤ h'.lastState.depth :=
        hcutEq.mp hcut
      have hInactive : who ∉ G.active h.lastState := by
        simp [G, Machine.FOSGView.boundedActive, hcut]
      have hInactive' : who ∉ G.active h'.lastState := by
        simp [G, Machine.FOSGView.boundedActive, hcut']
      rw [G.availableMoves_eq_singleton_none_of_not_mem_active h hInactive,
        G.availableMoves_eq_singleton_none_of_not_mem_active h' hInactive']
    · have hcut' :
          ¬ horizon ≤ h'.lastState.depth := by
        intro hle
        exact hcut (hcutEq.mpr hle)
      have hlatest :=
        congrArg
          (GameTheory.FOSG.InfoState.latestObservation?
            (G := G) (i := who))
          hInfo
      have hlatest₁ :
          GameTheory.FOSG.InfoState.latestObservation?
              (G := G) (i := who) (h.playerView who) =
            some
              (syntaxGraphObserve g who h.lastState.state,
                syntaxGraphPublicView g h.lastState.state) := by
        simpa [G, syntaxGraphMachine, ProtocolGraph.toMachine,
          syntaxGraphMachineInterface] using
          (syntaxGraphFOSGView g)
            |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
              horizon who h hnil
      have hlatest₂ :
          GameTheory.FOSG.InfoState.latestObservation?
              (G := G) (i := who) (h'.playerView who) =
            some
              (syntaxGraphObserve g who h'.lastState.state,
                syntaxGraphPublicView g h'.lastState.state) := by
        simpa [G, syntaxGraphMachine, ProtocolGraph.toMachine,
          syntaxGraphMachineInterface] using
          (syntaxGraphFOSGView g)
            |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
              horizon who h' hnil'
      rw [hlatest₁, hlatest₂] at hlatest
      injection hlatest with hobs
      have hpriv :
          syntaxGraphObserve g who h.lastState.state =
            syntaxGraphObserve g who h'.lastState.state :=
        congrArg Prod.fst hobs
      have hpub :
          syntaxGraphPublicView g h.lastState.state =
            syntaxGraphPublicView g h'.lastState.state :=
        congrArg Prod.snd hobs
      simpa [GameTheory.FOSG.availableMoves] using
        syntaxGraph_boundedAvailableMovesAtState_eq_of_observation_eq
          g horizon who hcut hcut' hpriv hpub

/-- Finite state helper for the graph-native syntax machine. -/
@[reducible] noncomputable instance syntaxGraphMachine.instFintypeState
    (g : WFProgram P L) [FiniteDomains g] :
    Fintype (syntaxGraphMachine g).State := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  dsimp [syntaxGraphMachine, ProtocolGraph.toMachine,
    syntaxProtocolGraph, ProtocolGraph.Configuration,
    ProtocolGraph.ResultAssignment, ProtocolGraph.WriteSlice]
  infer_instance

/-- Finite action helper for the graph-native syntax machine. -/
@[reducible] noncomputable instance syntaxGraphMachine.instFintypeAction
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((syntaxGraphMachine g).Action who) := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  dsimp [syntaxGraphMachine, ProtocolGraph.toMachine,
    ProtocolGraph.PlayerAction, syntaxProtocolGraph,
    ProtocolGraph.WriteSlice]
  infer_instance

/-- Finite optional-action helper for the graph-native syntax machine. -/
@[reducible] noncomputable instance syntaxGraphMachine.instFintypeOptionAction
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype (Option ((syntaxGraphMachine g).Action who)) := by
  classical
  letI : Fintype ((syntaxGraphMachine g).Action who) :=
    syntaxGraphMachine.instFintypeAction g who
  infer_instance

/-- Finite FOSG round-action helper for the graph-native syntax FOSG view. -/
@[reducible] noncomputable instance syntaxGraphFOSGView.instFintypeAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((syntaxGraphFOSGView g).Act who) := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  haveI : Fintype (syntaxProtocolGraph g).Node := by
    change Fintype (ProgramNode g.prog)
    exact ProgramNode.instFintype g.prog
  haveI : Fintype (syntaxProtocolGraph g).Field := by
    change Fintype (ProgramField g.prog)
    exact ProgramField.instFintype g.prog
  haveI :
      ∀ field : (syntaxProtocolGraph g).Field,
        Fintype (L.Val ((syntaxProtocolGraph g).fieldTy field)) := by
    intro field
    change Fintype (L.Val field.ty)
    exact ProgramField.instFintypeValue g field
  change Fintype (ProtocolGraph.PlayerRoundAction (syntaxProtocolGraph g) who)
  exact ProtocolGraph.PlayerRoundAction.instFintype (syntaxProtocolGraph g) who

/-- Finite optional FOSG round-action helper for graph-native syntax views. -/
@[reducible] noncomputable instance syntaxGraphFOSGView.instFintypeOptionAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype (Option ((syntaxGraphFOSGView g).Act who)) := by
  classical
  letI : Fintype ((syntaxGraphFOSGView g).Act who) :=
    syntaxGraphFOSGView.instFintypeAct g who
  infer_instance

/-- Finite internal-event helper for the graph-native syntax machine. -/
@[reducible] noncomputable instance syntaxGraphMachine.instFintypeInternal
    (g : WFProgram P L) :
    Fintype (syntaxGraphMachine g).Internal := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  dsimp [syntaxGraphMachine, ProtocolGraph.toMachine,
    ProtocolGraph.InternalEvent, syntaxProtocolGraph]
  infer_instance

/-- Finite primitive-event helper for the graph-native syntax machine. -/
@[reducible] noncomputable instance syntaxGraphMachine.instFintypeEvent
    (g : WFProgram P L) [FiniteDomains g] [Fintype P] :
    Fintype (syntaxGraphMachine g).Event := by
  classical
  letI : ∀ who : P, Fintype ((syntaxGraphMachine g).Action who) :=
    fun who => syntaxGraphMachine.instFintypeAction g who
  letI : Fintype (syntaxGraphMachine g).Internal :=
    syntaxGraphMachine.instFintypeInternal g
  let playEvents : Finset (syntaxGraphMachine g).Event :=
    (Finset.univ :
      Finset (Sigma fun who : P => (syntaxGraphMachine g).Action who)).image
        (fun x => Machine.Event.play x.1 x.2)
  let internalEvents : Finset (syntaxGraphMachine g).Event :=
    (Finset.univ : Finset (syntaxGraphMachine g).Internal).image
      (fun event => Machine.Event.internal event)
  refine Fintype.mk (playEvents ∪ internalEvents) ?_
  intro event
  cases event with
  | play who action =>
      exact Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_image.mpr
            ⟨⟨who, action⟩, Finset.mem_univ _, rfl⟩))
  | internal event =>
      exact Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_image.mpr
            ⟨event, Finset.mem_univ _, rfl⟩))

/-- Finite-history helper for bounded graph-native syntax FOSG views. -/
@[reducible] noncomputable instance syntaxGraphFOSGView.instFintypeBoundedHistory
    (g : WFProgram P L) (horizon : Nat)
    [Fintype P] [FiniteDomains g] :
    Fintype (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History) := by
  classical
  haveI :
      Fintype ((syntaxGraphMachine g).BoundedState horizon) :=
    Machine.BoundedState.instFintype
  haveI :
      ∀ who : P, Fintype (Option ((syntaxGraphFOSGView g).Act who)) :=
    fun who => syntaxGraphFOSGView.instFintypeOptionAct g who
  exact GameTheory.FOSG.historyFintypeOfBoundedHorizon
    (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
    ((syntaxGraphFOSGView g).toBoundedFOSG_boundedHorizon horizon)

/-- Terminal decidability for bounded graph-native syntax FOSG views. -/
noncomputable instance syntaxGraphFOSGView.instDecidablePredBoundedTerminal
    (g : WFProgram P L) (horizon : Nat) :
    DecidablePred (((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal) :=
  Classical.decPred _

/-- History-dependent blocked primitive trace distribution induced by a
bounded syntax-graph FOSG behavioral profile. -/
noncomputable def syntaxGraphFOSGBlockTraceDistFrom
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon)) :
    Nat →
      (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History) →
        PMF (List (List (syntaxGraphMachine g).Event) ×
          (syntaxGraphMachine g).State) := by
  letI :
      ∀ player,
        Fintype
          (Option
            (((syntaxProtocolGraph g).toFOSGView
              (syntaxGraphMachineInterface g)
              (syntaxProtocolGraph_hasStableFrontierRounds g)).Act
                player)) := by
    intro player
    simpa [syntaxGraphFOSGView] using
      (syntaxGraphFOSGView.instFintypeOptionAct g player)
  simpa [syntaxGraphMachine, syntaxGraphFOSGView] using
    (ProtocolGraph.boundedFOSGBlockTraceDistFrom
      (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
      (syntaxProtocolGraph_hasStableFrontierRounds g) horizon σ)

/-- Bounded syntax-graph FOSG execution, projected to extracted primitive
event blocks and checkpoint state, equals the history-dependent blocked
machine trace distribution induced by the same behavioral profile. -/
theorem syntaxGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon))
    (n : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)) :
    PMF.map
        (fun h' =>
          (syntaxGraphFOSGHistoryEventBlocks g horizon h',
            h'.lastState.state))
        (GameTheory.FOSG.History.runDistFrom
          ((syntaxGraphFOSGView g).toBoundedFOSG horizon) σ n h) =
      syntaxGraphFOSGBlockTraceDistFrom g horizon σ n h := by
  letI :
      ∀ player,
        Fintype
          (Option
            (((syntaxProtocolGraph g).toFOSGView
              (syntaxGraphMachineInterface g)
              (syntaxProtocolGraph_hasStableFrontierRounds g)).Act
                player)) := by
    intro player
    simpa [syntaxGraphFOSGView] using
      (syntaxGraphFOSGView.instFintypeOptionAct g player)
  letI :
      Fintype
        (((syntaxProtocolGraph g).toMachine
          (syntaxGraphMachineInterface g)).BoundedState horizon) := by
    simpa [syntaxGraphMachine] using
      (inferInstance : Fintype ((syntaxGraphMachine g).BoundedState horizon))
  letI :
      DecidablePred
        ((((syntaxProtocolGraph g).toFOSGView
          (syntaxGraphMachineInterface g)
          (syntaxProtocolGraph_hasStableFrontierRounds g)).toBoundedFOSG
            horizon).terminal) :=
    Classical.decPred _
  simpa [syntaxGraphFOSGHistoryEventBlocks, syntaxGraphMachine,
    syntaxGraphFOSGView, syntaxGraphFOSGBlockTraceDistFrom] using
      (ProtocolGraph.boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
        (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
        (syntaxProtocolGraph_hasStableFrontierRounds g) horizon σ n h)

/-- Initial history of the bounded syntax-graph FOSG presentation. -/
noncomputable def syntaxGraphInitialHistory
    (g : WFProgram P L) (horizon : Nat) :
    (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History) :=
  GameTheory.FOSG.History.nil
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon)

/-- Project a bounded syntax-graph FOSG history to primitive event blocks and
the checkpoint machine state. -/
noncomputable def syntaxGraphHistoryTrace
    (g : WFProgram P L) (horizon : Nat)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)) :
    List (List (syntaxGraphMachine g).Event) × (syntaxGraphMachine g).State :=
  (syntaxGraphFOSGHistoryEventBlocks g horizon h, h.lastState.state)

/-- Outcome extracted from a blocked syntax-graph trace. -/
noncomputable def syntaxGraphTraceOutcome
    (g : WFProgram P L)
    (trace :
      List (List (syntaxGraphMachine g).Event) ×
        (syntaxGraphMachine g).State) :
    (syntaxGraphMachine g).Outcome :=
  (syntaxGraphMachine g).outcome trace.2

/-- Bounded behavioral outcome kernel of the syntax-graph FOSG view, computed
as the machine outcome projection of the induced blocked primitive trace
distribution. -/
theorem syntaxGraphFOSG_boundedOutcomeFromBehavioral_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (syntaxGraphFOSGView g).BoundedBehavioralProfile horizon)
    (steps : Nat) :
    (syntaxGraphFOSGView g).boundedOutcomeFromBehavioral
        horizon β steps =
      PMF.map
        (syntaxGraphTraceOutcome g)
        (syntaxGraphFOSGBlockTraceDistFrom g horizon β.extend steps
          (syntaxGraphInitialHistory g horizon)) := by
  let run :=
    GameTheory.FOSG.History.runDistFrom
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon) β.extend steps
      (syntaxGraphInitialHistory g horizon)
  calc
    (syntaxGraphFOSGView g).boundedOutcomeFromBehavioral horizon β steps =
      PMF.map
        (fun h' => (syntaxGraphMachine g).outcome h'.lastState.state)
        run := by
          rfl
    _ = PMF.map (syntaxGraphTraceOutcome g)
          (PMF.map (syntaxGraphHistoryTrace g horizon) run) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map (syntaxGraphTraceOutcome g)
        (syntaxGraphFOSGBlockTraceDistFrom g horizon β.extend steps
          (syntaxGraphInitialHistory g horizon)) := by
          have htrace :
              PMF.map (syntaxGraphHistoryTrace g horizon) run =
                syntaxGraphFOSGBlockTraceDistFrom g horizon β.extend steps
                  (syntaxGraphInitialHistory g horizon) := by
            simpa [syntaxGraphHistoryTrace, run] using
              (syntaxGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
                (g := g) (horizon := horizon) (σ := β.extend)
                (n := steps)
                (h := syntaxGraphInitialHistory g horizon))
          rw [htrace]

/-- Bounded pure outcome kernel of the syntax-graph FOSG view, computed as
the machine outcome projection of the blocked primitive trace distribution
induced by the pure profile's behavioral embedding. -/
theorem syntaxGraphFOSG_boundedOutcomeFromPure_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (π : (syntaxGraphFOSGView g).BoundedPureProfile horizon)
    (steps : Nat) :
    (syntaxGraphFOSGView g).boundedOutcomeFromPure
        horizon π steps =
      PMF.map
        (syntaxGraphTraceOutcome g)
        (syntaxGraphFOSGBlockTraceDistFrom g horizon
          (GameTheory.FOSG.legalPureToBehavioral
            ((syntaxGraphFOSGView g).toBoundedFOSG horizon) π.extend)
          steps
          (syntaxGraphInitialHistory g horizon)) := by
  let σ :=
    GameTheory.FOSG.legalPureToBehavioral
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon) π.extend
  let run :=
    GameTheory.FOSG.History.runDistFrom
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon) σ steps
      (syntaxGraphInitialHistory g horizon)
  calc
    (syntaxGraphFOSGView g).boundedOutcomeFromPure horizon π steps =
      PMF.map
        (fun h' => (syntaxGraphMachine g).outcome h'.lastState.state)
        run := by
          rfl
    _ = PMF.map (syntaxGraphTraceOutcome g)
          (PMF.map (syntaxGraphHistoryTrace g horizon) run) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map (syntaxGraphTraceOutcome g)
        (syntaxGraphFOSGBlockTraceDistFrom g horizon σ steps
          (syntaxGraphInitialHistory g horizon)) := by
          have htrace :
              PMF.map (syntaxGraphHistoryTrace g horizon) run =
                syntaxGraphFOSGBlockTraceDistFrom g horizon σ steps
                  (syntaxGraphInitialHistory g horizon) := by
            simpa [syntaxGraphHistoryTrace, run] using
              (syntaxGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
                (g := g) (horizon := horizon) (σ := σ)
                (n := steps)
                (h := syntaxGraphInitialHistory g horizon))
          rw [htrace]

end Vegas
