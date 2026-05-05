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
  match field.bindTy with
  | .pub _ => none
  | .hidden who _ => some who

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

/-- Current-context fields embedded into a program's final field set. -/
noncomputable def currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) : Finset (ProgramField p) := by
  classical
  exact ((VCtxField.enumerate Γ).map (fun field => ofCurrent p field)).toFinset

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
  classical
  unfold currentFields at h ⊢
  simp [VCtxField.enumerate, ofCurrent] at h ⊢
  rcases h with hhead | htail
  · right
    subst field
    simp [writtenBy]
  · left
    exact htail

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
  classical
  unfold currentFields at h ⊢
  simp [VCtxField.enumerate, ofCurrent] at h ⊢
  rcases h with hhead | htail
  · right
    subst field
    simp [writtenBy]
  · left
    exact htail

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
  classical
  unfold currentFields at h ⊢
  simp [VCtxField.enumerate, ofCurrent] at h ⊢
  rcases h with hhead | htail
  · right
    subst field
    simp [writtenBy]
  · left
    exact htail

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
  classical
  unfold currentFields at h ⊢
  simp [VCtxField.enumerate, ofCurrent] at h ⊢
  rcases h with hhead | htail
  · right
    subst field
    simp [writtenBy]
  · left
    exact htail

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
        FDist.totalWeight (L.evalDist D (VEnv.eraseSampleEnv env)) = 1) :
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
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (field : ProgramField p) (hty : field.ty = b)
    (hlegal :
      ∀ env : Env L.Val (eraseVCtx Γ),
        ∃ a : L.Val b,
          evalGuard (Player := P) (L := L) R a env = true) :
    ProtocolGraph.GraphGuard L (ProgramField p)
      (fun field => field.ty) field where
  reads := currentFields p
  eval := fun value ρ =>
    evalGuard (Player := P) (L := L) R
      (cast (by rw [hty]) value)
      (VEnv.eraseEnv (currentReadEnvToVEnv p ρ))
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
  classical
  exact
    if h :
        ∃ node slice stored,
          result node = some slice ∧ slice field = some stored then
      let stored := Classical.choose (Classical.choose_spec
        (Classical.choose_spec h))
      some stored.raw
    else
      initialValue? p env field

theorem value?_isSome_of_result_slice
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p} {node : ProgramNode p} {slice : WriteSlice p}
    {stored : ProtocolGraph.StoredValue (L.Val field.ty)}
    (hresult : result node = some slice)
    (hslice : slice field = some stored) :
    (value? env result field).isSome := by
  classical
  unfold value?
  rw [dif_pos]
  · simp
  · exact ⟨node, slice, stored, hresult, hslice⟩

theorem value?_isSome_of_initialValue?
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p}
    (hinitial : (initialValue? p env field).isSome) :
    (value? env result field).isSome := by
  classical
  unfold value?
  by_cases h :
      ∃ node slice stored,
        result node = some slice ∧ slice field = some stored
  · rw [dif_pos h]
    simp
  · rw [dif_neg h]
    exact hinitial

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

namespace Wrap

noncomputable def letReadEnv
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {reads : Finset (ProgramField k)}
    (ρ : ProtocolGraph.ReadEnv L (ProgramField (.letExpr x e k))
      (fun field => field.ty) (reads.image ProgramField.letTail)) :
    ProtocolGraph.ReadEnv L (ProgramField k)
      (fun field => field.ty) reads where
  value field hmem :=
    ρ.value (.letTail field)
      (Finset.mem_image.mpr ⟨field, hmem, rfl⟩)

noncomputable def sampleReadEnv
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {reads : Finset (ProgramField k)}
    (ρ : ProtocolGraph.ReadEnv L (ProgramField (.sample x D k))
      (fun field => field.ty) (reads.image ProgramField.sampleTail)) :
    ProtocolGraph.ReadEnv L (ProgramField k)
      (fun field => field.ty) reads where
  value field hmem :=
    ρ.value (.sampleTail field)
      (Finset.mem_image.mpr ⟨field, hmem, rfl⟩)

noncomputable def commitReadEnv
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {reads : Finset (ProgramField k)}
    (ρ : ProtocolGraph.ReadEnv L (ProgramField (.commit x who R k))
      (fun field => field.ty) (reads.image ProgramField.commitTail)) :
    ProtocolGraph.ReadEnv L (ProgramField k)
      (fun field => field.ty) reads where
  value field hmem :=
    ρ.value (.commitTail field)
      (Finset.mem_image.mpr ⟨field, hmem, rfl⟩)

noncomputable def revealReadEnv
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    {reads : Finset (ProgramField k)}
    (ρ : ProtocolGraph.ReadEnv L (ProgramField (.reveal y who x hx k))
      (fun field => field.ty) (reads.image ProgramField.revealTail)) :
    ProtocolGraph.ReadEnv L (ProgramField k)
      (fun field => field.ty) reads where
  value field hmem :=
    ρ.value (.revealTail field)
      (Finset.mem_image.mpr ⟨field, hmem, rfl⟩)

noncomputable def letExpr
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} {ty : L.Ty}
    (expr : ProtocolGraph.GraphExpr L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphExpr L (ProgramField (.letExpr x e k))
      (fun field => field.ty) ty where
  reads := expr.reads.image ProgramField.letTail
  eval := fun ρ => expr.eval (letReadEnv ρ)

noncomputable def sampleExpr
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} {ty : L.Ty}
    (expr : ProtocolGraph.GraphExpr L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphExpr L (ProgramField (.sample x D k))
      (fun field => field.ty) ty where
  reads := expr.reads.image ProgramField.sampleTail
  eval := fun ρ => expr.eval (sampleReadEnv ρ)

noncomputable def commitExpr
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} {ty : L.Ty}
    (expr : ProtocolGraph.GraphExpr L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphExpr L (ProgramField (.commit x who R k))
      (fun field => field.ty) ty where
  reads := expr.reads.image ProgramField.commitTail
  eval := fun ρ => expr.eval (commitReadEnv ρ)

noncomputable def revealExpr
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} {ty : L.Ty}
    (expr : ProtocolGraph.GraphExpr L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphExpr L (ProgramField (.reveal y who x hx k))
      (fun field => field.ty) ty where
  reads := expr.reads.image ProgramField.revealTail
  eval := fun ρ => expr.eval (revealReadEnv ρ)

noncomputable def letDist
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} {ty : L.Ty}
    (dist : ProtocolGraph.GraphDist L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphDist L (ProgramField (.letExpr x e k))
      (fun field => field.ty) ty where
  reads := dist.reads.image ProgramField.letTail
  eval := fun ρ => dist.eval (letReadEnv ρ)

noncomputable def sampleDist
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} {ty : L.Ty}
    (dist : ProtocolGraph.GraphDist L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphDist L (ProgramField (.sample x D k))
      (fun field => field.ty) ty where
  reads := dist.reads.image ProgramField.sampleTail
  eval := fun ρ => dist.eval (sampleReadEnv ρ)

noncomputable def commitDist
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} {ty : L.Ty}
    (dist : ProtocolGraph.GraphDist L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphDist L (ProgramField (.commit x who R k))
      (fun field => field.ty) ty where
  reads := dist.reads.image ProgramField.commitTail
  eval := fun ρ => dist.eval (commitReadEnv ρ)

noncomputable def revealDist
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} {ty : L.Ty}
    (dist : ProtocolGraph.GraphDist L (ProgramField k)
      (fun field => field.ty) ty) :
    ProtocolGraph.GraphDist L (ProgramField (.reveal y who x hx k))
      (fun field => field.ty) ty where
  reads := dist.reads.image ProgramField.revealTail
  eval := fun ρ => dist.eval (revealReadEnv ρ)

noncomputable def letGuard
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {field : ProgramField k}
    (guard : ProtocolGraph.GraphGuard L (ProgramField k)
      (fun field => field.ty) field) :
    ProtocolGraph.GraphGuard L (ProgramField (.letExpr x e k))
      (fun field => field.ty) (.letTail field) where
  reads := guard.reads.image ProgramField.letTail
  eval := fun value ρ => guard.eval value (letReadEnv ρ)
  satisfiable := fun ρ => guard.satisfiable (letReadEnv ρ)

noncomputable def sampleGuard
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {field : ProgramField k}
    (guard : ProtocolGraph.GraphGuard L (ProgramField k)
      (fun field => field.ty) field) :
    ProtocolGraph.GraphGuard L (ProgramField (.sample x D k))
      (fun field => field.ty) (.sampleTail field) where
  reads := guard.reads.image ProgramField.sampleTail
  eval := fun value ρ => guard.eval value (sampleReadEnv ρ)
  satisfiable := fun ρ => guard.satisfiable (sampleReadEnv ρ)

noncomputable def commitGuard
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {field : ProgramField k}
    (guard : ProtocolGraph.GraphGuard L (ProgramField k)
      (fun field => field.ty) field) :
    ProtocolGraph.GraphGuard L (ProgramField (.commit x who R k))
      (fun field => field.ty) (.commitTail field) where
  reads := guard.reads.image ProgramField.commitTail
  eval := fun value ρ => guard.eval value (commitReadEnv ρ)
  satisfiable := fun ρ => guard.satisfiable (commitReadEnv ρ)

noncomputable def revealGuard
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    {field : ProgramField k}
    (guard : ProtocolGraph.GraphGuard L (ProgramField k)
      (fun field => field.ty) field) :
    ProtocolGraph.GraphGuard L (ProgramField (.reveal y who x hx k))
      (fun field => field.ty) (.revealTail field) where
  reads := guard.reads.image ProgramField.revealTail
  eval := fun value ρ => guard.eval value (revealReadEnv ρ)
  satisfiable := fun ρ => guard.satisfiable (revealReadEnv ρ)

noncomputable def letNodeSem
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    ProtocolGraph.NodeSem P (ProgramField k) L (fun field => field.ty) →
      ProtocolGraph.NodeSem P (ProgramField (.letExpr x e k)) L
        (fun field => field.ty)
  | .assign field expr => .assign (.letTail field) (letExpr expr)
  | .sample field dist => .sample (.letTail field) (letDist dist)
  | .commit who field guard => .commit who (.letTail field) (letGuard guard)
  | .reveal source target hty => .reveal (.letTail source) (.letTail target) hty

noncomputable def sampleNodeSem
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    ProtocolGraph.NodeSem P (ProgramField k) L (fun field => field.ty) →
      ProtocolGraph.NodeSem P (ProgramField (.sample x D k)) L
        (fun field => field.ty)
  | .assign field expr => .assign (.sampleTail field) (sampleExpr expr)
  | .sample field dist => .sample (.sampleTail field) (sampleDist dist)
  | .commit who field guard => .commit who (.sampleTail field) (sampleGuard guard)
  | .reveal source target hty => .reveal (.sampleTail source) (.sampleTail target) hty

noncomputable def commitNodeSem
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
    ProtocolGraph.NodeSem P (ProgramField k) L (fun field => field.ty) →
      ProtocolGraph.NodeSem P (ProgramField (.commit x who R k)) L
        (fun field => field.ty)
  | .assign field expr => .assign (.commitTail field) (commitExpr expr)
  | .sample field dist => .sample (.commitTail field) (commitDist dist)
  | .commit owner field guard => .commit owner (.commitTail field) (commitGuard guard)
  | .reveal source target hty => .reveal (.commitTail source) (.commitTail target) hty

noncomputable def revealNodeSem
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} :
    ProtocolGraph.NodeSem P (ProgramField k) L (fun field => field.ty) →
      ProtocolGraph.NodeSem P (ProgramField (.reveal y who x hx k)) L
        (fun field => field.ty)
  | .assign field expr => .assign (.revealTail field) (revealExpr expr)
  | .sample field dist => .sample (.revealTail field) (revealDist dist)
  | .commit owner field guard => .commit owner (.revealTail field) (revealGuard guard)
  | .reveal source target hty => .reveal (.revealTail source) (.revealTail target) hty

theorem mem_reads_letNodeSem
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField (.letExpr x e k)}
    (h : field ∈ (letNodeSem sem).reads) :
    ∃ inner, field = .letTail inner ∧ inner ∈ sem.reads := by
  cases sem with
  | assign target expr =>
      simp [letNodeSem, letExpr, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | sample target dist =>
      simp [letNodeSem, letDist, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | commit who target guard =>
      simp [letNodeSem, letGuard, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | reveal source target hty =>
      simp [letNodeSem, ProtocolGraph.NodeSem.reads] at h
      exact ⟨source, h, by simp [ProtocolGraph.NodeSem.reads]⟩

theorem mem_reads_sampleNodeSem
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField (.sample x D k)}
    (h : field ∈ (sampleNodeSem sem).reads) :
    ∃ inner, field = .sampleTail inner ∧ inner ∈ sem.reads := by
  cases sem with
  | assign target expr =>
      simp [sampleNodeSem, sampleExpr, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | sample target dist =>
      simp [sampleNodeSem, sampleDist, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | commit who target guard =>
      simp [sampleNodeSem, sampleGuard, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | reveal source target hty =>
      simp [sampleNodeSem, ProtocolGraph.NodeSem.reads] at h
      exact ⟨source, h, by simp [ProtocolGraph.NodeSem.reads]⟩

theorem mem_reads_commitNodeSem
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField (.commit x who R k)}
    (h : field ∈ (commitNodeSem sem).reads) :
    ∃ inner, field = .commitTail inner ∧ inner ∈ sem.reads := by
  cases sem with
  | assign target expr =>
      simp [commitNodeSem, commitExpr, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | sample target dist =>
      simp [commitNodeSem, commitDist, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | commit owner target guard =>
      simp [commitNodeSem, commitGuard, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | reveal source target hty =>
      simp [commitNodeSem, ProtocolGraph.NodeSem.reads] at h
      exact ⟨source, h, by simp [ProtocolGraph.NodeSem.reads]⟩

theorem mem_reads_revealNodeSem
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField (.reveal y who x hx k)}
    (h : field ∈ (revealNodeSem sem).reads) :
    ∃ inner, field = .revealTail inner ∧ inner ∈ sem.reads := by
  cases sem with
  | assign target expr =>
      simp [revealNodeSem, revealExpr, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | sample target dist =>
      simp [revealNodeSem, revealDist, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | commit owner target guard =>
      simp [revealNodeSem, revealGuard, ProtocolGraph.NodeSem.reads] at h
      rcases h with ⟨inner, hinner, hfield⟩
      exact ⟨inner, hfield.symm, hinner⟩
  | reveal source target hty =>
      simp [revealNodeSem, ProtocolGraph.NodeSem.reads] at h
      exact ⟨source, h, by simp [ProtocolGraph.NodeSem.reads]⟩

theorem letTail_mem_writeFields_of_mem
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField k}
    (h : field ∈ sem.writeFields) :
    ProgramField.letTail (e := e) field ∈
      (letNodeSem (e := e) sem).writeFields := by
  cases sem <;>
    simp [letNodeSem, ProtocolGraph.NodeSem.writeFields,
      ProtocolGraph.NodeSem.writes] at h ⊢
  · exact congrArg ProgramField.letTail h
  · exact congrArg ProgramField.letTail h
  · exact congrArg ProgramField.letTail h
  · exact congrArg ProgramField.letTail h

theorem sampleTail_mem_writeFields_of_mem
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField k}
    (h : field ∈ sem.writeFields) :
    ProgramField.sampleTail (D := D) field ∈
      (sampleNodeSem (D := D) sem).writeFields := by
  cases sem <;>
    simp [sampleNodeSem, ProtocolGraph.NodeSem.writeFields,
      ProtocolGraph.NodeSem.writes] at h ⊢
  · exact congrArg ProgramField.sampleTail h
  · exact congrArg ProgramField.sampleTail h
  · exact congrArg ProgramField.sampleTail h
  · exact congrArg ProgramField.sampleTail h

theorem commitTail_mem_writeFields_of_mem
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField k}
    (h : field ∈ sem.writeFields) :
    ProgramField.commitTail (R := R) field ∈
      (commitNodeSem (R := R) sem).writeFields := by
  cases sem <;>
    simp [commitNodeSem, ProtocolGraph.NodeSem.writeFields,
      ProtocolGraph.NodeSem.writes] at h ⊢
  · exact congrArg ProgramField.commitTail h
  · exact congrArg ProgramField.commitTail h
  · exact congrArg ProgramField.commitTail h
  · exact congrArg ProgramField.commitTail h

theorem revealTail_mem_writeFields_of_mem
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    {sem : ProtocolGraph.NodeSem P (ProgramField k) L
      (fun field => field.ty)}
    {field : ProgramField k}
    (h : field ∈ sem.writeFields) :
    ProgramField.revealTail (x := x) (hx := hx) field ∈
      (revealNodeSem (x := x) (hx := hx) sem).writeFields := by
  cases sem <;>
    simp [revealNodeSem, ProtocolGraph.NodeSem.writeFields,
      ProtocolGraph.NodeSem.writes] at h ⊢
  · exact congrArg ProgramField.revealTail h
  · exact congrArg ProgramField.revealTail h
  · exact congrArg ProgramField.revealTail h
  · exact congrArg ProgramField.revealTail h

end Wrap

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

/-- Conservative source-order prerequisites. This is graph-native state
without cursors: the dependency relation is a static relation on source
occurrences, not a runtime program point. -/
noncomputable def prereqs
    {Γ : VCtx P L} (p : VegasCore P L Γ) (node : ProgramNode p) :
    Finset (ProgramNode p) := by
  classical
  exact (finset p).filter fun prior => prior.rank < node.rank

/-- Semantic payload of a source occurrence, expressed over the final field set
of the enclosing program. -/
noncomputable def sem :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      Legal p → NormalizedDists p → ProgramNode p →
      ProtocolGraph.NodeSem P (ProgramField p) L
        (fun field => field.ty)
  | _, .letExpr x (b := b) e k, _legal, normalized, .letHere =>
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
  | _, .letExpr _ _ _, legal, normalized, .letTail node =>
      ProgramField.Wrap.letNodeSem (sem legal normalized node)
  | _, .sample x (b := b) D k, _legal, normalized, .sampleHere =>
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
  | _, .sample _ _ _, legal, normalized, .sampleTail node =>
      ProgramField.Wrap.sampleNodeSem (sem legal normalized.2 node)
  | _, .commit x who (b := b) R k, legal, normalized, .commitHere =>
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
          target htarget legal.1)
  | _, .commit _ _ _ _, legal, normalized, .commitTail node =>
      ProgramField.Wrap.commitNodeSem (sem legal.2 normalized node)
  | _, .reveal y who x (b := b) hx k, _legal, normalized, .revealHere =>
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
  | _, .reveal _ _ _ _ _, legal, normalized, .revealTail node =>
      ProgramField.Wrap.revealNodeSem (sem legal normalized node)

/-- Every source node semantically writes its syntactic result field. -/
theorem writtenBy_mem_writeFields :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (legal : Legal p) → (normalized : NormalizedDists p) →
      (node : ProgramNode p) →
        ProgramField.writtenBy node ∈
          (ProgramNode.sem legal normalized node).writeFields
  | _, .letExpr x e k, legal, normalized, .letHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .letExpr _ _ k, legal, normalized, .letTail node => by
      exact ProgramField.Wrap.letTail_mem_writeFields_of_mem
        (writtenBy_mem_writeFields (p := k) legal normalized node)
  | _, .sample x D k, legal, normalized, .sampleHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .sample _ _ k, legal, normalized, .sampleTail node => by
      exact ProgramField.Wrap.sampleTail_mem_writeFields_of_mem
        (writtenBy_mem_writeFields (p := k) legal normalized.2 node)
  | _, .commit x who R k, legal, normalized, .commitHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .commit _ _ _ k, legal, normalized, .commitTail node => by
      exact ProgramField.Wrap.commitTail_mem_writeFields_of_mem
        (writtenBy_mem_writeFields (p := k) legal.2 normalized node)
  | _, .reveal y who x hx k, legal, normalized, .revealHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        ProtocolGraph.NodeSem.writeFields, ProtocolGraph.NodeSem.writes,
        ProtocolGraph.FieldWrite.field]
  | _, .reveal _ _ _ _ k, legal, normalized, .revealTail node => by
      exact ProgramField.Wrap.revealTail_mem_writeFields_of_mem
        (writtenBy_mem_writeFields (p := k) legal normalized node)

/-- Source reads are causally available: a node reads either an initial current
field of the enclosing program or a field written by an earlier source node. -/
theorem read_current_or_prior_write :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (legal : Legal p) → (normalized : NormalizedDists p) →
      (node : ProgramNode p) → {field : ProgramField p} →
      field ∈ (ProgramNode.sem legal normalized node).reads →
        field ∈ ProgramField.currentFields p ∨
          ∃ prior : ProgramNode p,
            prior.rank < node.rank ∧
              field ∈
                (ProgramNode.sem legal normalized prior).writeFields
  | _, .letExpr x e k, legal, normalized, .letHere, field, hread => by
      left
      simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads,
        ProgramField.castGraphExpr, ProgramField.publicGraphExpr] using hread
  | _, .letExpr x e k, legal, normalized, .letTail node, field, hread => by
      rcases ProgramField.Wrap.mem_reads_letNodeSem hread with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) legal normalized node hinner
      rcases hrec with hcurrent | hprior
      ·
          cases ProgramField.letTail_currentFields_or_eq_writtenBy_letHere
              (e := e) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.letHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields legal normalized
                  (.letHere (x := x) (e := e) (k := k)))
      ·
          rcases hprior with ⟨prior, hrank, hwrite⟩
          right
          refine ⟨.letTail prior, Nat.succ_lt_succ hrank, ?_⟩
          exact ProgramField.Wrap.letTail_mem_writeFields_of_mem hwrite
  | _, .sample x D k, legal, normalized, .sampleHere, field, hread => by
      left
      simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads,
        ProgramField.castGraphDist, ProgramField.publicGraphDist] using hread
  | _, .sample x D k, legal, normalized, .sampleTail node, field, hread => by
      rcases ProgramField.Wrap.mem_reads_sampleNodeSem hread with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) legal normalized.2 node hinner
      rcases hrec with hcurrent | hprior
      ·
          cases ProgramField.sampleTail_currentFields_or_eq_writtenBy_sampleHere
              (D := D) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.sampleHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields legal normalized
                  (.sampleHere (x := x) (D := D) (k := k)))
      ·
          rcases hprior with ⟨prior, hrank, hwrite⟩
          right
          refine ⟨.sampleTail prior, Nat.succ_lt_succ hrank, ?_⟩
          exact ProgramField.Wrap.sampleTail_mem_writeFields_of_mem hwrite
  | _, .commit x who R k, legal, normalized, .commitHere, field, hread => by
      left
      simpa [ProgramNode.sem, ProtocolGraph.NodeSem.reads,
        ProgramField.commitGraphGuard] using hread
  | _, .commit x who R k, legal, normalized, .commitTail node, field, hread => by
      rcases ProgramField.Wrap.mem_reads_commitNodeSem hread with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) legal.2 normalized node hinner
      rcases hrec with hcurrent | hprior
      ·
          cases ProgramField.commitTail_currentFields_or_eq_writtenBy_commitHere
              (R := R) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.commitHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields legal normalized
                  (.commitHere (x := x) (who := who) (R := R) (k := k)))
      ·
          rcases hprior with ⟨prior, hrank, hwrite⟩
          right
          refine ⟨.commitTail prior, Nat.succ_lt_succ hrank, ?_⟩
          exact ProgramField.Wrap.commitTail_mem_writeFields_of_mem hwrite
  | _, .reveal y who x hx k, legal, normalized, .revealHere, field, hread => by
      left
      simp [ProgramNode.sem, ProtocolGraph.NodeSem.reads] at hread
      subst field
      exact ProgramField.ofCurrent_mem_currentFields
        (.reveal y who x hx k) (.mk hx)
  | _, .reveal y who x hx k, legal, normalized, .revealTail node, field, hread => by
      rcases ProgramField.Wrap.mem_reads_revealNodeSem hread with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) legal normalized node hinner
      rcases hrec with hcurrent | hprior
      ·
          cases ProgramField.revealTail_currentFields_or_eq_writtenBy_revealHere
              (x := x) (hx := hx) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.revealHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields legal normalized
                  (.revealHere (y := y) (who := who) (x := x) (hx := hx)
                    (k := k)))
      ·
          rcases hprior with ⟨prior, hrank, hwrite⟩
          right
          refine ⟨.revealTail prior, Nat.succ_lt_succ hrank, ?_⟩
          exact ProgramField.Wrap.revealTail_mem_writeFields_of_mem hwrite

/-- A source graph slice is well-formed for a node when it has the storage
shape prescribed by the node semantics. Dynamic guard checks are handled by
`actionLegal`. -/
noncomputable def sliceLegal
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (legal : Legal p) (normalized : NormalizedDists p)
    (node : ProgramNode p) (slice : ProgramField.WriteSlice p) : Prop :=
  match sem legal normalized node with
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
    (legal : Legal p) (normalized : NormalizedDists p)
    (node : ProgramNode p) {slice : ProgramField.WriteSlice p}
    {field : ProgramField p}
    (hlegal : sliceLegal legal normalized node slice)
    (hwrite :
      field ∈
        (ProgramNode.sem legal normalized node).writeFields) :
    ∃ stored : ProtocolGraph.StoredValue (L.Val field.ty),
      slice field = some stored := by
  classical
  cases hsem : ProgramNode.sem legal normalized node with
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
    (legal : Legal p) (normalized : NormalizedDists p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p))
    (node : ProgramNode p) (slice : ProgramField.WriteSlice p) : Prop :=
  match sem legal normalized node with
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
    (legal : Legal p) (normalized : NormalizedDists p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p))
    (node : ProgramNode p) {who : P}
    (hactor : (sem legal normalized node).actor = some who)
    (hreads :
      ∀ read, read ∈ (sem legal normalized node).reads →
        (ProgramField.value? env result read).isSome) :
    ∃ slice,
      sliceLegal legal normalized node slice ∧
        actionLegal env legal normalized result node slice := by
  cases hsem : sem legal normalized node with
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

/-- A completed source node makes every field it semantically writes available
in the source-level extensional value lookup. -/
theorem value?_isSome_of_completed_write
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (legal : Legal p) (normalized : NormalizedDists p)
    {result : ProgramNode p → Option (ProgramField.WriteSlice p)}
    {writer : ProgramNode p} {field : ProgramField p}
    (hdone : (result writer).isSome)
    (hcfgLegal :
      ∀ {node slice},
        result node = some slice →
          ProgramNode.sliceLegal legal normalized node slice)
    (hwrite :
      field ∈ (ProgramNode.sem legal normalized writer).writeFields) :
    (ProgramField.value? env result field).isSome := by
  rcases Option.isSome_iff_exists.mp hdone with ⟨slice, hresult⟩
  have hsliceLegal : ProgramNode.sliceLegal legal normalized writer slice :=
    hcfgLegal hresult
  rcases ProgramNode.sliceLegal_writeField_isSome legal normalized writer
      hsliceLegal hwrite with ⟨stored, hstored⟩
  exact ProgramField.value?_isSome_of_result_slice env hresult hstored

/-- Internal kernel for source graph nodes. Assignment and reveal nodes are
deterministic; sample nodes use the checked PMF distribution; commit nodes are
not internal. -/
noncomputable def internalKernel
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (legal : Legal p) (normalized : NormalizedDists p)
    (node : ProgramNode p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p)) :
    PMF (ProgramField.WriteSlice p) := by
  classical
  exact
    match hsem : sem legal normalized node with
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

This is the new semantic object that should replace cursor/action-graph
execution. It is intentionally conservative about prerequisites for now:
source occurrence rank gives an acyclic graph without storing a runtime cursor.
The dependency relation can be narrowed later by replacing
`ProgramNode.prereqs`; the machine carrier and configuration representation do
not change. -/
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
  sem := ProgramNode.sem g.legal g.normalized
  prereqs := ProgramNode.prereqs g.prog
  rank := fun node => node.rank
  prereqs_subset_nodes := by
    intro node prereq _hnode hpre
    exact (Finset.mem_filter.mp hpre).1
  prereq_rank_lt := by
    intro node prereq _hnode hpre
    exact (Finset.mem_filter.mp hpre).2
  read_fields_mem := by
    intro node field _hnode _hfield
    exact ProgramField.mem_finset g.prog field
  write_fields_mem := by
    intro node write _hnode hwrite
    exact ProgramField.mem_finset g.prog write.field
  no_duplicate_writes := by
    intro node field left right _hnode hleft hright hleftField hrightField
    cases hsem : ProgramNode.sem g.legal g.normalized node with
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
  sliceLegal := ProgramNode.sliceLegal g.legal g.normalized
  actionLegal := ProgramNode.actionLegal g.env g.legal g.normalized
  internalKernel := ProgramNode.internalKernel g.env g.legal g.normalized

/-- Static read-availability invariant needed by the graph FOSG view: every
declared read of every frontier node has a value in the extensional graph
configuration. -/
def syntaxReadsAvailableAtFrontier
    (g : WFProgram P L) : Prop :=
  ∀ (cfg : (syntaxProtocolGraph g).Configuration) {node : ProgramNode g.prog},
    node ∈ cfg.frontier →
      ∀ read, read ∈ (ProgramNode.sem g.legal g.normalized node).reads →
        (ProgramField.value? g.env cfg.result read).isSome

/-- Source graph frontier reads are available in every configuration. -/
theorem syntaxReadsAvailableAtFrontier_of_wfProgram
    (g : WFProgram P L) :
    syntaxReadsAvailableAtFrontier g := by
  intro cfg node hfrontier read hread
  rcases ProgramNode.read_current_or_prior_write
      g.legal g.normalized node hread with hcurrent | hprior
  · exact ProgramField.value?_isSome_of_initialValue? g.env
      (ProgramField.initialValue?_isSome_of_mem_currentFields
        g.prog g.env hcurrent)
  · rcases hprior with ⟨prior, hrank, hwrite⟩
    have hpre : prior ∈ (syntaxProtocolGraph g).prereqs node := by
      change prior ∈ ProgramNode.prereqs g.prog node
      exact Finset.mem_filter.mpr
        ⟨ProgramNode.mem_finset g.prog prior, hrank⟩
    have hdone : (cfg.result prior).isSome :=
      cfg.result_some_of_prereq_of_mem_frontier hfrontier hpre
    have hcfgLegal :
        ∀ {node slice},
          cfg.result node = some slice →
            ProgramNode.sliceLegal g.legal g.normalized node slice := by
      intro node slice hresult
      simpa [syntaxProtocolGraph] using cfg.legal hresult
    exact ProgramNode.value?_isSome_of_completed_write
      g.env g.legal g.normalized hdone hcfgLegal hwrite

/-- Source graph commits cannot deadlock: the generated guard carries a
satisfying action for the available read environment. -/
theorem syntaxProtocolGraph_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (syntaxProtocolGraph g).HasAvailablePlayerActions := by
  intro cfg node who hfrontier hactor
  rcases ProgramNode.exists_actionLegal_of_reads_available
      g.env g.legal g.normalized cfg.result node
      (who := who)
      (by simpa [syntaxProtocolGraph] using hactor)
      (syntaxReadsAvailableAtFrontier_of_wfProgram g cfg hfrontier) with
    ⟨slice, hslice, haction⟩
  exact ⟨slice, hslice, haction⟩

/-- Private observation of the graph-native syntax machine: the visible part
of the extensional field assignment. -/
structure SyntaxPrivateObs (g : WFProgram P L) (who : P) where
  value? : (field : ProgramField g.prog) → Option (L.Val field.ty)

/-- Recover a field value from a graph-native syntax configuration. -/
noncomputable def syntaxGraphConfigValue?
    (g : WFProgram P L)
    (cfg : (syntaxProtocolGraph g).Configuration)
    (field : ProgramField g.prog) :
    Option (L.Val field.ty) :=
  (syntaxProtocolGraph g).value? cfg.result field

/-- Player observation for the graph-native syntax machine. -/
noncomputable def syntaxGraphObserve
    (g : WFProgram P L) (who : P)
    (cfg : (syntaxProtocolGraph g).Configuration) :
    SyntaxPrivateObs g who where
  value? := fun field =>
    if field.owner = none ∨ field.owner = some who then
      syntaxGraphConfigValue? g cfg field
    else
      none

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
  Public := PUnit
  Obs := fun who => SyntaxPrivateObs g who
  Outcome := Outcome P
  publicView := fun _ => PUnit.unit
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
    (syntaxProtocolGraph_hasAvailablePlayerActions g)

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
      Fintype ((syntaxGraphMachine g).BoundedRunPrefix horizon) :=
    Machine.BoundedRunPrefix.instFintype
  exact GameTheory.FOSG.historyFintypeOfBoundedHorizon
    (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
    ((syntaxGraphFOSGView g).toBoundedFOSG_boundedHorizon horizon)

/-- Terminal decidability for bounded graph-native syntax FOSG views. -/
noncomputable instance syntaxGraphFOSGView.instDecidablePredBoundedTerminal
    (g : WFProgram P L) (horizon : Nat) :
    DecidablePred (((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal) :=
  Classical.decPred _

end Vegas
