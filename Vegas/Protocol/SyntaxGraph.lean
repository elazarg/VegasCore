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

end Vegas
