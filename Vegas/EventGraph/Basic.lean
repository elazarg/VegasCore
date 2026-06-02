/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Mathlib.Data.Finset.Basic
import Vegas.Foundation.Basic

/-!
# Event graphs

An event graph is the protocol-level dependency object produced by compiling a
checked Vegas program.  Nodes are protocol events, fields are typed storage
locations, and `reads` is the scheduling dependency footprint.

The graph uses canonical numeric ids.  Source syntax may guide allocation, but
source occurrences are not graph identity.
-/

namespace Vegas

namespace EventGraph

/-- A dynamically packaged language value. -/
structure TypedValue (L : IExpr) where
  ty : L.Ty
  value : L.Val ty

namespace TypedValue

variable {L : IExpr}

/-- Try to read a typed value at a requested language type. -/
noncomputable def as? (value : TypedValue L) (ty : L.Ty) :
    Option (L.Val ty) :=
  if h : value.ty = ty then
    some (cast (by rw [h]) value.value)
  else
    none

end TypedValue

/-- Runtime field store used to evaluate node-local expressions. -/
abbrev Store (L : IExpr) := Nat → Option (TypedValue L)

namespace Store

variable {L : IExpr}

/-- Read a field at an expected type. -/
noncomputable def getAs (store : Store L) (field : Nat) (ty : L.Ty) :
    Option (L.Val ty) :=
  match store field with
  | none => none
  | some value => value.as? ty

theorem getAs_cast (store : Store L) (field : Nat)
    {source target : L.Ty} (hty : source = target)
    {value : L.Val source}
    (hget : getAs store field source = some value) :
    getAs store field target =
      some (cast (congrArg L.Val hty) value) := by
  cases hty
  exact hget

end Store

/-- A graph field id together with the type expected at that field. -/
structure FieldRef (L : IExpr) where
  field : Nat
  ty : L.Ty
deriving DecidableEq

namespace FieldRef

variable {L : IExpr}

/-- Project typed field references to the numeric dependency footprint used for
scheduling. -/
def fields (refs : Finset (FieldRef L)) : Finset Nat :=
  refs.image FieldRef.field

@[simp] theorem fields_empty :
    fields (∅ : Finset (FieldRef L)) = ∅ := by
  simp [fields]

@[simp] theorem mem_fields_singleton {ref : FieldRef L} {field : Nat} :
    field ∈ fields ({ref} : Finset (FieldRef L)) ↔ field = ref.field := by
  simp [fields]

end FieldRef

/-- Restricted read environment supplied to graph-local computations.

The environment exposes typed values only for the node's declared read
footprint. Payload code has no access to the ambient graph store and cannot
ask for a field at a type not listed in its `FieldRef` footprint. -/
structure ReadEnv (L : IExpr) (reads : Finset (FieldRef L)) where
  read : (ref : FieldRef L) → ref ∈ reads → L.Val ref.ty

namespace ReadEnv

variable {L : IExpr} {refs : Finset (FieldRef L)}

@[ext] theorem ext
    {left right : ReadEnv L refs}
    (hread :
      ∀ ref (href : ref ∈ refs), left.read ref href = right.read ref href) :
    left = right := by
  cases left
  cases right
  congr
  funext ref href
  exact hread ref href

/-- Restrict a full store to a declared read footprint, given evidence that
all declared typed reads are present at the requested types. -/
noncomputable def ofStore (store : Store L) (refs : Finset (FieldRef L))
    (available :
      ∀ ref, ref ∈ refs → ∃ value, Store.getAs store ref.field ref.ty = some value) :
    ReadEnv L refs where
  read := fun ref href => Classical.choose (available ref href)

/-- Try to restrict a store to a typed read footprint. This fails exactly when
a declared read is absent or present at a different type. -/
noncomputable def ofStore? (store : Store L) (refs : Finset (FieldRef L)) :
    Option (ReadEnv L refs) := by
  classical
  exact
    if h :
        ∀ ref, ref ∈ refs →
          ∃ value, Store.getAs store ref.field ref.ty = some value then
      some (ofStore store refs h)
    else
      none

@[simp] theorem ofStore_read (store : Store L) (refs : Finset (FieldRef L))
    (available :
      ∀ ref, ref ∈ refs → ∃ value, Store.getAs store ref.field ref.ty = some value)
    {ref : FieldRef L} (href : ref ∈ refs) :
    Store.getAs store ref.field ref.ty =
      some ((ofStore store refs available).read ref href) := by
  unfold ofStore
  exact Classical.choose_spec (available ref href)

theorem ofStore?_read {store : Store L} {refs : Finset (FieldRef L)}
    {env : ReadEnv L refs}
    (henv : ofStore? store refs = some env)
    {ref : FieldRef L} (href : ref ∈ refs) :
    Store.getAs store ref.field ref.ty = some (env.read ref href) := by
  unfold ofStore? at henv
  by_cases h :
      ∀ ref, ref ∈ refs →
        ∃ value, Store.getAs store ref.field ref.ty = some value
  · rw [dif_pos h] at henv
    cases henv
    exact ofStore_read store refs h href
  · rw [dif_neg h] at henv
    cases henv

theorem ofStore_eq_of_getAs_eq
    {left right : Store L} {refs : Finset (FieldRef L)}
    (availableLeft :
      ∀ ref, ref ∈ refs →
        ∃ value, Store.getAs left ref.field ref.ty = some value)
    (availableRight :
      ∀ ref, ref ∈ refs →
        ∃ value, Store.getAs right ref.field ref.ty = some value)
    (heq :
      ∀ ref, ref ∈ refs →
        Store.getAs left ref.field ref.ty =
          Store.getAs right ref.field ref.ty) :
    ofStore left refs availableLeft =
      ofStore right refs availableRight := by
  ext ref href
  unfold ofStore
  have hleftAtRight :
      Store.getAs right ref.field ref.ty =
        some (Classical.choose (availableLeft ref href)) := by
    rw [← heq ref href]
    exact Classical.choose_spec (availableLeft ref href)
  have hright :=
    Classical.choose_spec (availableRight ref href)
  rw [hright] at hleftAtRight
  exact (Option.some.inj hleftAtRight).symm

theorem ofStore?_eq_of_getAs_eq
    {left right : Store L} {refs : Finset (FieldRef L)}
    {env : ReadEnv L refs}
    (henv : ofStore? left refs = some env)
    (heq :
      ∀ ref, ref ∈ refs →
        Store.getAs left ref.field ref.ty =
          Store.getAs right ref.field ref.ty) :
    ofStore? right refs = some env := by
  unfold ofStore? at henv ⊢
  by_cases hleft :
      ∀ ref, ref ∈ refs →
        ∃ value, Store.getAs left ref.field ref.ty = some value
  · rw [dif_pos hleft] at henv
    have hright :
        ∀ ref, ref ∈ refs →
          ∃ value, Store.getAs right ref.field ref.ty = some value := by
      intro ref href
      rcases hleft ref href with ⟨value, hvalue⟩
      exact ⟨value, by
        rw [← heq ref href]
        exact hvalue⟩
    rw [dif_pos hright]
    have hstore :
        ofStore left refs hleft = ofStore right refs hright :=
      ofStore_eq_of_getAs_eq hleft hright heq
    rw [← hstore]
    exact henv
  · rw [dif_neg hleft] at henv
    cases henv

end ReadEnv

/-- A graph-local finite probability distribution with an explicit dependency
footprint. Source distributions cross the `FWeight → PMF` normalization bridge
during compilation; executable graphs do not carry raw weights. -/
structure EventDist (L : IExpr) where
  ty : L.Ty
  reads : Finset (FieldRef L)
  eval : ReadEnv L reads → PMF (L.Val ty)

/-- A commit guard. `choiceReads` is the player-visible information footprint
available to the actor when choosing this commit. It may strictly contain the
guard expression's syntactic reads; the guard evaluator receives the full
choice view and may ignore unused fields. Scheduling and observation use this
choice footprint, not a minimal guard-expression footprint. -/
structure EventGuard (L : IExpr) where
  ty : L.Ty
  choiceReads : Finset (FieldRef L)
  eval : L.Val ty → ReadEnv L choiceReads → Bool

/-- A graph-local payoff projection. Payoff expressions are compiled to
integers immediately so executable machines do not need to recover erased
source types from an untyped list of graph expressions. -/
structure EventPayoff (L : IExpr) where
  reads : Finset (FieldRef L)
  eval : ReadEnv L reads → Int

/-- Semantic payload of one graph node. The output field is supplied by the
graph row that contains the node, so the payload cannot disagree with field
writer metadata. -/
inductive NodeSem (Player : Type) (L : IExpr) where
  | sample (dist : EventDist L)
  | commit (who : Player) (guard : EventGuard L)
  | reveal (source : Nat)

namespace NodeSem

variable {Player : Type} {L : IExpr}

/-- Fields whose values are needed before this event can run or be chosen. -/
def reads : NodeSem Player L → Finset Nat
  | .sample dist => FieldRef.fields dist.reads
  | .commit _ guard => FieldRef.fields guard.choiceReads
  | .reveal source => {source}

/-- Player who chooses at this node, if any. -/
def actor : NodeSem Player L → Option Player
  | .sample _ => none
  | .commit who _ => some who
  | .reveal _ => none

/-- Commit-node test used by dependency construction. -/
def isCommit : NodeSem Player L → Bool
  | .commit _ _ => true
  | _ => false

/-- Reveal-node test used by dependency construction. -/
def isReveal : NodeSem Player L → Bool
  | .reveal _ => true
  | _ => false

end NodeSem

/-- Origin of a field in the computed field view. This is not stored in graph
data for event fields; event field origins are derived from the node index. -/
inductive FieldSource (L : IExpr) : L.Ty → Type where
  | initial {ty : L.Ty} (value : L.Val ty) : FieldSource L ty
  | event {ty : L.Ty} (node : Nat) : FieldSource L ty

/-- Metadata for an initial graph field. -/
structure InitialField (Player : Type) (L : IExpr) where
  ty : L.Ty
  owner : Option Player
  value : L.Val ty

/-- A graph node together with the metadata of its output field. -/
structure EventNode (Player : Type) (L : IExpr) where
  ty : L.Ty
  owner : Option Player
  sem : NodeSem Player L

/-- Computed metadata for a graph field. -/
structure FieldSpec (Player : Type) (L : IExpr) where
  ty : L.Ty
  owner : Option Player
  source : FieldSource L ty

namespace FieldSpec

variable {Player : Type} {L : IExpr}

/-- Initial field value as a dynamic value. -/
def initialValue? (field : FieldSpec Player L) : Option (TypedValue L) :=
  match field.source with
  | .initial value => some { ty := field.ty, value := value }
  | .event _ => none

end FieldSpec

/-- A canonical event graph.

Initial field ids are `0 ... initialFields.length - 1`. Event field ids are
`initialFields.length + node`, so an event node owns its output field by
construction. -/
structure Graph (Player : Type) [DecidableEq Player] (L : IExpr) where
  initialFields : List (InitialField Player L)
  nodes : List (EventNode Player L)

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

def nodeCount (G : Graph Player L) : Nat :=
  G.nodes.length

def fieldCount (G : Graph Player L) : Nat :=
  G.initialFields.length + G.nodeCount

/-- Canonical graph-node order, by numeric node id. -/
def nodeOrder (G : Graph Player L) : List (Fin G.nodeCount) :=
  List.finRange G.nodeCount

@[simp] theorem mem_nodeOrder (G : Graph Player L)
    (node : Fin G.nodeCount) :
    node ∈ G.nodeOrder := by
  unfold nodeOrder
  exact List.mem_finRange node

theorem nodeOrder_nodup (G : Graph Player L) :
    G.nodeOrder.Nodup := by
  unfold nodeOrder
  exact List.nodup_finRange G.nodeCount

def node? (G : Graph Player L) (node : Nat) : Option (NodeSem Player L) :=
  match G.nodes[node]? with
  | none => none
  | some event => some event.sem

theorem nodes_get_of_fin (G : Graph Player L)
    (node : Fin G.nodeCount) :
    ∃ event, G.nodes[node]? = some event := by
  have hlt : (node : Nat) < G.nodes.length := by
    change (node : Nat) < G.nodeCount
    exact node.isLt
  refine ⟨G.nodes[(node : Nat)], ?_⟩
  change G.nodes[(node : Nat)]? = some G.nodes[(node : Nat)]
  rw [List.getElem?_eq_getElem hlt]

/-- The event row at a valid graph node. -/
def nodeRow (G : Graph Player L)
    (node : Fin G.nodeCount) : EventNode Player L :=
  G.nodes[(node : Nat)]' (by
    change (node : Nat) < G.nodeCount
    exact node.isLt)

@[simp] theorem nodes_get?_nodeRow (G : Graph Player L)
    (node : Fin G.nodeCount) :
    G.nodes[(node : Nat)]? = some (G.nodeRow node) := by
  unfold nodeRow
  rw [List.getElem?_eq_getElem]

@[simp] theorem node?_nodeRow (G : Graph Player L)
    (node : Fin G.nodeCount) :
    G.node? node = some (G.nodeRow node).sem := by
  unfold node?
  simp

/-- Package a graph-node-typed output value for the primitive machine
boundary. -/
def nodeTypedValue (G : Graph Player L)
    (node : Fin G.nodeCount)
    (value : L.Val (G.nodeRow node).ty) : TypedValue L where
  ty := (G.nodeRow node).ty
  value := value

/-- Output field id owned by a graph node. -/
def nodeTarget (G : Graph Player L) (node : Nat) : Nat :=
  G.initialFields.length + node

def field? (G : Graph Player L) (field : Nat) :
    Option (FieldSpec Player L) :=
  if _h : field < G.initialFields.length then
    match G.initialFields[field]? with
    | none => none
    | some spec =>
        some
          { ty := spec.ty
            owner := spec.owner
            source := .initial spec.value }
  else
    let node := field - G.initialFields.length
    match G.nodes[node]? with
    | none => none
    | some event =>
        some
          { ty := event.ty
            owner := event.owner
            source := .event node }

/-- The field row at a valid graph field id. -/
def fieldRow (G : Graph Player L)
    (field : Fin G.fieldCount) : FieldSpec Player L :=
  if hinit : (field : Nat) < G.initialFields.length then
    let init := G.initialFields[(field : Nat)]' hinit
    { ty := init.ty
      owner := init.owner
      source := .initial init.value }
  else
    let node : Nat := (field : Nat) - G.initialFields.length
    have hnode : node < G.nodeCount := by
      have hlt :
          (field : Nat) < G.initialFields.length + G.nodeCount := by
        have hlt' := field.isLt
        change (field : Nat) < G.initialFields.length + G.nodeCount at hlt'
        exact hlt'
      have hge : G.initialFields.length ≤ (field : Nat) :=
        Nat.le_of_not_gt hinit
      dsimp [node]
      omega
    let event := G.nodes[node]' hnode
    { ty := event.ty
      owner := event.owner
      source := .event node }

@[simp] theorem fieldRow_mk_eq_mk (G : Graph Player L)
    (field : Nat) (h₁ h₂ : field < G.fieldCount) :
    G.fieldRow (⟨field, h₁⟩ : Fin G.fieldCount) =
      G.fieldRow ⟨field, h₂⟩ := by
  have hfin :
      (⟨field, h₁⟩ : Fin G.fieldCount) = ⟨field, h₂⟩ := by
    ext
    rfl
  rw [hfin]

@[simp] theorem field?_fieldRow (G : Graph Player L)
    (field : Fin G.fieldCount) :
    G.field? (field : Nat) = some (G.fieldRow field) := by
  by_cases hinit : (field : Nat) < G.initialFields.length
  · simp [field?, fieldRow, hinit]
  · have hnode :
        (field : Nat) - G.initialFields.length < G.nodes.length := by
      have hlt : (field : Nat) < G.initialFields.length + G.nodes.length := by
        have hlt' := field.isLt
        change (field : Nat) < G.initialFields.length + G.nodes.length at hlt'
        exact hlt'
      omega
    simp [field?, fieldRow, hinit, List.getElem?_eq_getElem hnode]
    constructor <;> rfl

theorem field_lt_fieldCount_of_field?_some (G : Graph Player L)
    {field : Nat} {spec : FieldSpec Player L}
    (hfield : G.field? field = some spec) :
    field < G.fieldCount := by
  unfold field? at hfield
  by_cases hinit : field < G.initialFields.length
  · unfold fieldCount
    omega
  · simp only [hinit, ↓reduceDIte] at hfield
    let node := field - G.initialFields.length
    cases hnode : G.nodes[node]? with
    | none =>
        rw [hnode] at hfield
        cases hfield
    | some event =>
        rw [hnode] at hfield
        have hnodeLt : node < G.nodes.length :=
          (List.getElem?_eq_some_iff.mp hnode).1
        unfold fieldCount nodeCount
        dsimp [node] at hnodeLt
        omega

theorem fieldRow_eq_of_field?_some (G : Graph Player L)
    {field : Nat} {spec : FieldSpec Player L}
    (hfield : G.field? field = some spec)
    (hlt : field < G.fieldCount) :
    G.fieldRow ⟨field, hlt⟩ = spec := by
  have hrow := G.field?_fieldRow ⟨field, hlt⟩
  rw [hfield] at hrow
  exact (Option.some.inj hrow).symm

@[simp] theorem field?_nodeTarget (G : Graph Player L)
    {node : Nat} {event : EventNode Player L}
    (hget : G.nodes[node]? = some event) :
    G.field? (G.nodeTarget node) =
      some { ty := event.ty, owner := event.owner, source := .event node } := by
  unfold field? nodeTarget
  have hnot : ¬ G.initialFields.length + node < G.initialFields.length := by
    omega
  simp [hnot, hget]

theorem field_eq_nodeTarget_of_event_source (G : Graph Player L)
    {field node : Nat} {spec : FieldSpec Player L}
    (hget : G.field? field = some spec)
    (hsource : spec.source = .event node) :
    field = G.nodeTarget node := by
  unfold field? at hget
  split at hget
  · rename_i hlt
    cases hinit : G.initialFields[field]? with
    | none =>
        rw [hinit] at hget
        cases hget
    | some init =>
        rw [hinit] at hget
        cases hget
        cases hsource
  · rename_i hlt
    dsimp at hget
    cases hnode : G.nodes[field - G.initialFields.length]? with
    | none =>
        rw [hnode] at hget
        cases hget
    | some event =>
        rw [hnode] at hget
        cases hget
        cases hsource
        unfold nodeTarget
        omega

theorem node_get_of_field_event_source (G : Graph Player L)
    {field node : Nat} {spec : FieldSpec Player L}
    (hget : G.field? field = some spec)
    (hsource : spec.source = .event node) :
    ∃ event, G.nodes[node]? = some event := by
  unfold field? at hget
  split at hget
  · cases hinit : G.initialFields[field]? with
    | none =>
        rw [hinit] at hget
        cases hget
    | some init =>
        rw [hinit] at hget
        cases hget
        cases hsource
  · cases hnode : G.nodes[field - G.initialFields.length]? with
    | none =>
        dsimp at hget
        rw [hnode] at hget
        cases hget
    | some event =>
        dsimp at hget
        rw [hnode] at hget
        cases hget
        cases hsource
        exact ⟨event, hnode⟩

/-- Initial store of graph fields. -/
def initialStore (G : Graph Player L) : Store L :=
  fun field =>
    match G.field? field with
    | none => none
    | some spec => spec.initialValue?

/-- Whether a field value is available before a node runs. Initial fields are
available from the start; event-written fields are available only to later
nodes. -/
def fieldAvailableBefore (G : Graph Player L) (node field : Nat) : Bool :=
  match G.field? field with
  | none => false
  | some spec =>
      match spec.source with
      | .initial _ => true
      | .event writer => decide (writer < node)

/-- A typed field reference names a public graph field. -/
def fieldRefPublic (G : Graph Player L) (ref : FieldRef L) : Prop :=
  ∃ spec, G.field? ref.field = some spec ∧
    spec.ty = ref.ty ∧ spec.owner = none

/-- A typed field reference names a graph field visible to a player. -/
def fieldRefVisibleTo (G : Graph Player L) (who : Player)
    (ref : FieldRef L) : Prop :=
  ∃ spec, G.field? ref.field = some spec ∧
    spec.ty = ref.ty ∧ (spec.owner = none ∨ spec.owner = some who)

/-- Proof-level node well-formedness. A node may read only fields that are
available before it runs. Public internal computations read only public fields;
commit choice footprints are visible to the actor; reveal opens a hidden source
into a public event field of the same type. -/
def nodeWFAt (G : Graph Player L) (node : Nat)
    (event : EventNode Player L) : Prop :=
  (∀ field, field ∈ event.sem.reads →
    G.fieldAvailableBefore node field = true) ∧
  match event.sem with
  | .sample dist =>
      event.ty = dist.ty ∧ event.owner = none ∧
        ∀ ref, ref ∈ dist.reads → G.fieldRefPublic ref
  | .commit who guard =>
      event.ty = guard.ty ∧ event.owner = some who ∧
        ∀ ref, ref ∈ guard.choiceReads → G.fieldRefVisibleTo who ref
  | .reveal source =>
      ∃ sourceSpec, G.field? source = some sourceSpec ∧
        sourceSpec.ty = event.ty ∧ sourceSpec.owner.isSome ∧ event.owner = none

/-- Well-formed raw graph: every stored numeric id resolves, every node target
has the right type, owner, and field origin, commit choice footprints are
visible to the actor, and reveals open hidden fields into public fields. Reads
must be available before the node runs: either initial, or written by an earlier
node. Public internal computations may read only public fields; hidden-to-public
flow is represented only by reveal nodes. Event output fields are owned by their
node by construction. Prerequisites are not stored; they are derived
canonically from node payloads.
-/
def WF (G : Graph Player L) : Prop :=
  ∀ node event, G.nodes[node]? = some event → G.nodeWFAt node event

end Graph

/-- Commit guards are live when every graph commit node admits some
guard-satisfying action for every declared choice environment. -/
def GuardLive {Player : Type} [DecidableEq Player] {L : IExpr}
    (G : Graph Player L) : Prop :=
  ∀ {node : Fin G.nodeCount} {row : EventNode Player L}
    {who : Player} {guard : EventGuard L},
    G.nodes[node]? = some row →
    row.sem = .commit who guard →
    ∀ env : ReadEnv L guard.choiceReads,
      ∃ value : L.Val guard.ty, guard.eval value env = true

/-- Evaluate graph payoff entries from a graph store. Failure is explicit:
a missing payoff dependency produces `none`, not a silently truncated
outcome. -/
noncomputable def evalPayoffEntries? {Player : Type} [DecidableEq Player]
    {L : IExpr} (payoffs : List (Player × EventPayoff L)) (store : Store L) :
    Option (List (Player × Int)) :=
  match payoffs with
  | [] => some []
  | payoff :: rest => do
      let env ← ReadEnv.ofStore? store payoff.2.reads
      let value := payoff.2.eval env
      let entries ← evalPayoffEntries? rest store
      some ((payoff.1, value) :: entries)

/-- Evaluate graph payoff projections from a graph store. -/
noncomputable def evalPayoffs? {Player : Type} [DecidableEq Player]
    {L : IExpr} (payoffs : List (Player × EventPayoff L))
    (store : Store L) : Option (Outcome Player) := do
  let entries ← evalPayoffEntries? payoffs store
  some (mkOutcome entries)

theorem evalPayoffEntries?_isSome_of_available
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (payoffs : List (Player × EventPayoff L)) (store : Store L)
    (available :
      ∀ payoff, payoff ∈ payoffs →
        ∀ ref, ref ∈ payoff.2.reads →
          ∃ value, Store.getAs store ref.field ref.ty = some value) :
    ∃ entries, evalPayoffEntries? payoffs store = some entries := by
  induction payoffs with
  | nil =>
      exact ⟨[], rfl⟩
  | cons payoff rest ih =>
      have headAvailable :
          ∀ ref, ref ∈ payoff.2.reads →
            ∃ value, Store.getAs store ref.field ref.ty = some value := by
        intro ref href
        exact available payoff (by simp) ref href
      have henvExists :
          ∃ env, ReadEnv.ofStore? store payoff.2.reads = some env := by
        unfold ReadEnv.ofStore?
        by_cases h :
            ∀ ref, ref ∈ payoff.2.reads →
              ∃ value, Store.getAs store ref.field ref.ty = some value
        · exact
            ⟨ReadEnv.ofStore store payoff.2.reads h, by
              rw [dif_pos h]⟩
        · exact False.elim (h headAvailable)
      have restAvailable :
          ∀ payoff, payoff ∈ rest →
            ∀ ref, ref ∈ payoff.2.reads →
              ∃ value, Store.getAs store ref.field ref.ty = some value := by
        intro restPayoff hrest ref href
        exact available restPayoff (by simp [hrest]) ref href
      rcases ih restAvailable with ⟨entries, hentries⟩
      rcases henvExists with ⟨env, henv⟩
      refine
        ⟨(payoff.1, payoff.2.eval env) :: entries, ?_⟩
      simp [evalPayoffEntries?, henv, hentries]

theorem evalPayoffs?_isSome_of_available
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (payoffs : List (Player × EventPayoff L)) (store : Store L)
    (available :
      ∀ payoff, payoff ∈ payoffs →
        ∀ ref, ref ∈ payoff.2.reads →
          ∃ value, Store.getAs store ref.field ref.ty = some value) :
    ∃ outcome, evalPayoffs? payoffs store = some outcome := by
  rcases evalPayoffEntries?_isSome_of_available
      payoffs store available with
    ⟨entries, hentries⟩
  exact ⟨mkOutcome entries, by simp [evalPayoffs?, hentries]⟩

/-- Source-order reveal barrier.

A reveal is source-causally after every earlier commit. This is an information
semantics rule, not an execution convenience: a source-level reveal publishes
information only after all earlier source-level commitments have become fixed.
Otherwise a program fragment `commit; ...; reveal` could be implemented by a
schedule in which the commitment observes information that the source program
reveals only later. Reveals are not ordered after earlier reveals by this rule.
-/
def sourceOrderRevealBarrier? {Player : Type} {L : IExpr}
    (nodes : List (EventNode Player L)) (node prior : Nat) : Bool :=
  if prior < node then
    match nodes[node]?, nodes[prior]? with
    | some current, some prev =>
        NodeSem.isReveal current.sem && NodeSem.isCommit prev.sem
    | _, _ => false
  else
    false

/-- Numeric dependency predicate used internally to compute graph prerequisites.

A prior node is a prerequisite exactly when it writes a field read by the
current node, or when `sourceOrderRevealBarrier?` says a prior source commit
must be fixed before a later reveal. Thus unrelated commit/commit and
reveal/reveal pairs stay unordered, while source-earlier commits are fixed
before any later reveal publishes information. -/
private def canonicalPrereq? {Player : Type} {L : IExpr}
    (initialFieldCount : Nat) (nodes : List (EventNode Player L))
    (node prior : Nat) : Bool :=
  match nodes[node]? with
  | none => false
  | some current =>
      if prior < node then
        match nodes[prior]? with
        | none => false
        | some _prev =>
            initialFieldCount + prior ∈ NodeSem.reads current.sem ||
              sourceOrderRevealBarrier? nodes node prior
      else
        false

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Canonical graph-causal prerequisites for a node. -/
def prereqs (G : Graph Player L)
    (node : Fin G.nodeCount) : Finset (Fin G.nodeCount) :=
  (Finset.univ : Finset (Fin G.nodeCount)).filter fun prior =>
    canonicalPrereq? G.initialFields.length G.nodes node prior = true

/-- Canonical graph prerequisites always point to earlier node ids. -/
theorem prereq_lt (G : Graph Player L)
    {node prior : Fin G.nodeCount}
    (hprior : prior ∈ G.prereqs node) :
    (prior : Nat) < (node : Nat) := by
  unfold prereqs at hprior
  have hcanon :
      canonicalPrereq? G.initialFields.length G.nodes node prior = true := by
    exact (Finset.mem_filter.mp hprior).2
  unfold canonicalPrereq? at hcanon
  cases hnode : G.nodes[(node : Nat)]? with
  | none =>
      simp [hnode] at hcanon
  | some current =>
      by_cases hlt : (prior : Nat) < (node : Nat)
      · exact hlt
      · simp [hnode, hlt] at hcanon

theorem nodeTarget_mem_prereqs_of_read (G : Graph Player L)
    {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat))
    (hread : G.nodeTarget prior ∈ event.sem.reads) :
    prior ∈ G.prereqs node := by
  unfold prereqs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold canonicalPrereq?
  change G.nodes[(node : Nat)]? = some event at hnode
  change G.nodes[(prior : Nat)]? = some priorEvent at hprior
  rw [hnode, hprior]
  unfold nodeTarget at hread
  simp only [hlt, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl hread

theorem prior_commit_mem_prereqs_of_reveal (G : Graph Player L)
    {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat))
    (hreveal : NodeSem.isReveal event.sem = true)
    (hcommit : NodeSem.isCommit priorEvent.sem = true) :
    prior ∈ G.prereqs node := by
  unfold prereqs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold canonicalPrereq?
  change G.nodes[(node : Nat)]? = some event at hnode
  change G.nodes[(prior : Nat)]? = some priorEvent at hprior
  rw [hnode, hprior]
  simp only [hlt, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq]
  right
  simp [sourceOrderRevealBarrier?, hlt, hnode, hprior, hreveal, hcommit]

end Graph

end EventGraph

end Vegas
