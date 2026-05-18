import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Vegas.Base.Basic

/-!
# Event Graphs

The event-graph state is extensional: a configuration records which event
nodes have produced results, not the schedule prefix that produced them. A
frontier is computed from that partial result assignment. Execution order is
presentation and proof data; it is not part of the semantic state.
-/

namespace Vegas

namespace EventGraph

/-- How a node write is classified before player-specific redaction. -/
inductive WriteMode where
  | clear
  | hidden
  deriving DecidableEq, Repr

/-- A semantic field write in a protocol node. -/
inductive FieldWrite (Player Field : Type) where
  | clear (field : Field)
  | hidden (owner : Player) (field : Field)

namespace FieldWrite

variable {Player Field : Type}

/-- The field touched by a write. -/
def field : FieldWrite Player Field → Field
  | .clear field => field
  | .hidden _ field => field

/-- The storage mode of a write. -/
def mode : FieldWrite Player Field → WriteMode
  | .clear _ => .clear
  | .hidden _ _ => .hidden

end FieldWrite

/-- Values of the fields read by an event-graph expression. -/
@[ext]
structure ReadEnv (L : IExpr) (Field : Type)
    (fieldTy : Field → L.Ty) (reads : Finset Field) where
  value : (field : Field) → field ∈ reads → L.Val (fieldTy field)

/-- An event-graph-local expression. Unlike source expressions, this evaluates from
only the fields it declares as reads. -/
structure EventExpr (L : IExpr) (Field : Type) [DecidableEq Field]
    (fieldTy : Field → L.Ty) (ty : L.Ty) where
  reads : Finset Field
  eval : ReadEnv L Field fieldTy reads → L.Val ty

/-- An event-graph-local probability kernel. -/
structure EventDist (L : IExpr) (Field : Type) [DecidableEq Field]
    (fieldTy : Field → L.Ty) (ty : L.Ty) where
  reads : Finset Field
  eval : ReadEnv L Field fieldTy reads → PMF (L.Val ty)

/-- An event-graph-local commit guard. -/
structure EventGuard (L : IExpr) (Field : Type) [DecidableEq Field]
    (fieldTy : Field → L.Ty) (field : Field) where
  reads : Finset Field
  visibleReads : Finset Field
  visibleReads_subset_reads : visibleReads ⊆ reads
  eval : L.Val (fieldTy field) → ReadEnv L Field fieldTy reads → Bool
  eval_eq_of_visible_eq :
    ∀ {value : L.Val (fieldTy field)}
      (ρ₁ ρ₂ : ReadEnv L Field fieldTy reads),
      (∀ read (h₁ : read ∈ reads) (h₂ : read ∈ reads),
        read ∈ visibleReads → ρ₁.value read h₁ = ρ₂.value read h₂) →
        eval value ρ₁ = eval value ρ₂
  satisfiable :
    (ρ : ReadEnv L Field fieldTy reads) →
      ∃ value : L.Val (fieldTy field), eval value ρ = true

namespace ReadEnv

variable {L : IExpr}
variable {Field Field' : Type} [DecidableEq Field']
variable {fieldTy : Field → L.Ty} {fieldTy' : Field' → L.Ty}

/-- Pull a read environment on mapped fields back to the source fields. -/
noncomputable def comapFields
    {reads : Finset Field}
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field)
    (ρ : ReadEnv L Field' fieldTy' (reads.image f)) :
    ReadEnv L Field fieldTy reads where
  value field hmem :=
    cast (by rw [hty field])
      (ρ.value (f field) (Finset.mem_image.mpr ⟨field, hmem, rfl⟩))

end ReadEnv

namespace EventExpr

variable {L : IExpr}
variable {Field Field' : Type} [DecidableEq Field] [DecidableEq Field']
variable {fieldTy : Field → L.Ty} {fieldTy' : Field' → L.Ty}
variable {ty : L.Ty}

/-- Transport a graph expression through a field map preserving field types. -/
noncomputable def mapFields
    (expr : EventExpr L Field fieldTy ty)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    EventExpr L Field' fieldTy' ty where
  reads := expr.reads.image f
  eval := fun ρ => expr.eval (ReadEnv.comapFields f hty ρ)

end EventExpr

namespace EventDist

variable {L : IExpr}
variable {Field Field' : Type} [DecidableEq Field] [DecidableEq Field']
variable {fieldTy : Field → L.Ty} {fieldTy' : Field' → L.Ty}
variable {ty : L.Ty}

/-- Transport a graph distribution through a field map preserving field types. -/
noncomputable def mapFields
    (dist : EventDist L Field fieldTy ty)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    EventDist L Field' fieldTy' ty where
  reads := dist.reads.image f
  eval := fun ρ => dist.eval (ReadEnv.comapFields f hty ρ)

end EventDist

namespace EventGuard

variable {L : IExpr}
variable {Field Field' : Type} [DecidableEq Field] [DecidableEq Field']
variable {fieldTy : Field → L.Ty} {fieldTy' : Field' → L.Ty}

/-- Transport a graph guard through a field map preserving field types. -/
noncomputable def mapFields
    {field : Field}
    (guard : EventGuard L Field fieldTy field)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    EventGuard L Field' fieldTy' (f field) where
  reads := guard.reads.image f
  visibleReads := guard.visibleReads.image f
  visibleReads_subset_reads := by
    intro read hread
    rcases Finset.mem_image.mp hread with ⟨inner, hinner, rfl⟩
    exact Finset.mem_image.mpr
      ⟨inner, guard.visibleReads_subset_reads hinner, rfl⟩
  eval := fun value ρ =>
    guard.eval (cast (by rw [hty field]) value)
      (ReadEnv.comapFields f hty ρ)
  eval_eq_of_visible_eq := by
    intro value ρ₁ ρ₂ hvisible
    apply guard.eval_eq_of_visible_eq
    intro read h₁ h₂ hreadVisible
    simpa [ReadEnv.comapFields] using
      hvisible (f read)
        (Finset.mem_image.mpr ⟨read, h₁, rfl⟩)
        (Finset.mem_image.mpr ⟨read, h₂, rfl⟩)
        (Finset.mem_image.mpr ⟨read, hreadVisible, rfl⟩)
  satisfiable := by
    intro ρ
    rcases guard.satisfiable (ReadEnv.comapFields f hty ρ) with
      ⟨value, hvalue⟩
    refine ⟨cast (by rw [← hty field]) value, ?_⟩
    simpa using hvalue

@[simp] theorem reads_mapFields
    {field : Field}
    (guard : EventGuard L Field fieldTy field)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    (guard.mapFields f hty).reads = guard.reads.image f := rfl

@[simp] theorem visibleReads_mapFields
    {field : Field}
    (guard : EventGuard L Field fieldTy field)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    (guard.mapFields f hty).visibleReads =
      guard.visibleReads.image f := rfl

end EventGuard

/-- Protocol meaning attached to one event node.

This is intentionally semantic, not backend metadata.  Visibility is computed
from the writes: clear writes are public/revealed, hidden writes are commits. -/
inductive NodeSem (Player Field : Type) [DecidableEq Field]
    (L : IExpr) (fieldTy : Field → L.Ty) where
  | assign (field : Field) (expr : EventExpr L Field fieldTy (fieldTy field))
  | sample (field : Field) (dist : EventDist L Field fieldTy (fieldTy field))
  | commit (who : Player) (field : Field)
      (guard : EventGuard L Field fieldTy field)
  | reveal (source target : Field) (sameTy : fieldTy source = fieldTy target)

namespace NodeSem

variable {Player Field : Type} [DecidableEq Field]
variable {L : IExpr} {fieldTy : Field → L.Ty}

variable {Field' : Type} [DecidableEq Field'] {fieldTy' : Field' → L.Ty}

/-- Whether this node is a player commit. -/
def isCommit :
    NodeSem Player Field L fieldTy → Bool
  | .commit .. => true
  | _ => false

/-- Whether this node reveals a previously hidden field. -/
def isReveal :
    NodeSem Player Field L fieldTy → Bool
  | .reveal .. => true
  | _ => false

/-- Transport a node semantic payload through a field map preserving field
types. -/
noncomputable def mapFields
    (sem : NodeSem Player Field L fieldTy)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    NodeSem Player Field' L fieldTy' :=
  match sem with
  | .assign field expr =>
      .assign (f field) {
        reads := expr.reads.image f
        eval := fun ρ =>
          cast (by rw [hty field])
            (expr.eval (ReadEnv.comapFields f hty ρ)) }
  | .sample field dist =>
      .sample (f field) {
        reads := dist.reads.image f
        eval := fun ρ =>
          cast (by rw [hty field])
            (dist.eval (ReadEnv.comapFields f hty ρ)) }
  | .commit who field guard =>
      .commit who (f field) (guard.mapFields f hty)
  | .reveal source target hsameTy =>
      .reveal (f source) (f target)
        (by rw [hty source, hty target, hsameTy])

@[simp] theorem isCommit_mapFields
    (sem : NodeSem Player Field L fieldTy)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    (sem.mapFields f hty).isCommit = sem.isCommit := by
  cases sem <;> rfl

@[simp] theorem isReveal_mapFields
    (sem : NodeSem Player Field L fieldTy)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    (sem.mapFields f hty).isReveal = sem.isReveal := by
  cases sem <;> rfl

/-- Player responsible for this node, if any. -/
def actor :
    NodeSem Player Field L fieldTy → Option Player
  | .assign _ _ => none
  | .sample _ _ => none
  | .commit who _ _ => some who
  | .reveal _ _ _ => none

/-- Fields read by this node. -/
def reads :
    NodeSem Player Field L fieldTy → Finset Field
  | .assign _ expr => expr.reads
  | .sample _ dist => dist.reads
  | .commit _ _ guard => guard.reads
  | .reveal source _ _ => {source}

@[simp] theorem reads_mapFields
    (sem : NodeSem Player Field L fieldTy)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    (sem.mapFields f hty).reads = sem.reads.image f := by
  cases sem with
  | assign field expr =>
      simp [mapFields, reads]
  | sample field dist =>
      simp [mapFields, reads]
  | commit who field guard =>
      rfl
  | reveal source target hsameTy =>
      simp [mapFields, reads]

theorem mem_reads_mapFields
    {sem : NodeSem Player Field L fieldTy}
    {f : Field → Field'}
    {hty : ∀ field, fieldTy' (f field) = fieldTy field}
    {field' : Field'}
    (h : field' ∈ (sem.mapFields f hty).reads) :
    ∃ field, field' = f field ∧ field ∈ sem.reads := by
  have h' : field' ∈ sem.reads.image f := by
    simpa using h
  rcases Finset.mem_image.mp h' with ⟨field, hfield, hfield'⟩
  exact ⟨field, hfield'.symm, hfield⟩

/-- Semantic writes produced by this node. -/
def writes :
    NodeSem Player Field L fieldTy → List (FieldWrite Player Field)
  | .assign field _ => [FieldWrite.clear field]
  | .sample field _ => [FieldWrite.clear field]
  | .commit who field _ => [FieldWrite.hidden who field]
  | .reveal _ target _ => [FieldWrite.clear target]

/-- The unique field targeted by this node's write. -/
def writeTarget :
    NodeSem Player Field L fieldTy → Field
  | .assign field _ => field
  | .sample field _ => field
  | .commit _ field _ => field
  | .reveal _ target _ => target

@[simp] theorem writeTarget_mapFields
    (sem : NodeSem Player Field L fieldTy)
    (f : Field → Field')
    (hty : ∀ field, fieldTy' (f field) = fieldTy field) :
    (sem.mapFields f hty).writeTarget = f sem.writeTarget := by
  cases sem <;> simp [mapFields, writeTarget]

/-- A node writes a field if one of its semantic writes targets that field. -/
def WritesField (sem : NodeSem Player Field L fieldTy) (field : Field) : Prop :=
  ∃ write ∈ sem.writes, write.field = field

/-- A node writes a field with the given storage mode. -/
def WritesWithMode
    (sem : NodeSem Player Field L fieldTy) (field : Field) (mode : WriteMode) :
    Prop :=
  ∃ write ∈ sem.writes, write.field = field ∧ write.mode = mode

/-- Fields written by a node. -/
noncomputable def writeFields
    (sem : NodeSem Player Field L fieldTy) : Finset Field :=
  (sem.writes.map FieldWrite.field).toFinset

/-- Storage mode for a field written by this node, if any.

Conflicting duplicate writes are ruled out by `EventGraph` well-formedness.
Hidden wins here only to make this projection total. -/
noncomputable def writeMode
    (sem : NodeSem Player Field L fieldTy) (field : Field) :
    Option WriteMode := by
  classical
  exact
    if sem.WritesWithMode field .hidden then
      some .hidden
    else if sem.WritesWithMode field .clear then
      some .clear
    else
      none

@[simp] theorem mem_writeFields_iff
    (sem : NodeSem Player Field L fieldTy) (field : Field) :
    field ∈ sem.writeFields ↔ sem.WritesField field := by
  classical
  simp [writeFields, WritesField]

@[simp] theorem writeFields_eq_singleton
    (sem : NodeSem Player Field L fieldTy) :
    sem.writeFields = {sem.writeTarget} := by
  classical
  cases sem <;> simp [writeFields, writes, writeTarget, FieldWrite.field]

theorem mem_writeFields_iff_eq_writeTarget
    (sem : NodeSem Player Field L fieldTy) (field : Field) :
    field ∈ sem.writeFields ↔ field = sem.writeTarget := by
  rw [writeFields_eq_singleton]
  simp

theorem mem_writeFields_mapFields_of_mem
    {sem : NodeSem Player Field L fieldTy}
    {f : Field → Field'}
    {hty : ∀ field, fieldTy' (f field) = fieldTy field}
    {field : Field}
    (h : field ∈ sem.writeFields) :
    f field ∈ (sem.mapFields f hty).writeFields := by
  rw [mem_writeFields_iff_eq_writeTarget] at h ⊢
  rw [h]
  simp

end NodeSem

end EventGraph

/-- A checked protocol dependency graph.

`EventGraph` is protocol-specific.  Nodes have semantic payloads; fields are
typed storage locations; dependencies are the causal/readability order used to
compute the executable frontier.

The graph deliberately does not store a separate visibility map.  Field
visibility is a computed property of `sem node`. -/
structure EventGraph (Player : Type) [DecidableEq Player] (L : IExpr) where
  Node : Type
  Field : Type
  nodeDecEq : DecidableEq Node
  fieldDecEq : DecidableEq Field
  nodes : Finset Node
  fields : Finset Field
  fieldTy : Field → L.Ty
  fieldOwner : Field → Option Player
  initial : (field : Field) → Option (L.Val (fieldTy field))
  sem : Node → @EventGraph.NodeSem Player Field fieldDecEq L fieldTy
  prereqs : Node → Finset Node
  rank : Node → Nat
  prereqs_subset_nodes :
    ∀ {node prereq}, node ∈ nodes → prereq ∈ prereqs node → prereq ∈ nodes
  prereq_rank_lt :
    ∀ {node prereq}, node ∈ nodes → prereq ∈ prereqs node →
      rank prereq < rank node
  read_fields_mem :
    ∀ {node field}, node ∈ nodes → field ∈ (sem node).reads → field ∈ fields
  write_fields_mem :
    ∀ {node write}, node ∈ nodes → write ∈ (sem node).writes →
      write.field ∈ fields
  no_duplicate_writes :
    ∀ {node field left right},
      node ∈ nodes →
      left ∈ (sem node).writes →
      right ∈ (sem node).writes →
      left.field = field →
      right.field = field →
      left = right
  patchLegal :
    Node →
      ((field : Field) →
        Option (L.Val (fieldTy field))) →
      Prop
  actionLegal :
    ((node : Node) →
        Option ((field : Field) →
          Option (L.Val (fieldTy field)))) →
      Node →
      ((field : Field) →
        Option (L.Val (fieldTy field))) →
      Prop
  internalKernel :
    Node →
      ((node : Node) →
        Option ((field : Field) →
          Option (L.Val (fieldTy field)))) →
      PMF ((field : Field) →
        Option (L.Val (fieldTy field)))
  internalKernel_support_legal :
    ∀ {node result patch},
      node ∈ nodes →
      (result node).isNone →
      (∀ prereq, prereq ∈ prereqs node → (result prereq).isSome) →
      (∀ {doneNode donePatch},
        result doneNode = some donePatch → patchLegal doneNode donePatch) →
      (sem node).actor = none →
      patch ∈ (internalKernel node result).support →
      patchLegal node patch

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- A typed field patch produced by one node. -/
abbrev FieldPatch (G : Vegas.EventGraph Player L) : Type :=
  (field : G.Field) → Option (L.Val (G.fieldTy field))

namespace FieldPatch

variable (G : Vegas.EventGraph Player L)

/-- The empty field patch. -/
def empty : FieldPatch G :=
  fun _ => none

/-- A singleton field patch writing one field. -/
noncomputable def single
    (field : G.Field)
    (value : L.Val (G.fieldTy field)) :
    FieldPatch G :=
  fun other =>
    if h : other = field then
      some (cast (by rw [h]) value)
    else
      none

@[simp] theorem single_self
    (field : G.Field)
    (value : L.Val (G.fieldTy field)) :
    single G field value field = some value := by
  simp [single]

@[simp] theorem single_ne
    {field other : G.Field}
    (value : L.Val (G.fieldTy field))
    (h : other ≠ field) :
    single G field value other = none := by
  simp [single, h]

end FieldPatch

/-- Extensional partial node-result assignment. -/
abbrev ResultAssignment (G : Vegas.EventGraph Player L) : Type :=
  (node : G.Node) → Option (FieldPatch G)

/-- Value of a graph field under a partial result assignment. Completed node
patches override initial values; if no completed patch has written the field,
the graph initial value is used. -/
noncomputable def value?
    (G : Vegas.EventGraph Player L) (result : G.ResultAssignment)
    (field : G.Field) : Option (L.Val (G.fieldTy field)) := by
  classical
  exact
    if h :
        ∃ node patch value,
          result node = some patch ∧ patch field = some value then
      let node := Classical.choose h
      let patch := Classical.choose (Classical.choose_spec h)
      let value := Classical.choose (Classical.choose_spec
        (Classical.choose_spec h))
      some value
    else
      G.initial field

theorem value?_isSome_of_result_patch
    (G : Vegas.EventGraph Player L) {result : G.ResultAssignment}
    {field : G.Field} {node : G.Node} {patch : FieldPatch G}
    {value : L.Val (G.fieldTy field)}
    (hresult : result node = some patch)
    (hpatch : patch field = some value) :
    (G.value? result field).isSome := by
  classical
  unfold value?
  rw [dif_pos]
  · simp
  · exact ⟨node, patch, value, hresult, hpatch⟩

/-- Result assignments agree on the prerequisites of a node. -/
def AgreeOnPrereqs (G : Vegas.EventGraph Player L)
    (left right : ResultAssignment G) (node : G.Node) : Prop :=
  ∀ prereq, prereq ∈ G.prereqs node → left prereq = right prereq

/-- Nodes that have already produced a result. -/
noncomputable def done (G : Vegas.EventGraph Player L)
    (result : ResultAssignment G) : Finset G.Node := by
  classical
  exact G.nodes.filter fun node => (result node).isSome

@[simp] theorem mem_done_iff
    (G : Vegas.EventGraph Player L) (result : ResultAssignment G)
    (node : G.Node) :
    node ∈ G.done result ↔ node ∈ G.nodes ∧ (result node).isSome := by
  classical
  simp [done]

/-- Predecessor-closed partial node-result assignment for an event graph.

The closure invariant says completed nodes are lower-closed under graph
dependencies.  The legality invariant says every node result is a
well-formed field patch for that node. Dynamic action legality is checked at the
machine frontier instead of being cached in the configuration. -/
structure ClosedAssignment (G : Vegas.EventGraph Player L) where
  result : ResultAssignment G
  result_nodes :
    ∀ {node}, (result node).isSome → node ∈ G.nodes
  closed :
    ∀ {node prereq},
      (result node).isSome →
      prereq ∈ G.prereqs node →
      (result prereq).isSome
  legal :
    ∀ {node patch},
      result node = some patch →
      G.patchLegal node patch

/-- Machine configuration for the native event-graph semantics.

At the current abstraction level the machine state is exactly a
predecessor-closed assignment. Keeping the configuration name separate leaves
room for future operational state without making the graph assignment itself
carry presentation-specific data. -/
abbrev Configuration (G : Vegas.EventGraph Player L) : Type :=
  ClosedAssignment G

namespace Configuration

variable {G : Vegas.EventGraph Player L}

@[ext] theorem ext
    {left right : G.Configuration}
    (hresult : left.result = right.result) :
    left = right := by
  cases left
  cases right
  cases hresult
  rfl

/-- Empty initial configuration. Initial field values belong to the graph, not
to an executed node result. -/
def initial (G : Vegas.EventGraph Player L) : G.Configuration where
  result := fun _ => none
  result_nodes := by
    intro node h
    simp at h
  closed := by
    intro node prereq h
    simp at h
  legal := by
    intro node patch h
    simp at h

/-- Completed nodes of a configuration. -/
noncomputable def done (cfg : G.Configuration) : Finset G.Node :=
  G.done cfg.result

/-- An event node is enabled when it is unfinished and all prerequisites are
finished. -/
def Enabled (cfg : G.Configuration) (node : G.Node) : Prop :=
  node ∈ G.nodes ∧
    (cfg.result node).isNone ∧
      G.prereqs node ⊆ cfg.done

/-- The frontier: the current enabled event set. -/
noncomputable def frontier (cfg : G.Configuration) : Finset G.Node := by
  classical
  exact G.nodes.filter fun node => cfg.Enabled node

/-- Terminal configurations have completed every event node. -/
def terminal (cfg : G.Configuration) : Prop :=
  G.nodes ⊆ cfg.done

@[simp] theorem mem_frontier_iff
    (cfg : G.Configuration) (node : G.Node) :
    node ∈ cfg.frontier ↔ cfg.Enabled node := by
  classical
  simp [frontier, Enabled]

theorem mem_nodes_of_mem_frontier
    {cfg : G.Configuration} {node : G.Node}
    (h : node ∈ cfg.frontier) :
    node ∈ G.nodes :=
  (cfg.mem_frontier_iff node).mp h |>.1

theorem not_done_of_mem_frontier
    {cfg : G.Configuration} {node : G.Node}
    (h : node ∈ cfg.frontier) :
    (cfg.result node).isNone :=
  (cfg.mem_frontier_iff node).mp h |>.2.1

theorem prereq_done_of_mem_frontier
    {cfg : G.Configuration} {node prereq : G.Node}
    (h : node ∈ cfg.frontier)
    (hpre : prereq ∈ G.prereqs node) :
    prereq ∈ cfg.done :=
  (cfg.mem_frontier_iff node).mp h |>.2.2 hpre

theorem result_some_of_prereq_of_mem_frontier
    {cfg : G.Configuration} {node prereq : G.Node}
    (h : node ∈ cfg.frontier)
    (hpre : prereq ∈ G.prereqs node) :
    (cfg.result prereq).isSome := by
  have hdone := cfg.prereq_done_of_mem_frontier h hpre
  exact (G.mem_done_iff cfg.result prereq).mp hdone |>.2

/-- No current frontier node is a prerequisite of another current frontier
node. This is the graph-level independence fact behind frontier steps:
dependencies must have already been completed before a node reaches the
frontier. -/
theorem not_prereq_of_mem_frontier
    {cfg : G.Configuration} {first second : G.Node}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier) :
    first ∉ G.prereqs second := by
  intro hpre
  have hdone : (cfg.result first).isSome :=
    cfg.result_some_of_prereq_of_mem_frontier hsecond hpre
  have hnone : (cfg.result first).isNone :=
    cfg.not_done_of_mem_frontier hfirst
  cases hresult : cfg.result first <;> simp [hresult] at hdone hnone

theorem not_terminal_of_mem_frontier
    {cfg : G.Configuration} {node : G.Node}
    (h : node ∈ cfg.frontier) :
    ¬ cfg.terminal := by
  intro hterminal
  have hnodes : node ∈ G.nodes := cfg.mem_nodes_of_mem_frontier h
  have hnone : (cfg.result node).isNone :=
    cfg.not_done_of_mem_frontier h
  have hdone : node ∈ cfg.done := hterminal hnodes
  have hsome : (cfg.result node).isSome :=
    (G.mem_done_iff cfg.result node).mp hdone |>.2
  cases hresult : cfg.result node <;> simp [hresult] at hnone hsome

/-- A nonterminal configuration has some unfinished event node. -/
theorem exists_unfinished_of_not_terminal
    {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    ∃ node, node ∈ G.nodes ∧ (cfg.result node).isNone := by
  classical
  simp only [terminal, Finset.not_subset] at hterminal
  rcases hterminal with ⟨node, hnode, hnot_done⟩
  refine ⟨node, hnode, ?_⟩
  cases hresult : cfg.result node with
  | none => rfl
  | some patch =>
      exfalso
      apply hnot_done
      exact (G.mem_done_iff cfg.result node).mpr (by simp [hnode, hresult])

/-- If the configuration is nonterminal, a minimal unfinished node is enabled. -/
theorem exists_enabled_of_not_terminal
    {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    ∃ node, cfg.Enabled node := by
  classical
  rcases cfg.exists_unfinished_of_not_terminal hterminal with
    ⟨witness, hwitness_node, hwitness_unfinished⟩
  let unfinished : Finset G.Node :=
    G.nodes.filter fun node => (cfg.result node).isNone
  have hwitness_none : cfg.result witness = none := by
    cases hresult : cfg.result witness with
    | none => rfl
    | some patch => simp [hresult] at hwitness_unfinished
  have hunfinished_nonempty : unfinished.Nonempty := by
    refine ⟨witness, ?_⟩
    simp [unfinished, hwitness_node, hwitness_none]
  rcases Finset.exists_min_image unfinished G.rank hunfinished_nonempty with
    ⟨node, hnode_unfinished, hmin⟩
  have hnode : node ∈ G.nodes := (Finset.mem_filter.mp hnode_unfinished).1
  have hnode_unfinished' : (cfg.result node).isNone :=
    (Finset.mem_filter.mp hnode_unfinished).2
  refine ⟨node, ⟨hnode, hnode_unfinished', ?_⟩⟩
  intro prereq hpre
  have hpre_node : prereq ∈ G.nodes :=
    G.prereqs_subset_nodes hnode hpre
  by_contra hpre_not_done
  have hpre_unfinished : (cfg.result prereq).isNone := by
    cases hresult : cfg.result prereq with
    | none => rfl
    | some patch =>
        exfalso
        apply hpre_not_done
        exact (G.mem_done_iff cfg.result prereq).mpr
          (by simp [hpre_node, hresult])
  have hpre_none : cfg.result prereq = none := by
    cases hresult : cfg.result prereq with
    | none => rfl
    | some patch => simp [hresult] at hpre_unfinished
  have hle : G.rank node ≤ G.rank prereq :=
    hmin prereq (by simp [unfinished, hpre_node, hpre_none])
  exact (Nat.not_lt_of_ge hle) (G.prereq_rank_lt hnode hpre)

/-- A rank-minimal unfinished node is enabled.

This is the graph-level form of the "linear read is sufficient" principle:
if a reader scans nodes in the graph's rank order and stops at the first
unfinished node, that node is executable. Dependencies cannot be waiting
behind it, because prerequisites have strictly smaller rank. -/
theorem enabled_of_rank_minimal_unfinished
    {cfg : G.Configuration} {node : G.Node}
    (hnode : node ∈ G.nodes)
    (hunfinished : (cfg.result node).isNone)
    (hmin :
      ∀ other, other ∈ G.nodes → (cfg.result other).isNone →
        G.rank node ≤ G.rank other) :
    cfg.Enabled node := by
  refine ⟨hnode, hunfinished, ?_⟩
  intro prereq hpre
  have hpre_node : prereq ∈ G.nodes :=
    G.prereqs_subset_nodes hnode hpre
  by_contra hpre_not_done
  have hpre_unfinished : (cfg.result prereq).isNone := by
    cases hresult : cfg.result prereq with
    | none => rfl
    | some patch =>
        exfalso
        apply hpre_not_done
        exact (G.mem_done_iff cfg.result prereq).mpr
          (by simp [hpre_node, hresult])
  exact (Nat.not_lt_of_ge (hmin prereq hpre_node hpre_unfinished))
    (G.prereq_rank_lt hnode hpre)

/-- Every nonterminal event-graph configuration has an enabled node that is
rank-minimal among all unfinished nodes.

Equivalently: the rank-ordered linear presentation never gets stuck before
the graph execution does. -/
theorem exists_rank_minimal_enabled_of_not_terminal
    {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    ∃ node, cfg.Enabled node ∧
      ∀ other, other ∈ G.nodes → (cfg.result other).isNone →
        G.rank node ≤ G.rank other := by
  classical
  rcases cfg.exists_unfinished_of_not_terminal hterminal with
    ⟨witness, hwitness_node, hwitness_unfinished⟩
  let unfinished : Finset G.Node :=
    G.nodes.filter fun node => (cfg.result node).isNone
  have hwitness_none : cfg.result witness = none := by
    cases hresult : cfg.result witness with
    | none => rfl
    | some patch => simp [hresult] at hwitness_unfinished
  have hunfinished_nonempty : unfinished.Nonempty := by
    refine ⟨witness, ?_⟩
    simp [unfinished, hwitness_node, hwitness_none]
  rcases Finset.exists_min_image unfinished G.rank hunfinished_nonempty with
    ⟨node, hnode_unfinished, hmin⟩
  have hnode : node ∈ G.nodes := (Finset.mem_filter.mp hnode_unfinished).1
  have hnode_unfinished' : (cfg.result node).isNone :=
    (Finset.mem_filter.mp hnode_unfinished).2
  have hmin' :
      ∀ other, other ∈ G.nodes → (cfg.result other).isNone →
        G.rank node ≤ G.rank other := by
    intro other hother hother_unfinished
    have hother_none : cfg.result other = none := by
      cases hresult : cfg.result other with
      | none => rfl
      | some patch => simp [hresult] at hother_unfinished
    exact hmin other (by simp [unfinished, hother, hother_none])
  exact ⟨node,
    cfg.enabled_of_rank_minimal_unfinished hnode hnode_unfinished' hmin',
    hmin'⟩

/-- A nonterminal configuration has a nonempty executable frontier. -/
theorem frontier_nonempty_of_not_terminal
    {cfg : G.Configuration}
    (hterminal : ¬ cfg.terminal) :
    cfg.frontier.Nonempty := by
  rcases cfg.exists_enabled_of_not_terminal hterminal with ⟨node, henabled⟩
  exact ⟨node, (cfg.mem_frontier_iff node).mpr henabled⟩

/-- Replace the result at one node. -/
noncomputable def updatePatch
    (cfg : G.Configuration) (node : G.Node) (patch : FieldPatch G) :
    ResultAssignment G := by
  classical
  exact fun candidate =>
    if candidate = node then some patch else cfg.result candidate

@[simp] theorem updatePatch_self
    (cfg : G.Configuration) (node : G.Node) (patch : FieldPatch G) :
    updatePatch cfg node patch node = some patch := by
  classical
  simp [updatePatch]

@[simp] theorem updatePatch_of_ne
    (cfg : G.Configuration) {node candidate : G.Node}
    (patch : FieldPatch G) (h : candidate ≠ node) :
    updatePatch cfg node patch candidate = cfg.result candidate := by
  classical
  simp [updatePatch, h]

/-- Execute one enabled event node with a legal result, producing the extensional
successor configuration. -/
noncomputable def withPatch
    (cfg : G.Configuration) {node : G.Node} (patch : FieldPatch G)
    (hfrontier : node ∈ cfg.frontier)
    (hlegal : G.patchLegal node patch) :
    G.Configuration where
  result := updatePatch cfg node patch
  result_nodes := by
    classical
    intro candidate hsome
    by_cases hcandidate : candidate = node
    · subst candidate
      exact cfg.mem_nodes_of_mem_frontier hfrontier
    · have hold : (cfg.result candidate).isSome := by
        simpa [updatePatch, hcandidate] using hsome
      exact cfg.result_nodes hold
  closed := by
    classical
    intro candidate prereq hcandidateDone hpre
    by_cases hcandidate : candidate = node
    · subst candidate
      have hpreDone : (cfg.result prereq).isSome :=
        cfg.result_some_of_prereq_of_mem_frontier hfrontier hpre
      by_cases hpreq : prereq = node
      · subst prereq
        have hnodeNone : (cfg.result node).isNone :=
          cfg.not_done_of_mem_frontier hfrontier
        cases hnode : cfg.result node <;> simp [hnode] at hpreDone hnodeNone
      · simpa [updatePatch, hpreq] using hpreDone
    · have hcandidateOld : (cfg.result candidate).isSome := by
        simpa [updatePatch, hcandidate] using hcandidateDone
      have hpreOld : (cfg.result prereq).isSome :=
        cfg.closed hcandidateOld hpre
      by_cases hpreq : prereq = node
      · subst prereq
        have hnodeNone : (cfg.result node).isNone :=
          cfg.not_done_of_mem_frontier hfrontier
        cases hnode : cfg.result node <;> simp [hnode] at hpreOld hnodeNone
      · simpa [updatePatch, hpreq] using hpreOld
  legal := by
    classical
    intro candidate candidatePatch hcandidateResult
    by_cases hcandidate : candidate = node
    · subst candidate
      have hpatch : patch = candidatePatch := by
        simpa [updatePatch] using hcandidateResult
      subst candidatePatch
      exact hlegal
    · have holdResult : cfg.result candidate = some candidatePatch := by
        simpa [updatePatch, hcandidate] using hcandidateResult
      exact cfg.legal holdResult

/-- A distinct frontier node remains on the frontier after executing another
frontier node. Executing one enabled event only records that event's
result; it does not invalidate any other enabled event. -/
theorem withPatch_mem_frontier_of_ne
    (cfg : G.Configuration)
    {first second : G.Node} {patch : FieldPatch G}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hlegal : G.patchLegal first patch) :
    second ∈ (cfg.withPatch patch hfirst hlegal).frontier := by
  classical
  rw [mem_frontier_iff] at hsecond ⊢
  rcases hsecond with ⟨hnode, hnone, hprereqs⟩
  refine ⟨hnode, ?_, ?_⟩
  · simpa [withPatch, updatePatch, hne] using hnone
  · intro prereq hpre
    have hdone := hprereqs hpre
    have hdoneData := (G.mem_done_iff cfg.result prereq).mp hdone
    refine (G.mem_done_iff
      (cfg.withPatch patch hfirst hlegal).result prereq).mpr ?_
    refine ⟨hdoneData.1, ?_⟩
    by_cases hpreq : prereq = first
    · subst prereq
      simp [withPatch, updatePatch]
    · simpa [withPatch, updatePatch, hpreq] using hdoneData.2

/-- Frontier execution has a diamond property: two distinct enabled events
can be linearized in either order, and after both have executed the same
extensional configuration is reached. -/
theorem withPatch_comm
    (cfg : G.Configuration)
    {left right : G.Node} {leftPatch rightPatch : FieldPatch G}
    (hleft : left ∈ cfg.frontier)
    (hright : right ∈ cfg.frontier)
    (hne : left ≠ right)
    (hleftLegal : G.patchLegal left leftPatch)
    (hrightLegal : G.patchLegal right rightPatch) :
    let hrightAfterLeft :=
      cfg.withPatch_mem_frontier_of_ne
        hleft hright (Ne.symm hne) hleftLegal
    let hleftAfterRight :=
      cfg.withPatch_mem_frontier_of_ne
        hright hleft hne hrightLegal
    (cfg.withPatch leftPatch hleft hleftLegal).withPatch
        rightPatch hrightAfterLeft hrightLegal =
      (cfg.withPatch rightPatch hright hrightLegal).withPatch
        leftPatch hleftAfterRight hleftLegal := by
  classical
  dsimp
  apply Configuration.ext
  funext candidate
  by_cases hcLeft : candidate = left
  · subst candidate
    have hleftRight : left ≠ right := hne
    simp [withPatch, updatePatch, hleftRight]
  · by_cases hcRight : candidate = right
    · subst candidate
      have hrightLeft : right ≠ left := Ne.symm hne
      simp [withPatch, updatePatch, hrightLeft]
    · simp [withPatch, updatePatch, hcLeft, hcRight]

/-- Record legal patches for a finite subset of the current frontier, leaving
all other node results unchanged. This is the prefix form of
`withFrontierPatches`: it describes the extensional state reached after any
schedule prefix that executes exactly `nodes`. -/
noncomputable def withNodePatches
    (cfg : G.Configuration)
    (nodes : Finset G.Node)
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → FieldPatch G)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode)) :
    G.Configuration where
  result := fun candidate =>
    if hnode : candidate ∈ nodes then
      some (patch candidate hnode)
    else
      cfg.result candidate
  result_nodes := by
    classical
    intro candidate hsome
    by_cases hnode : candidate ∈ nodes
    · exact cfg.mem_nodes_of_mem_frontier (hsubset hnode)
    · have hold : (cfg.result candidate).isSome := by
        dsimp only
        rw [dif_neg hnode] at hsome
        exact hsome
      exact cfg.result_nodes hold
  closed := by
    classical
    intro candidate prereq hcandidateDone hpre
    by_cases hcandidateNode : candidate ∈ nodes
    · have hpreDone : (cfg.result prereq).isSome :=
        cfg.result_some_of_prereq_of_mem_frontier
          (hsubset hcandidateNode) hpre
      by_cases hpreNode : prereq ∈ nodes
      · dsimp only
        rw [dif_pos hpreNode]
        rfl
      · dsimp only
        rw [dif_neg hpreNode]
        exact hpreDone
    · have hcandidateOld : (cfg.result candidate).isSome := by
        rw [dif_neg hcandidateNode] at hcandidateDone
        exact hcandidateDone
      have hpreDone : (cfg.result prereq).isSome :=
        cfg.closed hcandidateOld hpre
      by_cases hpreNode : prereq ∈ nodes
      · dsimp only
        rw [dif_pos hpreNode]
        rfl
      · dsimp only
        rw [dif_neg hpreNode]
        exact hpreDone
  legal := by
    classical
    intro candidate candidatePatch hcandidateResult
    by_cases hnode : candidate ∈ nodes
    · rw [dif_pos hnode] at hcandidateResult
      have hpatch : patch candidate hnode = candidatePatch := by
        simpa using hcandidateResult
      subst candidatePatch
      exact hlegal candidate hnode
    · have holdResult : cfg.result candidate = some candidatePatch := by
        rw [dif_neg hnode] at hcandidateResult
        exact hcandidateResult
      exact cfg.legal holdResult

@[simp] theorem withNodePatches_result_of_mem
    (cfg : G.Configuration)
    (nodes : Finset G.Node)
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → FieldPatch G)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode))
    {node : G.Node} (hnode : node ∈ nodes) :
    (cfg.withNodePatches nodes hsubset patch hlegal).result node =
      some (patch node hnode) := by
  classical
  dsimp [withNodePatches]
  rw [dif_pos hnode]

@[simp] theorem withNodePatches_result_of_not_mem
    (cfg : G.Configuration)
    (nodes : Finset G.Node)
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → FieldPatch G)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode))
    {node : G.Node} (hnode : node ∉ nodes) :
    (cfg.withNodePatches nodes hsubset patch hlegal).result node =
      cfg.result node := by
  classical
  dsimp [withNodePatches]
  rw [dif_neg hnode]

/-- Partial-frontier extension is extensional in the selected patches. -/
theorem withNodePatches_congr
    (cfg : G.Configuration)
    (nodes : Finset G.Node)
    {hsubset₁ hsubset₂ : nodes ⊆ cfg.frontier}
    {patch₁ patch₂ : ∀ node, node ∈ nodes → FieldPatch G}
    {hlegal₁ : ∀ node hnode, G.patchLegal node (patch₁ node hnode)}
    {hlegal₂ : ∀ node hnode, G.patchLegal node (patch₂ node hnode)}
    (hpatch :
      ∀ node (h₁ h₂ : node ∈ nodes), patch₁ node h₁ = patch₂ node h₂) :
    cfg.withNodePatches nodes hsubset₁ patch₁ hlegal₁ =
      cfg.withNodePatches nodes hsubset₂ patch₂ hlegal₂ := by
  classical
  apply Configuration.ext
  funext candidate
  by_cases hnode : candidate ∈ nodes
  · rw [withNodePatches_result_of_mem cfg nodes hsubset₁ patch₁ hlegal₁ hnode]
    rw [withNodePatches_result_of_mem cfg nodes hsubset₂ patch₂ hlegal₂ hnode]
    rw [hpatch candidate hnode hnode]
  · rw [withNodePatches_result_of_not_mem cfg nodes hsubset₁ patch₁ hlegal₁ hnode]
    rw [withNodePatches_result_of_not_mem cfg nodes hsubset₂ patch₂ hlegal₂ hnode]

/-- A source-frontier node that is not in the executed subset remains enabled
after recording that subset. -/
theorem withNodePatches_mem_frontier_of_not_mem
    (cfg : G.Configuration)
    {nodes : Finset G.Node}
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → FieldPatch G)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode))
    {candidate : G.Node}
    (hcandidate : candidate ∈ cfg.frontier)
    (hnotmem : candidate ∉ nodes) :
    candidate ∈
      (cfg.withNodePatches nodes hsubset patch hlegal).frontier := by
  classical
  rw [mem_frontier_iff] at hcandidate ⊢
  rcases hcandidate with ⟨hnode, hnone, hprereqs⟩
  refine ⟨hnode, ?_, ?_⟩
  · simpa [withNodePatches, hnotmem] using hnone
  · intro prereq hpre
    have hdone := hprereqs hpre
    have hdoneData := (G.mem_done_iff cfg.result prereq).mp hdone
    refine (G.mem_done_iff
      (cfg.withNodePatches nodes hsubset patch hlegal).result prereq).mpr ?_
    refine ⟨hdoneData.1, ?_⟩
    by_cases hpreNode : prereq ∈ nodes
    · simp [withNodePatches, hpreNode]
    · simpa [withNodePatches, hpreNode] using hdoneData.2

/-- Adding one more source-frontier patch to a partial-frontier extension is the
same extensional state as extending by the inserted subset at once. -/
theorem withNodePatches_insert_eq_withPatch
    (cfg : G.Configuration)
    {nodes : Finset G.Node}
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → FieldPatch G)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode))
    {node : G.Node}
    (hfrontier : node ∈ cfg.frontier)
    (hnotmem : node ∉ nodes)
    (nodePatch : FieldPatch G)
    (hnodeLegal : G.patchLegal node nodePatch) :
    let inserted : Finset G.Node := insert node nodes
    let insertedSubset : inserted ⊆ cfg.frontier := by
      intro candidate hcandidate
      rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
      · subst candidate
        exact hfrontier
      · exact hsubset hcandidate
    let insertedPatch :
        ∀ candidate, candidate ∈ inserted → FieldPatch G := fun candidate hcandidate =>
      if h : candidate = node then
        nodePatch
      else
        patch candidate (by
          have hmem := (Finset.mem_insert.mp hcandidate)
          rcases hmem with hmem | hmem
          · exact False.elim (h hmem)
          · exact hmem)
    let insertedLegal :
        ∀ candidate hcandidate,
          G.patchLegal candidate (insertedPatch candidate hcandidate) := by
      intro candidate hcandidate
      dsimp [insertedPatch]
      split
      · subst candidate
        exact hnodeLegal
      · rename_i hne
        exact hlegal candidate (by
          rcases Finset.mem_insert.mp hcandidate with hmem | hmem
          · exact False.elim (hne hmem)
          · exact hmem)
    (cfg.withNodePatches nodes hsubset patch hlegal).withPatch
        nodePatch
        (cfg.withNodePatches_mem_frontier_of_not_mem
          hsubset patch hlegal hfrontier hnotmem)
        hnodeLegal =
      cfg.withNodePatches inserted insertedSubset insertedPatch
        insertedLegal := by
  classical
  dsimp
  apply Configuration.ext
  funext candidate
  by_cases hcnode : candidate = node
  · subst candidate
    simp [withPatch, updatePatch, withNodePatches]
  · by_cases hcmem : candidate ∈ nodes
    · have hcinsert : candidate ∈ insert node nodes :=
        Finset.mem_insert_of_mem hcmem
      simp [withPatch, updatePatch, withNodePatches, hcnode, hcmem]
    · have hcinsert : candidate ∉ insert node nodes := by
        intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hcnode h
        · exact hcmem h
      simp [withPatch, updatePatch, withNodePatches, hcnode, hcmem]

/-- Execute a whole frontier extensionally by recording one legal field patch
for each node in the current frontier and leaving every non-frontier result as
it was.

This is not a scheduler. It is the canonical endpoint that any legal
linearization of the same source frontier and same sampled/player patches must
reach. -/
noncomputable def withFrontierPatches
    (cfg : G.Configuration)
    (patch : ∀ node, node ∈ cfg.frontier → FieldPatch G)
    (hlegal : ∀ node hfrontier, G.patchLegal node (patch node hfrontier)) :
    G.Configuration where
  result := fun candidate =>
    if hfrontier : candidate ∈ cfg.frontier then
      some (patch candidate hfrontier)
    else
      cfg.result candidate
  result_nodes := by
    classical
    intro candidate hsome
    by_cases hfrontier : candidate ∈ cfg.frontier
    · exact cfg.mem_nodes_of_mem_frontier hfrontier
    · have hold : (cfg.result candidate).isSome := by
        dsimp only
        rw [dif_neg hfrontier] at hsome
        exact hsome
      exact cfg.result_nodes hold
  closed := by
    classical
    intro candidate prereq hcandidateDone hpre
    by_cases hcandidateFrontier : candidate ∈ cfg.frontier
    · have hpreDone : (cfg.result prereq).isSome :=
        cfg.result_some_of_prereq_of_mem_frontier hcandidateFrontier hpre
      by_cases hpreFrontier : prereq ∈ cfg.frontier
      · dsimp only
        rw [dif_pos hpreFrontier]
        rfl
      · dsimp only
        rw [dif_neg hpreFrontier]
        exact hpreDone
    · have hcandidateOld : (cfg.result candidate).isSome := by
        rw [dif_neg hcandidateFrontier] at hcandidateDone
        exact hcandidateDone
      have hpreDone : (cfg.result prereq).isSome :=
        cfg.closed hcandidateOld hpre
      by_cases hpreFrontier : prereq ∈ cfg.frontier
      · dsimp only
        rw [dif_pos hpreFrontier]
        rfl
      · dsimp only
        rw [dif_neg hpreFrontier]
        exact hpreDone
  legal := by
    classical
    intro candidate candidatePatch hcandidateResult
    by_cases hfrontier : candidate ∈ cfg.frontier
    · rw [dif_pos hfrontier] at hcandidateResult
      have hpatch : patch candidate hfrontier = candidatePatch := by
        simpa using hcandidateResult
      subst candidatePatch
      exact hlegal candidate hfrontier
    · have holdResult : cfg.result candidate = some candidatePatch := by
        rw [dif_neg hfrontier] at hcandidateResult
        exact hcandidateResult
      exact cfg.legal holdResult

@[simp] theorem withFrontierPatches_result_of_mem
    (cfg : G.Configuration)
    (patch : ∀ node, node ∈ cfg.frontier → FieldPatch G)
    (hlegal : ∀ node hfrontier, G.patchLegal node (patch node hfrontier))
    {node : G.Node} (hfrontier : node ∈ cfg.frontier) :
    (cfg.withFrontierPatches patch hlegal).result node =
      some (patch node hfrontier) := by
  classical
  dsimp [withFrontierPatches]
  rw [dif_pos hfrontier]

@[simp] theorem withFrontierPatches_result_of_not_mem
    (cfg : G.Configuration)
    (patch : ∀ node, node ∈ cfg.frontier → FieldPatch G)
    (hlegal : ∀ node hfrontier, G.patchLegal node (patch node hfrontier))
    {node : G.Node} (hfrontier : node ∉ cfg.frontier) :
    (cfg.withFrontierPatches patch hlegal).result node =
      cfg.result node := by
  classical
  dsimp [withFrontierPatches]
  rw [dif_neg hfrontier]

/-- A configuration is the canonical whole-frontier result iff it records the
chosen patch at every source-frontier node and leaves every non-frontier node's
result unchanged. This is the extensional form of frontier linearization
invariance: scheduler order is not part of the endpoint once the per-node
results are fixed. -/
theorem eq_withFrontierPatches_of_result_eq
    (cfg dst : G.Configuration)
    (patch : ∀ node, node ∈ cfg.frontier → FieldPatch G)
    (hlegal : ∀ node hfrontier, G.patchLegal node (patch node hfrontier))
    (honFrontier :
      ∀ node (hfrontier : node ∈ cfg.frontier),
        dst.result node = some (patch node hfrontier))
    (hoffFrontier :
      ∀ node, node ∉ cfg.frontier → dst.result node = cfg.result node) :
    dst = cfg.withFrontierPatches patch hlegal := by
  classical
  apply Configuration.ext
  funext node
  by_cases hfrontier : node ∈ cfg.frontier
  · rw [honFrontier node hfrontier]
    rw [withFrontierPatches_result_of_mem cfg patch hlegal hfrontier]
  · rw [hoffFrontier node hfrontier]
    rw [withFrontierPatches_result_of_not_mem cfg patch hlegal hfrontier]

end Configuration

/-- The finite index of nodes enabled at a configuration. -/
abbrev FrontierIndex (G : Vegas.EventGraph Player L)
    (cfg : G.Configuration) : Type :=
  { node : G.Node // node ∈ cfg.frontier }

/-- Order-free assignment of one concrete field patch to every node in the
current frontier. This is the semantic payload of a realized event-graph round;
primitive event lists are schedules that realize this payload. -/
structure FrontierRealization
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration) where
  patch : FrontierIndex G cfg → FieldPatch G

namespace FrontierRealization

variable {G : Vegas.EventGraph Player L} {cfg : G.Configuration}

/-- All patches in a frontier realization are legal for their nodes. -/
def Legal (realization : FrontierRealization G cfg) : Prop :=
  ∀ idx : FrontierIndex G cfg, G.patchLegal idx.1 (realization.patch idx)

/-- Patch selected for a frontier node. -/
def patchAt (realization : FrontierRealization G cfg)
    (node : G.Node) (hfrontier : node ∈ cfg.frontier) :
    FieldPatch G :=
  realization.patch ⟨node, hfrontier⟩

@[ext] theorem ext
    {left right : FrontierRealization G cfg}
    (hpatch : ∀ idx, left.patch idx = right.patch idx) :
    left = right := by
  cases left with
  | mk leftPatch =>
      cases right with
      | mk rightPatch =>
          have h : leftPatch = rightPatch := by
            funext idx
            exact hpatch idx
          cases h
          rfl

end FrontierRealization

namespace Configuration

variable {G : Vegas.EventGraph Player L}

/-- Extend a configuration by recording one legal patch for every currently
enabled frontier node. -/
noncomputable def extendFrontier
    (cfg : G.Configuration)
    (realization : FrontierRealization G cfg)
    (hlegal : realization.Legal) :
    G.Configuration :=
  cfg.withFrontierPatches
    (fun node hfrontier => realization.patchAt node hfrontier)
    (fun node hfrontier => hlegal ⟨node, hfrontier⟩)

@[simp] theorem extendFrontier_result_of_mem
    (cfg : G.Configuration)
    (realization : FrontierRealization G cfg)
    (hlegal : realization.Legal)
    {node : G.Node} (hfrontier : node ∈ cfg.frontier) :
    (cfg.extendFrontier realization hlegal).result node =
      some (realization.patchAt node hfrontier) := by
  exact
    withFrontierPatches_result_of_mem cfg
      (fun node hfrontier => realization.patchAt node hfrontier)
      (fun node hfrontier => hlegal ⟨node, hfrontier⟩)
      hfrontier

@[simp] theorem extendFrontier_result_of_not_mem
    (cfg : G.Configuration)
    (realization : FrontierRealization G cfg)
    (hlegal : realization.Legal)
    {node : G.Node} (hfrontier : node ∉ cfg.frontier) :
    (cfg.extendFrontier realization hlegal).result node =
      cfg.result node := by
  simp [extendFrontier, hfrontier]

end Configuration

/-- Graph configurations are finite when nodes, fields, and every field value
domain are finite. The configuration invariant is proof data over a finite
result assignment. -/
@[reducible] noncomputable instance Configuration.instFintype
    (G : Vegas.EventGraph Player L)
    [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype G.Configuration := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (L.Val (G.fieldTy field))) :=
    fun _ => inferInstance
  letI : Fintype (FieldPatch G) := by
    dsimp [FieldPatch]
    infer_instance
  letI : Fintype (ResultAssignment G) := by
    dsimp [ResultAssignment]
    infer_instance
  let ValidResult : Type :=
    { result : ResultAssignment G //
      (∀ {node}, (result node).isSome → node ∈ G.nodes) ∧
      (∀ {node prereq},
        (result node).isSome → prereq ∈ G.prereqs node →
          (result prereq).isSome) ∧
      (∀ {node patch}, result node = some patch → G.patchLegal node patch) }
  haveI : Fintype ValidResult := by
    dsimp [ValidResult]
    infer_instance
  let e : G.Configuration ≃ ValidResult :=
    { toFun := fun cfg =>
        ⟨cfg.result, cfg.result_nodes, cfg.closed, cfg.legal⟩
      invFun := fun result =>
        { result := result.1
          result_nodes := result.2.1
          closed := result.2.2.1
          legal := result.2.2.2 }
      left_inv := by
        intro cfg
        cases cfg
        rfl
      right_inv := by
        intro result
        cases result
        rfl }
  exact Fintype.ofEquiv ValidResult e.symm

end EventGraph

end Vegas
