import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Vegas.Core

/-!
# Protocol graphs

This module is the intended replacement core for `Vegas.Protocol.ActionGraph`.

The graph state is extensional: a configuration records which graph nodes have
produced results, not the schedule prefix that produced them.  A frontier is
computed from that partial result assignment.  Execution order is presentation
and proof data; it is not stored in the semantic state.
-/

namespace Vegas

namespace ProtocolGraph

/-- How a node write is stored before player-specific redaction. -/
inductive WriteMode where
  | clear
  | hidden
  deriving DecidableEq, Repr

/-- One typed stored value. -/
inductive StoredValue (α : Type) where
  | clear (value : α)
  | hidden (value : α)
  deriving DecidableEq, Repr

namespace StoredValue

variable {α : Type}

/-- Forget whether a stored value is currently public or sealed. -/
def raw : StoredValue α → α
  | .clear value => value
  | .hidden value => value

end StoredValue

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

/-- Values of the fields read by a graph expression. -/
structure ReadEnv (L : IExpr) (Field : Type)
    (fieldTy : Field → L.Ty) (reads : Finset Field) where
  value : (field : Field) → field ∈ reads → L.Val (fieldTy field)

/-- A graph-local expression. Unlike source expressions, this evaluates from
only the fields it declares as reads. -/
structure GraphExpr (L : IExpr) (Field : Type) [DecidableEq Field]
    (fieldTy : Field → L.Ty) (ty : L.Ty) where
  reads : Finset Field
  eval : ReadEnv L Field fieldTy reads → L.Val ty

/-- A graph-local probability kernel. -/
structure GraphDist (L : IExpr) (Field : Type) [DecidableEq Field]
    (fieldTy : Field → L.Ty) (ty : L.Ty) where
  reads : Finset Field
  eval : ReadEnv L Field fieldTy reads → PMF (L.Val ty)

/-- A graph-local commit guard. -/
structure GraphGuard (L : IExpr) (Field : Type) [DecidableEq Field]
    (fieldTy : Field → L.Ty) (field : Field) where
  reads : Finset Field
  eval : L.Val (fieldTy field) → ReadEnv L Field fieldTy reads → Bool

/-- Protocol meaning attached to one graph node.

This is intentionally semantic, not backend metadata.  Visibility is computed
from the writes: clear writes are public/revealed, hidden writes are commits. -/
inductive NodeSem (Player Field : Type) [DecidableEq Field]
    (L : IExpr) (fieldTy : Field → L.Ty) where
  | assign (field : Field) (expr : GraphExpr L Field fieldTy (fieldTy field))
  | sample (field : Field) (dist : GraphDist L Field fieldTy (fieldTy field))
  | commit (who : Player) (field : Field)
      (guard : GraphGuard L Field fieldTy field)
  | reveal (source target : Field) (sameTy : fieldTy source = fieldTy target)

namespace NodeSem

variable {Player Field : Type} [DecidableEq Field]
variable {L : IExpr} {fieldTy : Field → L.Ty}

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

/-- Semantic writes produced by this node. -/
def writes :
    NodeSem Player Field L fieldTy → List (FieldWrite Player Field)
  | .assign field _ => [FieldWrite.clear field]
  | .sample field _ => [FieldWrite.clear field]
  | .commit who field _ => [FieldWrite.hidden who field]
  | .reveal _ target _ => [FieldWrite.clear target]

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

Conflicting duplicate writes are ruled out by `ProtocolGraph` well-formedness.
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

end NodeSem

end ProtocolGraph

/-- A checked protocol dependency graph.

`ProtocolGraph` is protocol-specific.  Nodes have semantic payloads; fields are
typed storage locations; dependencies are the causal/readability order used to
compute the executable frontier.

The graph deliberately does not store a separate visibility map.  Field
visibility is a computed property of `sem node`. -/
structure ProtocolGraph (Player : Type) [DecidableEq Player] (L : IExpr) where
  Node : Type
  Field : Type
  nodeDecEq : DecidableEq Node
  fieldDecEq : DecidableEq Field
  nodes : Finset Node
  fields : Finset Field
  fieldTy : Field → L.Ty
  fieldOwner : Field → Option Player
  initial : (field : Field) → Option (L.Val (fieldTy field))
  sem : Node → @ProtocolGraph.NodeSem Player Field fieldDecEq L fieldTy
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
  sliceLegal :
    Node →
      ((field : Field) →
        Option (ProtocolGraph.StoredValue (L.Val (fieldTy field)))) →
      Prop
  actionLegal :
    ((node : Node) →
        Option ((field : Field) →
          Option (ProtocolGraph.StoredValue (L.Val (fieldTy field))))) →
      Node →
      ((field : Field) →
        Option (ProtocolGraph.StoredValue (L.Val (fieldTy field)))) →
      Prop
  internalKernel :
    Node →
      ((node : Node) →
        Option ((field : Field) →
          Option (ProtocolGraph.StoredValue (L.Val (fieldTy field))))) →
      PMF ((field : Field) →
        Option (ProtocolGraph.StoredValue (L.Val (fieldTy field))))

namespace ProtocolGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] ProtocolGraph.nodeDecEq
attribute [local instance] ProtocolGraph.fieldDecEq

/-- A typed write slice produced by one node. -/
abbrev WriteSlice (G : Vegas.ProtocolGraph Player L) : Type :=
  (field : G.Field) → Option (StoredValue (L.Val (G.fieldTy field)))

namespace WriteSlice

variable (G : Vegas.ProtocolGraph Player L)

/-- The empty result slice. -/
def empty : WriteSlice G :=
  fun _ => none

/-- A singleton result slice writing one field. -/
noncomputable def single
    (field : G.Field)
    (value : StoredValue (L.Val (G.fieldTy field))) :
    WriteSlice G :=
  fun other =>
    if h : other = field then
      some (cast (by rw [h]) value)
    else
      none

@[simp] theorem single_self
    (field : G.Field)
    (value : StoredValue (L.Val (G.fieldTy field))) :
    single G field value field = some value := by
  simp [single]

@[simp] theorem single_ne
    {field other : G.Field}
    (value : StoredValue (L.Val (G.fieldTy field)))
    (h : other ≠ field) :
    single G field value other = none := by
  simp [single, h]

end WriteSlice

/-- Extensional partial node-result assignment. -/
abbrev ResultAssignment (G : Vegas.ProtocolGraph Player L) : Type :=
  (node : G.Node) → Option (WriteSlice G)

/-- Result assignments agree on the prerequisites of a node. -/
def AgreeOnPrereqs (G : Vegas.ProtocolGraph Player L)
    (left right : ResultAssignment G) (node : G.Node) : Prop :=
  ∀ prereq, prereq ∈ G.prereqs node → left prereq = right prereq

/-- Nodes that have already produced a result. -/
noncomputable def done (G : Vegas.ProtocolGraph Player L)
    (result : ResultAssignment G) : Finset G.Node := by
  classical
  exact G.nodes.filter fun node => (result node).isSome

@[simp] theorem mem_done_iff
    (G : Vegas.ProtocolGraph Player L) (result : ResultAssignment G)
    (node : G.Node) :
    node ∈ G.done result ↔ node ∈ G.nodes ∧ (result node).isSome := by
  classical
  simp [done]

/-- Extensional machine configuration for a protocol graph.

The closure invariant says completed nodes are lower-closed under graph
dependencies.  The legality invariant says every stored node result is a
well-formed slice for that node. Dynamic action legality is checked at the
machine frontier instead of being cached in the configuration. -/
structure Configuration (G : Vegas.ProtocolGraph Player L) where
  result : ResultAssignment G
  result_nodes :
    ∀ {node}, (result node).isSome → node ∈ G.nodes
  closed :
    ∀ {node prereq},
      (result node).isSome →
      prereq ∈ G.prereqs node →
      (result prereq).isSome
  legal :
    ∀ {node slice},
      result node = some slice →
      G.sliceLegal node slice

namespace Configuration

variable {G : Vegas.ProtocolGraph Player L}

/-- Empty initial configuration. Initial field values belong to the graph, not
to an executed node result. -/
def initial (G : Vegas.ProtocolGraph Player L) : G.Configuration where
  result := fun _ => none
  result_nodes := by
    intro node h
    simp at h
  closed := by
    intro node prereq h
    simp at h
  legal := by
    intro node slice h
    simp at h

/-- Completed nodes of a configuration. -/
noncomputable def done (cfg : G.Configuration) : Finset G.Node :=
  G.done cfg.result

/-- A graph node is ready when it is unfinished and all prerequisites are
finished. -/
def Ready (cfg : G.Configuration) (node : G.Node) : Prop :=
  node ∈ G.nodes ∧
    (cfg.result node).isNone ∧
      G.prereqs node ⊆ cfg.done

/-- The executable frontier: currently schedulable graph events. -/
noncomputable def frontier (cfg : G.Configuration) : Finset G.Node := by
  classical
  exact G.nodes.filter fun node => cfg.Ready node

/-- Terminal configurations have completed every graph node. -/
def terminal (cfg : G.Configuration) : Prop :=
  G.nodes ⊆ cfg.done

@[simp] theorem mem_frontier_iff
    (cfg : G.Configuration) (node : G.Node) :
    node ∈ cfg.frontier ↔ cfg.Ready node := by
  classical
  simp [frontier, Ready]

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

/-- Replace the result at one node. -/
noncomputable def updateResult
    (cfg : G.Configuration) (node : G.Node) (slice : WriteSlice G) :
    ResultAssignment G := by
  classical
  exact fun candidate =>
    if candidate = node then some slice else cfg.result candidate

@[simp] theorem updateResult_self
    (cfg : G.Configuration) (node : G.Node) (slice : WriteSlice G) :
    updateResult cfg node slice node = some slice := by
  classical
  simp [updateResult]

@[simp] theorem updateResult_of_ne
    (cfg : G.Configuration) {node candidate : G.Node}
    (slice : WriteSlice G) (h : candidate ≠ node) :
    updateResult cfg node slice candidate = cfg.result candidate := by
  classical
  simp [updateResult, h]

/-- Execute one ready graph node with a legal result, producing the extensional
successor configuration. -/
noncomputable def withResult
    (cfg : G.Configuration) {node : G.Node} (slice : WriteSlice G)
    (hfrontier : node ∈ cfg.frontier)
    (hlegal : G.sliceLegal node slice) :
    G.Configuration where
  result := updateResult cfg node slice
  result_nodes := by
    classical
    intro candidate hsome
    by_cases hcandidate : candidate = node
    · subst candidate
      exact cfg.mem_nodes_of_mem_frontier hfrontier
    · have hold : (cfg.result candidate).isSome := by
        simpa [updateResult, hcandidate] using hsome
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
      · simpa [updateResult, hpreq] using hpreDone
    · have hcandidateOld : (cfg.result candidate).isSome := by
        simpa [updateResult, hcandidate] using hcandidateDone
      have hpreOld : (cfg.result prereq).isSome :=
        cfg.closed hcandidateOld hpre
      by_cases hpreq : prereq = node
      · subst prereq
        have hnodeNone : (cfg.result node).isNone :=
          cfg.not_done_of_mem_frontier hfrontier
        cases hnode : cfg.result node <;> simp [hnode] at hpreOld hnodeNone
      · simpa [updateResult, hpreq] using hpreOld
  legal := by
    classical
    intro candidate candidateSlice hcandidateResult
    by_cases hcandidate : candidate = node
    · subst candidate
      have hslice : slice = candidateSlice := by
        simpa [updateResult] using hcandidateResult
      subst candidateSlice
      exact hlegal
    · have holdResult : cfg.result candidate = some candidateSlice := by
        simpa [updateResult, hcandidate] using hcandidateResult
      exact cfg.legal holdResult

end Configuration

end ProtocolGraph

end Vegas
