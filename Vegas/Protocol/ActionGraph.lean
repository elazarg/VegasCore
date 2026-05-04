import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Math.BoundedLists

/-!
# Protocol action graphs

This module defines the proof-carrying Lean version of the action-DAG/frontier
abstractions used by the Kotlin prototype in `../vegas`: action metadata,
dependency reachability, frontier execution, redacted history, and the local
validation facts needed by compiler-preservation certificates. Backend-oriented
action DAGs can elaborate to this structure when they can supply the required
evidence.

Strategic claims should be proved for the executable machine denoted by
`ActionGraph.Semantics.toMachine`. This file defines the graph language, its
local invariants, and frontier-resolution structure; the actual machine
constructor lives in `Vegas.Protocol.Machine` to avoid an import cycle.
-/

namespace Vegas

/-- Visibility classification of a field write in a protocol action. -/
inductive Visibility where
  | commit
  | reveal
  | pub
  deriving DecidableEq, Repr

/-- Coarse action kind derived from the visibility of the fields it writes. -/
inductive ActionKind where
  | commit
  | reveal
  | pub
  | mixed
  deriving DecidableEq, Repr

/-- Fine-grained phase used by the visibility-expanded scheduling view. -/
inductive Phase where
  | commitEvent
  | choice
  | revealEvent
  deriving DecidableEq, Repr

/-- A node in the phase-expanded scheduling view of an action graph. -/
structure PhaseNode (Action : Type) where
  action : Action
  phase : Phase
  deriving DecidableEq, Repr

/-- Kotlin-style action identifier: a role/owner coordinate plus a source
index. The generic `ActionGraph` below does not require this concrete action
type, but frontends and backends that use the prototype's convention can share
this carrier directly. -/
structure ActionId (Player : Type) where
  owner : Player
  index : Nat
  deriving DecidableEq, Repr

/-- A typed action parameter. The name/type spaces are kept generic so the
carrier can be used both by Vegas syntax and by backend IRs. -/
structure ActionParam (Name Ty : Type) where
  name : Name
  ty : Ty
  deriving Repr

/-- Semantic payload attached to an action. `guard` is intentionally abstract:
the carrier records where guards live and what fields they read, while concrete
languages provide evaluation in their elaboration data. -/
structure ActionSpec (Param Guard Join : Type) where
  params : List Param
  join : Option Join
  guard : Guard
  deriving Repr

/-- Structural action metadata: who performs the action, what fields it writes,
how those writes are exposed, and which fields its guard reads.

`owner = none` covers nature/internal actions. Strategic actions normally use
`some who`. -/
structure ActionStruct (Player Field : Type) [DecidableEq Field] where
  owner : Option Player
  writes : Finset Field
  visibility : Field → Visibility
  guardReads : Finset Field

namespace ActionStruct

variable {Player Field : Type} [DecidableEq Field]

/-- Fields written with a particular visibility. -/
def fieldsWithVisibility (s : ActionStruct Player Field)
    (visibility : Visibility) : Finset Field :=
  s.writes.filter (fun field => s.visibility field = visibility)

@[simp] theorem mem_fieldsWithVisibility_iff
    (s : ActionStruct Player Field) (visibility : Visibility) (field : Field) :
    field ∈ s.fieldsWithVisibility visibility ↔
      field ∈ s.writes ∧ s.visibility field = visibility := by
  simp [fieldsWithVisibility]

/-- Fields committed by this action. -/
def commitFields (s : ActionStruct Player Field) : Finset Field :=
  s.fieldsWithVisibility .commit

/-- Fields revealed by this action. -/
def revealFields (s : ActionStruct Player Field) : Finset Field :=
  s.fieldsWithVisibility .reveal

/-- Fields written publicly by this action. -/
def publicFields (s : ActionStruct Player Field) : Finset Field :=
  s.fieldsWithVisibility .pub

/-- Coarse action kind inferred from structural write visibility. -/
def kind (s : ActionStruct Player Field) : ActionKind :=
  if s.commitFields.Nonempty then
    if s.revealFields.Nonempty then .mixed else .commit
  else if s.revealFields.Nonempty then
    .reveal
  else
    .pub

end ActionStruct

/-- Full per-action metadata in the prototype shape. `ActionGraph` stores this
data in projected fields for proof convenience; `ActionGraph.meta` reconstructs
this view. -/
structure ActionMeta
    (Action Player Field Param Guard Join : Type) [DecidableEq Field] where
  id : Action
  spec : ActionSpec Param Guard Join
  struct : ActionStruct Player Field

namespace ActionMeta

variable {Action Player Field Param Guard Join : Type} [DecidableEq Field]

/-- Coarse action kind inferred from metadata. -/
def kind (m : ActionMeta Action Player Field Param Guard Join) : ActionKind :=
  m.struct.kind

end ActionMeta

/-- Values stored in the protocol history before player-specific redaction. -/
inductive StoredValue (Value : Type) where
  | clear (value : Value)
  | hidden (value : Value)
  | quit
  deriving DecidableEq, Repr

/-- Values visible to one player after redacting a stored history. -/
inductive ObservedValue (Value : Type) where
  | value (value : Value)
  | opaque
  | quit
  deriving DecidableEq, Repr

namespace StoredValue

variable {Value : Type}

noncomputable instance instFintype [DecidableEq Value] [Fintype Value] :
    Fintype (StoredValue Value) := by
  classical
  refine Fintype.mk
    (((Finset.univ : Finset Value).image StoredValue.clear) ∪
      ((Finset.univ : Finset Value).image StoredValue.hidden) ∪
        {StoredValue.quit}) ?_
  intro value
  cases value with
  | clear value =>
      simp
  | hidden value =>
      simp
  | quit =>
      simp

/-- Redact one stored value for a player. Own hidden values are visible; hidden
values owned by others become `opaque`. -/
def redact (sameOwner : Bool) : StoredValue Value → ObservedValue Value
  | .clear value => .value value
  | .hidden value => if sameOwner then .value value else .opaque
  | .quit => .quit

@[simp] theorem redact_clear (sameOwner : Bool) (value : Value) :
    redact sameOwner (.clear value) = .value value := rfl

@[simp] theorem redact_hidden_true (value : Value) :
    redact true (.hidden value) = .value value := rfl

@[simp] theorem redact_hidden_false (value : Value) :
    redact false (.hidden value) = .opaque := rfl

@[simp] theorem redact_quit (sameOwner : Bool) :
    redact sameOwner (.quit : StoredValue Value) = .quit := rfl

end StoredValue

namespace ObservedValue

variable {Value : Type}

noncomputable instance instFintype [DecidableEq Value] [Fintype Value] :
    Fintype (ObservedValue Value) := by
  classical
  refine Fintype.mk
    (((Finset.univ : Finset Value).image ObservedValue.value) ∪
        {ObservedValue.opaque} ∪ {ObservedValue.quit}) ?_
  intro value
  cases value <;> simp

end ObservedValue

/-- A frontier/history slice: a partial field assignment represented as a
lookup function. -/
abbrev Slice (Field Value : Type) : Type := Field → Option Value

/-- A protocol history is a stack of frontier slices. The head is the newest
slice. -/
abbrev History (Field Value : Type) : Type := List (Slice Field Value)

namespace History

variable {Field Value Value' Player : Type}

/-- Lookup a field in a history stack, returning the newest assignment if one
exists. -/
def lookup : History Field Value → Field → Option Value
  | [], _ => none
  | slice :: rest, field =>
      match slice field with
      | some value => some value
      | none => lookup rest field

/-- Map a slice, allowing the map to depend on the field being read. -/
def mapSliceWithField (f : Field → Value → Value')
    (slice : Slice Field Value) : Slice Field Value' :=
  fun field => Option.map (f field) (slice field)

/-- Map a history, allowing the value map to depend on the field being read. -/
def mapWithField (f : Field → Value → Value')
    (history : History Field Value) : History Field Value' :=
  history.map (mapSliceWithField f)

/-- Merge a frontier delta into an existing slice. Values from `delta` take
precedence. This is the functional version of the prototype's disjoint map
union; disjointness is stated separately when a frontend needs it. -/
def mergeSlice (base delta : Slice Field Value) : Slice Field Value :=
  fun field =>
    match delta field with
    | some value => some value
    | none => base field

/-- Push a frontier slice onto the history stack. -/
def push (history : History Field Value) (slice : Slice Field Value) :
    History Field Value :=
  slice :: history

/-- Two slices have no overlapping assigned fields. This is the invariant
under which `mergeSlice` is the prototype's disjoint frontier union. -/
def SlicesDisjoint (left right : Slice Field Value) : Prop :=
  ∀ {field leftValue rightValue},
    left field = some leftValue → right field = some rightValue → False

theorem mergeSlice_eq_base_of_delta_none
    (base delta : Slice Field Value) {field : Field}
    (hdelta : delta field = none) :
    mergeSlice base delta field = base field := by
  simp [mergeSlice, hdelta]

theorem mergeSlice_eq_delta_of_delta_some
    (base delta : Slice Field Value) {field : Field} {value : Value}
    (hdelta : delta field = some value) :
    mergeSlice base delta field = some value := by
  simp [mergeSlice, hdelta]

/-- Lookup commutes with field-dependent history mapping. -/
theorem lookup_mapWithField (f : Field → Value → Value')
    (history : History Field Value) (field : Field) :
    lookup (mapWithField f history) field =
      Option.map (f field) (lookup history field) := by
  induction history with
  | nil =>
      rfl
  | cons slice rest ih =>
      cases h : slice field with
      | none =>
          simpa [lookup, mapWithField, mapSliceWithField, h] using ih
      | some value =>
          simp [lookup, mapWithField, mapSliceWithField, h]

/-- Redact an actual history into one player's observed history. -/
def redact [DecidableEq Player]
    (fieldOwner : Field → Player) (who : Player)
    (history : History Field (StoredValue Value)) :
    History Field (ObservedValue Value) :=
  mapWithField
    (fun field value => StoredValue.redact (decide (fieldOwner field = who)) value)
    history

/-- Looking up a field after redaction is the same as looking it up first and
then redacting the stored value for that field. -/
theorem lookup_redact [DecidableEq Player]
    (fieldOwner : Field → Player) (who : Player)
    (history : History Field (StoredValue Value)) (field : Field) :
    lookup (redact fieldOwner who history) field =
      Option.map
        (fun value => StoredValue.redact (decide (fieldOwner field = who)) value)
        (lookup history field) := by
  exact lookup_mapWithField
    (fun field value => StoredValue.redact (decide (fieldOwner field = who)) value)
    history field

/-- A player has quit if some historical slice stores `quit` in one of their
fields. This mirrors the prototype's `History.quit`. -/
def quit [DecidableEq Player]
    (fieldOwner : Field → Option Player) (who : Player)
    (history : History Field (StoredValue Value)) : Prop :=
  ∃ slice ∈ history, ∃ field,
    fieldOwner field = some who ∧ slice field = some StoredValue.quit

/-- Redact one stored slice for a player. -/
def redactSlice [DecidableEq Player]
    (fieldOwner : Field → Option Player) (who : Player)
    (slice : Slice Field (StoredValue Value)) :
    Slice Field (ObservedValue Value) :=
  mapSliceWithField
    (fun field value =>
      StoredValue.redact (decide (fieldOwner field = some who)) value)
    slice

/-- Reconstruct one player's perfect-recall view of a global history. -/
def playerView [DecidableEq Player]
    (fieldOwner : Field → Option Player) (who : Player)
    (history : History Field (StoredValue Value)) :
    History Field (ObservedValue Value) :=
  mapWithField
    (fun field value =>
      StoredValue.redact (decide (fieldOwner field = some who)) value)
    history

end History

/-- Raw observation predicate used inside the `ActionGraph` structure before
the graph-specific namespace is available. A player can observe a field write
if the field belongs to them, or if the write is public/revealed. -/
def CanObserveWriteData {Player Action Field : Type}
    (fieldOwner : Field → Option Player)
    (visibility : Action → Field → Visibility)
    (who : Player) (src : Action) (field : Field) : Prop :=
  fieldOwner field = some who ∨
    visibility src field = .pub ∨
    visibility src field = .reveal

/-- A finite action graph with enough semantic metadata to generate a
frontier-style protocol machine.

`rank` is an executable acyclicity certificate: every prerequisite must have
strictly smaller rank than the action that depends on it.

The guard-read invariant is reachability- and observation-aware. It says that
any field read by an action guard belongs to an action with a player actor and
is written by an earlier action whose write is visible to that actor. Public
and nature actions can have `actor = none`; guarded strategic actions should
have `actor = some who`. -/
structure ActionGraph
    (Player Action Field Param Guard Join : Type)
    [DecidableEq Action] [DecidableEq Field] where
  actions : Finset Action
  initialFields : Finset Field
  spec : Action → ActionSpec Param Guard Join
  actor : Action → Option Player
  fieldOwner : Field → Option Player
  prereqs : Action → Finset Action
  writes : Action → Finset Field
  visibility : Action → Field → Visibility
  guardReads : Action → Finset Field
  rank : Action → Nat
  precedes : Action → Action → Prop
  predecessors : Action → Finset Action
  prereq_precedes :
    ∀ {action prereq},
      action ∈ actions → prereq ∈ prereqs action → precedes prereq action
  precedes_left_mem :
    ∀ {src dst}, precedes src dst → src ∈ actions
  precedes_right_mem :
    ∀ {src dst}, precedes src dst → dst ∈ actions
  precedes_iff_mem_predecessors :
    ∀ {src dst}, precedes src dst ↔ src ∈ predecessors dst
  precedes_rank_lt :
    ∀ {src dst}, precedes src dst → rank src < rank dst
  precedes_trans :
    ∀ {src mid dst}, precedes src mid → precedes mid dst → precedes src dst
  commit_writes_owned :
    ∀ {action field},
      action ∈ actions → field ∈ writes action →
        visibility action field = .commit →
          ∃ who, actor action = some who ∧ fieldOwner field = some who
  guardReads_observable_from_prior :
    ∀ {action field},
      action ∈ actions → field ∈ guardReads action →
        ∃ who,
          actor action = some who ∧
          ((field ∈ initialFields ∧
              (fieldOwner field = none ∨ fieldOwner field = some who)) ∨
            ∃ prior,
              prior ∈ actions ∧
              precedes prior action ∧
              field ∈ writes prior ∧
              CanObserveWriteData fieldOwner visibility who prior field)
  reveal_has_prior_commit :
    ∀ {action field},
      action ∈ actions → field ∈ writes action →
        visibility action field = .reveal →
          ∃ commitAction,
            commitAction ∈ actions ∧
            precedes commitAction action ∧
            field ∈ writes commitAction ∧
            visibility commitAction field = .commit

namespace ActionGraph

variable {Player Action Field Param Guard Join : Type}
variable [DecidableEq Action] [DecidableEq Field]

/-- Reachability is decidable because it is represented by a finite predecessor
set. -/
instance instDecidablePrecedes
    (G : ActionGraph Player Action Field Param Guard Join) :
    DecidableRel G.precedes := by
  intro src dst
  rw [G.precedes_iff_mem_predecessors]
  infer_instance

/-- Immediate prerequisites are graph actions. This is derived from the
reachability witness rather than stored redundantly in the carrier. -/
theorem prereqs_subset_actions
    (G : ActionGraph Player Action Field Param Guard Join)
    {action prereq : Action}
    (haction : action ∈ G.actions)
    (hprereq : prereq ∈ G.prereqs action) :
    prereq ∈ G.actions :=
  G.precedes_left_mem (G.prereq_precedes haction hprereq)

/-- Immediate prerequisites have smaller rank. This follows from the
reachability rank certificate. -/
theorem prereq_rank_lt
    (G : ActionGraph Player Action Field Param Guard Join)
    {action prereq : Action}
    (haction : action ∈ G.actions)
    (hprereq : prereq ∈ G.prereqs action) :
    G.rank prereq < G.rank action :=
  G.precedes_rank_lt (G.prereq_precedes haction hprereq)

/-- A write by `src` is observable by `who` when it writes `who`'s field, or
when the write is public/revealed. -/
def CanObserveWrite (G : ActionGraph Player Action Field Param Guard Join)
    (who : Player) (src : Action) (field : Field) : Prop :=
  CanObserveWriteData G.fieldOwner G.visibility who src field

/-- Fields written by an action with a particular visibility. -/
def fieldsWithVisibility (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) (visibility : Visibility) : Finset Field :=
  G.writes action |>.filter (fun field => G.visibility action field = visibility)

@[simp] theorem mem_fieldsWithVisibility_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) (visibility : Visibility) (field : Field) :
    field ∈ G.fieldsWithVisibility action visibility ↔
      field ∈ G.writes action ∧ G.visibility action field = visibility := by
  simp [fieldsWithVisibility]

/-- Whether an action has at least one write with a given visibility. -/
def HasWriteVisibility (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) (visibility : Visibility) : Prop :=
  ∃ field, field ∈ G.writes action ∧ G.visibility action field = visibility

instance instDecidableHasWriteVisibility
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) (visibility : Visibility) :
    Decidable (G.HasWriteVisibility action visibility) := by
  dsimp [HasWriteVisibility]
  infer_instance

/-- Coarse action kind derived from write visibility.

Mixed commit/reveal actions are left explicit as `mixed`; transformations that
need pure commit or pure reveal actions should require that shape rather than
silently treating mixed nodes as public. -/
def kind (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : ActionKind :=
  if G.HasWriteVisibility action .commit then
    if G.HasWriteVisibility action .reveal then .mixed else .commit
  else if G.HasWriteVisibility action .reveal then
    .reveal
  else
    .pub

/-- Prototype-shaped structural metadata for one graph action. -/
def struct (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : ActionStruct Player Field where
  owner := G.actor action
  writes := G.writes action
  visibility := G.visibility action
  guardReads := G.guardReads action

/-- Prototype-shaped full metadata for one graph action. -/
def metadata (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : ActionMeta Action Player Field Param Guard Join where
  id := action
  spec := G.spec action
  struct := G.struct action

@[simp] theorem meta_id
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    (G.metadata action).id = action := rfl

@[simp] theorem meta_spec
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    (G.metadata action).spec = G.spec action := rfl

@[simp] theorem meta_struct
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    (G.metadata action).struct = G.struct action := rfl

@[simp] theorem struct_owner
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    (G.struct action).owner = G.actor action := rfl

@[simp] theorem struct_writes
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    (G.struct action).writes = G.writes action := rfl

@[simp] theorem struct_guardReads
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    (G.struct action).guardReads = G.guardReads action := rfl

@[simp] theorem struct_visibility
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) (field : Field) :
    (G.struct action).visibility field = G.visibility action field := rfl

/-- Immediate dependents of an action. -/
def dependentsOf (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : Finset Action :=
  G.actions.filter (fun dst => action ∈ G.prereqs dst)

@[simp] theorem mem_dependentsOf_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    (action dst : Action) :
    dst ∈ G.dependentsOf action ↔
      dst ∈ G.actions ∧ action ∈ G.prereqs dst := by
  simp [dependentsOf]

/-- Ancestors of an action, using the precomputed predecessor set carried by
the proof object. -/
def ancestorsOf (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : Finset Action :=
  G.predecessors action

/-- Descendants of an action. -/
def descendantsOf (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : Finset Action :=
  G.actions.filter (fun dst => G.precedes action dst)

@[simp] theorem mem_descendantsOf_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    (action dst : Action) :
    dst ∈ G.descendantsOf action ↔
      dst ∈ G.actions ∧ G.precedes action dst := by
  simp [descendantsOf]

/-- Kotlin-name reachability query: `reaches a b` means `a` semantically
precedes `b`. -/
def reaches (G : ActionGraph Player Action Field Param Guard Join)
    (src dst : Action) : Prop :=
  G.precedes src dst

/-- Two actions are comparable when either can reach the other. -/
def comparable (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) : Prop :=
  G.reaches left right ∨ G.reaches right left

/-- Kotlin-name concurrency query. This includes graph membership. -/
def canExecuteConcurrently
    (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) : Prop :=
  left ∈ G.actions ∧
    right ∈ G.actions ∧
    left ≠ right ∧
    ¬ G.comparable left right

/-- Sink actions: graph actions with no immediate dependents. -/
def sinks (G : ActionGraph Player Action Field Param Guard Join) :
    Finset Action :=
  G.actions.filter (fun action => G.dependentsOf action = ∅)

@[simp] theorem mem_sinks_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    action ∈ G.sinks ↔
      action ∈ G.actions ∧ G.dependentsOf action = ∅ := by
  simp [sinks]

/-- Fields observable by the owner of `targetAction` at that action from prior
graph writes. Initial fields are handled by `ObservableFieldAfter`; this is the
prototype's `observableFieldsAt` query over action metadata. It is stated as a
set because field domains need not be globally finite. -/
def observableFieldsAt (G : ActionGraph Player Action Field Param Guard Join)
    (targetAction : Action) : Set Field :=
  { field |
    ∃ who src,
      G.actor targetAction = some who ∧
      src ∈ G.actions ∧
      G.precedes src targetAction ∧
      field ∈ G.writes src ∧
      G.CanObserveWrite who src field }

theorem mem_observableFieldsAt_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    {targetAction : Action} {field : Field} :
    field ∈ G.observableFieldsAt targetAction ↔
      ∃ who src,
        G.actor targetAction = some who ∧
        src ∈ G.actions ∧
        G.precedes src targetAction ∧
        field ∈ G.writes src ∧
        G.CanObserveWrite who src field := Iff.rfl

/-- Static commit/reveal ordering validator, in the prototype shape. -/
def CommitRevealOrderingValid
    (G : ActionGraph Player Action Field Param Guard Join) : Prop :=
  ∀ {action field},
    action ∈ G.actions → field ∈ G.writes action →
      G.visibility action field = .reveal →
        ∃ commitAction,
          commitAction ∈ G.actions ∧
          G.precedes commitAction action ∧
          field ∈ G.writes commitAction ∧
          G.visibility commitAction field = .commit

theorem commitRevealOrderingValid
    (G : ActionGraph Player Action Field Param Guard Join) :
    G.CommitRevealOrderingValid := by
  intro action field haction hwrite hvis
  exact G.reveal_has_prior_commit haction hwrite hvis

/-- Static guard-read visibility validator, in the prototype shape. -/
def VisibilityOnReadsValid
    (G : ActionGraph Player Action Field Param Guard Join) : Prop :=
  ∀ {action field},
    action ∈ G.actions → field ∈ G.guardReads action →
      ∃ who,
        G.actor action = some who ∧
        ((field ∈ G.initialFields ∧
            (G.fieldOwner field = none ∨ G.fieldOwner field = some who)) ∨
          field ∈ G.observableFieldsAt action)

theorem visibilityOnReadsValid
    (G : ActionGraph Player Action Field Param Guard Join) :
    G.VisibilityOnReadsValid := by
  intro action field haction hfield
  rcases G.guardReads_observable_from_prior haction hfield with
    ⟨who, hactor, hinitial | hprior⟩
  · exact ⟨who, hactor, Or.inl hinitial⟩
  · rcases hprior with ⟨prior, hprior_action, hpre, hwrite, hobs⟩
    exact ⟨who, hactor, Or.inr ((G.mem_observableFieldsAt_iff).mpr
      ⟨who, prior, hactor, hprior_action, hpre, hwrite, hobs⟩)⟩

theorem canObserveWrite_of_fieldOwner
    (G : ActionGraph Player Action Field Param Guard Join)
    {who : Player} {src : Action} {field : Field}
    (h : G.fieldOwner field = some who) :
    G.CanObserveWrite who src field := by
  exact Or.inl h

theorem canObserveWrite_of_commit_actor_of_write
    (G : ActionGraph Player Action Field Param Guard Join)
    {who : Player} {src : Action} {field : Field}
    (hsrc : src ∈ G.actions)
    (hwrite : field ∈ G.writes src)
    (hvis : G.visibility src field = .commit)
    (hactor : G.actor src = some who) :
    G.CanObserveWrite who src field := by
  rcases G.commit_writes_owned hsrc hwrite hvis with ⟨owner, hactor', hfield⟩
  have howner : owner = who := by
    exact Option.some.inj (hactor'.symm.trans hactor)
  subst howner
  exact G.canObserveWrite_of_fieldOwner hfield

theorem canObserveWrite_of_public
    (G : ActionGraph Player Action Field Param Guard Join)
    {who : Player} {src : Action} {field : Field}
    (h : G.visibility src field = .pub) :
    G.CanObserveWrite who src field := by
  exact Or.inr (Or.inl h)

theorem canObserveWrite_of_reveal
    (G : ActionGraph Player Action Field Param Guard Join)
    {who : Player} {src : Action} {field : Field}
    (h : G.visibility src field = .reveal) :
    G.CanObserveWrite who src field := by
  exact Or.inr (Or.inr h)

/-- An action is ready at `done` when it belongs to the graph, has not already
been resolved, and all semantically preceding actions are done.  This uses the
graph's reachability certificate, not merely the immediate predecessor list. -/
def Ready (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) (action : Action) : Prop :=
  action ∈ G.actions ∧ action ∉ done ∧
    G.predecessors action ⊆ done

instance instDecidableReady (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) (action : Action) :
    Decidable (G.Ready done action) := by
  dsimp [Ready]
  infer_instance

/-- The current frontier: all ready actions. -/
def frontier (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) : Finset Action :=
  G.actions.filter (fun action => G.Ready done action)

@[simp] theorem mem_frontier_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) (action : Action) :
    action ∈ G.frontier done ↔ G.Ready done action := by
  simp [frontier, Ready]

theorem mem_actions_of_mem_frontier
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action}
    (h : action ∈ G.frontier done) :
    action ∈ G.actions :=
  (G.mem_frontier_iff done action).mp h |>.1

theorem not_mem_done_of_mem_frontier
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action}
    (h : action ∈ G.frontier done) :
    action ∉ done :=
  (G.mem_frontier_iff done action).mp h |>.2.1

theorem prereqs_subset_done_of_mem_frontier
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action}
    (h : action ∈ G.frontier done) :
    G.prereqs action ⊆ done :=
  by
    intro prereq hpre
    have hready := (G.mem_frontier_iff done action).mp h
    exact hready.2.2
      ((G.precedes_iff_mem_predecessors).mp
        (G.prereq_precedes hready.1 hpre))

theorem predecessors_done_of_mem_frontier
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action prior : Action}
    (h : action ∈ G.frontier done)
    (hprior : G.precedes prior action) :
    prior ∈ done :=
  (G.mem_frontier_iff done action).mp h |>.2.2
    ((G.precedes_iff_mem_predecessors).mp hprior)

theorem frontier_subset_actions
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    G.frontier done ⊆ G.actions := by
  intro action h
  exact G.mem_actions_of_mem_frontier h

/-- All graph actions have been resolved at a done set. Extra non-graph
actions in `done` are ignored. -/
def CompleteAt (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) : Prop :=
  G.actions ⊆ done

theorem not_completeAt_iff_exists_unfinished
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    ¬ G.CompleteAt done ↔
      ∃ action, action ∈ G.actions ∧ action ∉ done := by
  constructor
  · intro hcomplete
    by_contra hnone
    apply hcomplete
    intro action haction
    by_contra hnot_done
    exact hnone ⟨action, haction, hnot_done⟩
  · rintro ⟨action, haction, hnot_done⟩ hcomplete
    exact hnot_done (hcomplete haction)

/-- If the graph is not complete, some unfinished action is ready. This is the
finite-DAG progress fact behind frontier execution. -/
theorem exists_ready_of_not_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hcomplete : ¬ G.CompleteAt done) :
    ∃ action, G.Ready done action := by
  rcases (G.not_completeAt_iff_exists_unfinished done).mp hcomplete with
    ⟨witness, hwitness_action, hwitness_not_done⟩
  let unfinished : Finset Action :=
    G.actions.filter (fun action => action ∉ done)
  have hunfinished_nonempty : unfinished.Nonempty := by
    refine ⟨witness, ?_⟩
    simp [unfinished, hwitness_action, hwitness_not_done]
  rcases Finset.exists_min_image unfinished G.rank hunfinished_nonempty with
    ⟨action, haction_unfinished, hmin⟩
  have haction : action ∈ G.actions :=
    (Finset.mem_filter.mp haction_unfinished).1
  have hnot_done : action ∉ done :=
    (Finset.mem_filter.mp haction_unfinished).2
  refine ⟨action, ⟨haction, hnot_done, ?_⟩⟩
  intro prior hprior_mem
  by_contra hprior_not_done
  have hprior : G.precedes prior action :=
    (G.precedes_iff_mem_predecessors).mpr hprior_mem
  have hle : G.rank action ≤ G.rank prior :=
    hmin prior
      (by
        simp [unfinished, G.precedes_left_mem hprior, hprior_not_done])
  exact (Nat.not_lt_of_ge hle) (G.precedes_rank_lt hprior)

/-- A non-complete graph has a nonempty current frontier. -/
theorem frontier_nonempty_of_not_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hcomplete : ¬ G.CompleteAt done) :
    (G.frontier done).Nonempty := by
  rcases G.exists_ready_of_not_completeAt hcomplete with ⟨action, hready⟩
  exact ⟨action, (G.mem_frontier_iff done action).mpr hready⟩

/-- If the current frontier is empty, all graph actions are complete. -/
theorem completeAt_of_frontier_eq_empty
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hfrontier : G.frontier done = ∅) :
    G.CompleteAt done := by
  by_contra hcomplete
  rcases G.frontier_nonempty_of_not_completeAt hcomplete with ⟨action, haction⟩
  rw [hfrontier] at haction
  simp at haction

theorem frontier_eq_empty_iff_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    G.frontier done = ∅ ↔ G.CompleteAt done := by
  constructor
  · exact G.completeAt_of_frontier_eq_empty
  · intro hcomplete
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hfrontier
    exact G.not_mem_done_of_mem_frontier hfrontier
      (hcomplete (G.mem_actions_of_mem_frontier hfrontier))

/-- Resolve the current frontier by adding every ready action to `done`. -/
def advance (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) : Finset Action :=
  done ∪ G.frontier done

theorem done_subset_advance
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    done ⊆ G.advance done := by
  intro action h
  simp [advance, h]

theorem frontier_subset_advance
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    G.frontier done ⊆ G.advance done := by
  intro action h
  simp [advance, h]

theorem advance_subset_actions
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hdone : done ⊆ G.actions) :
    G.advance done ⊆ G.actions := by
  intro action h
  rcases Finset.mem_union.mp h with hdone_action | hfrontier
  · exact hdone hdone_action
  · exact G.mem_actions_of_mem_frontier hfrontier

theorem advance_eq_done_iff_frontier_eq_empty
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    G.advance done = done ↔ G.frontier done = ∅ := by
  constructor
  · intro hadvance
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hfrontier
    have hdone : action ∈ done := by
      have hmem_advance : action ∈ G.advance done := by
        exact G.frontier_subset_advance done hfrontier
      simpa [hadvance] using hmem_advance
    exact G.not_mem_done_of_mem_frontier hfrontier hdone
  · intro hfrontier
    simp [advance, hfrontier]

theorem advance_eq_done_iff_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    G.advance done = done ↔ G.CompleteAt done := by
  rw [G.advance_eq_done_iff_frontier_eq_empty,
    G.frontier_eq_empty_iff_completeAt]

theorem advance_ne_done_of_not_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hcomplete : ¬ G.CompleteAt done) :
    G.advance done ≠ done := by
  intro hadvance
  exact hcomplete ((G.advance_eq_done_iff_completeAt done).mp hadvance)

/-- If the graph is incomplete, advancing exposes at least one action that was
not already done. -/
theorem exists_mem_advance_not_mem_done_of_not_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hcomplete : ¬ G.CompleteAt done) :
    ∃ action, action ∈ G.advance done ∧ action ∉ done := by
  rcases G.frontier_nonempty_of_not_completeAt hcomplete with
    ⟨action, hfrontier⟩
  exact ⟨action, G.frontier_subset_advance done hfrontier,
    G.not_mem_done_of_mem_frontier hfrontier⟩

/-- Frontier advancement strictly grows the done set until graph completion.
This is the finite progress fact behind executable frontier iteration. -/
theorem done_ssubset_advance_of_not_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hcomplete : ¬ G.CompleteAt done) :
    done ⊂ G.advance done := by
  constructor
  · exact G.done_subset_advance done
  · intro hsub
    have heq : G.advance done = done := by
      apply Finset.Subset.antisymm hsub
      exact G.done_subset_advance done
    exact G.advance_ne_done_of_not_completeAt hcomplete heq

/-- The number of done actions strictly increases on each incomplete frontier
advance. -/
theorem card_done_lt_card_advance_of_not_completeAt
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hcomplete : ¬ G.CompleteAt done) :
    done.card < (G.advance done).card := by
  exact Finset.card_lt_card
    (G.done_ssubset_advance_of_not_completeAt hcomplete)

/-- Frontier advancement remains bounded by the finite action set whenever the
current done set is. -/
theorem card_advance_le_card_actions
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action}
    (hdone : done ⊆ G.actions) :
    (G.advance done).card ≤ G.actions.card := by
  exact Finset.card_le_card (G.advance_subset_actions hdone)

theorem frontier_disjoint_done
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    Disjoint (G.frontier done) done := by
  rw [Finset.disjoint_left]
  intro action hfrontier hdone
  exact G.not_mem_done_of_mem_frontier hfrontier hdone

theorem prereq_rank_lt_of_mem
    (G : ActionGraph Player Action Field Param Guard Join)
    {action prereq : Action}
    (haction : action ∈ G.actions)
    (hprereq : prereq ∈ G.prereqs action) :
    G.rank prereq < G.rank action :=
  G.prereq_rank_lt haction hprereq

/-- The reachability relation is irreflexive on actions. -/
theorem not_precedes_self
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    ¬ G.precedes action action := by
  intro h
  exact (Nat.lt_irrefl (G.rank action)) (G.precedes_rank_lt h)

/-- A predecessor is distinct from its successor. -/
theorem ne_of_precedes
    (G : ActionGraph Player Action Field Param Guard Join)
    {src dst : Action}
    (h : G.precedes src dst) :
    src ≠ dst := by
  intro heq
  exact (Nat.lt_irrefl (G.rank src)) (by
    simpa [heq] using G.precedes_rank_lt h)

/-- Reachability is asymmetric as a consequence of the rank certificate. -/
theorem not_precedes_of_precedes_reverse
    (G : ActionGraph Player Action Field Param Guard Join)
    {src dst : Action}
    (h : G.precedes src dst) :
    ¬ G.precedes dst src := by
  intro hrev
  exact Nat.lt_asymm (G.precedes_rank_lt h) (G.precedes_rank_lt hrev)

/-- Two actions are graph-concurrent when both are in the graph and neither
semantically precedes the other. This is only a structural/scheduling fact; it
does not by itself assert strategic equivalence of any transformation. -/
def Concurrent (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) : Prop :=
  left ∈ G.actions ∧
    right ∈ G.actions ∧
    left ≠ right ∧
    ¬ G.precedes left right ∧
    ¬ G.precedes right left

instance instDecidableConcurrent
    (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) :
    Decidable (G.Concurrent left right) := by
  dsimp [Concurrent]
  infer_instance

theorem concurrent_comm
    (G : ActionGraph Player Action Field Param Guard Join)
    {left right : Action} :
    G.Concurrent left right ↔ G.Concurrent right left := by
  constructor
  · intro h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩
  · intro h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩

theorem not_precedes_left_right_of_concurrent
    (G : ActionGraph Player Action Field Param Guard Join)
    {left right : Action}
    (h : G.Concurrent left right) :
    ¬ G.precedes left right :=
  h.2.2.2.1

theorem not_precedes_right_left_of_concurrent
    (G : ActionGraph Player Action Field Param Guard Join)
    {left right : Action}
    (h : G.Concurrent left right) :
    ¬ G.precedes right left :=
  h.2.2.2.2

theorem ne_of_concurrent
    (G : ActionGraph Player Action Field Param Guard Join)
    {left right : Action}
    (h : G.Concurrent left right) :
    left ≠ right :=
  h.2.2.1

theorem canExecuteConcurrently_iff_concurrent
    (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) :
    G.canExecuteConcurrently left right ↔ G.Concurrent left right := by
  simp [canExecuteConcurrently, Concurrent, comparable, reaches,
    not_or]

@[simp] theorem not_canExecuteConcurrently_self
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    ¬ G.canExecuteConcurrently action action := by
  simp [G.canExecuteConcurrently_iff_concurrent, Concurrent]

@[simp] theorem not_concurrent_self
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    ¬ G.Concurrent action action := by
  simp [Concurrent]

/-- A graph action that currently writes only public fields and has at least
one such write. This is the source shape considered by the prototype's
commit/reveal expansion pass. -/
def PurePublicAction
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : Prop :=
  action ∈ G.actions ∧
    ¬ G.HasWriteVisibility action .commit ∧
    ¬ G.HasWriteVisibility action .reveal ∧
    G.HasWriteVisibility action .pub

instance instDecidablePurePublicAction
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    Decidable (G.PurePublicAction action) := by
  dsimp [PurePublicAction]
  infer_instance

theorem kind_eq_pub_of_purePublicAction
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action}
    (h : G.PurePublicAction action) :
    G.kind action = .pub := by
  simp [kind, h.2.1, h.2.2.1]

/-- Two pure-public actions form a public concurrency risk when either can be
chosen before the other's value is fixed. This is a structural criterion only;
strategic soundness of an expansion is a separate machine/refinement theorem. -/
def PublicConcurrencyRisk
    (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) : Prop :=
  G.PurePublicAction left ∧
    G.PurePublicAction right ∧
    G.Concurrent left right

instance instDecidablePublicConcurrencyRisk
    (G : ActionGraph Player Action Field Param Guard Join)
    (left right : Action) :
    Decidable (G.PublicConcurrencyRisk left right) := by
  dsimp [PublicConcurrencyRisk]
  infer_instance

theorem publicConcurrencyRisk_comm
    (G : ActionGraph Player Action Field Param Guard Join)
    {left right : Action} :
    G.PublicConcurrencyRisk left right ↔
      G.PublicConcurrencyRisk right left := by
  constructor
  · intro h
    exact ⟨h.2.1, h.1, (G.concurrent_comm).mp h.2.2⟩
  · intro h
    exact ⟨h.2.1, h.1, (G.concurrent_comm).mp h.2.2⟩

/-- Actions that the prototype expansion pass would split into commit/reveal
nodes: pure-public actions with at least one concurrent pure-public partner. -/
def NeedsCommitRevealSplit
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) : Prop :=
  ∃ partner ∈ G.actions, G.PublicConcurrencyRisk action partner

instance instDecidableNeedsCommitRevealSplit
    (G : ActionGraph Player Action Field Param Guard Join)
    (action : Action) :
    Decidable (G.NeedsCommitRevealSplit action) := by
  dsimp [NeedsCommitRevealSplit]
  infer_instance

theorem purePublicAction_of_needsCommitRevealSplit
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action}
    (h : G.NeedsCommitRevealSplit action) :
    G.PurePublicAction action := by
  rcases h with ⟨_partner, _hpartner, hrisk⟩
  exact hrisk.1

theorem mem_actions_of_needsCommitRevealSplit
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action}
    (h : G.NeedsCommitRevealSplit action) :
    action ∈ G.actions :=
  (G.purePublicAction_of_needsCommitRevealSplit h).1

theorem exists_split_partner_of_needsCommitRevealSplit
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action}
    (h : G.NeedsCommitRevealSplit action) :
    ∃ partner,
      G.PurePublicAction partner ∧
        G.Concurrent action partner := by
  rcases h with ⟨partner, _hpartner, hrisk⟩
  exact ⟨partner, hrisk.2.1, hrisk.2.2⟩

/-- An action cannot be its own prerequisite. This is the immediate
acyclicity fact exposed by the rank certificate. -/
theorem not_mem_prereqs_self
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action}
    (haction : action ∈ G.actions) :
    action ∉ G.prereqs action := by
  intro hpre
  exact (Nat.lt_irrefl (G.rank action)) (G.prereq_rank_lt haction hpre)

theorem ne_of_mem_prereqs
    (G : ActionGraph Player Action Field Param Guard Join)
    {action prereq : Action}
    (haction : action ∈ G.actions)
    (hprereq : prereq ∈ G.prereqs action) :
    prereq ≠ action := by
  intro h
  subst h
  exact G.not_mem_prereqs_self haction hprereq

@[simp] theorem mem_advance_iff
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) (action : Action) :
    action ∈ G.advance done ↔ action ∈ done ∨ G.Ready done action := by
  simp [advance]

theorem not_mem_frontier_of_mem_done
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action}
    (hdone : action ∈ done) :
    action ∉ G.frontier done := by
  intro hfrontier
  exact G.not_mem_done_of_mem_frontier hfrontier hdone

/-- If an unfinished action has minimum rank among unfinished graph actions,
then it is ready. This is the progress lemma users need before choosing a
particular finite-minimum construction. -/
theorem ready_of_min_rank_not_done
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action}
    (haction : action ∈ G.actions)
    (hnotdone : action ∉ done)
    (hmin :
      ∀ {other : Action},
        other ∈ G.actions → other ∉ done → G.rank action ≤ G.rank other) :
    G.Ready done action := by
  refine ⟨haction, hnotdone, ?_⟩
  intro prior hprior_mem
  by_contra hprior_not_done
  have hprior : G.precedes prior action :=
    (G.precedes_iff_mem_predecessors).mpr hprior_mem
  have hle : G.rank action ≤ G.rank prior :=
    hmin (G.precedes_left_mem hprior) hprior_not_done
  exact (Nat.not_lt_of_ge hle) (G.precedes_rank_lt hprior)

/-! ## Frontier-machine views

The graph-level executable order is frontier resolution: resolve all currently
ready actions as one layer, then compute the next frontier. Transaction order,
FOSG node order, or trace serialization may refine a frontier into a linear
presentation, but that scheduler is not part of `ActionGraph`.
-/

/-- Frontier machine state for an action graph.

This is the Lean port of the prototype `FrontierMachine<T>` with the redundant
runtime caches removed. The enabled set and unresolved set are computed from
the proof-carrying graph and `done`; resolving enabled actions is exactly
`ActionGraph.advance`. -/
structure FrontierMachine (G : ActionGraph Player Action Field Param Guard Join) where
  done : Finset Action
  done_subset_actions : done ⊆ G.actions

namespace FrontierMachine

variable {G : ActionGraph Player Action Field Param Guard Join}

@[ext] theorem ext
    {left right : G.FrontierMachine}
    (hdone : left.done = right.done) :
    left = right := by
  cases left
  cases right
  cases hdone
  rfl

/-- Initial frontier machine: no actions have been resolved. -/
def initial (G : ActionGraph Player Action Field Param Guard Join) :
    G.FrontierMachine where
  done := ∅
  done_subset_actions := by intro action h; simp at h

/-- Currently enabled actions. -/
def enabled (m : G.FrontierMachine) : Finset Action :=
  G.frontier m.done

/-- Actions not yet resolved. -/
def unresolved (m : G.FrontierMachine) : Finset Action :=
  G.actions \ m.done

/-- All graph actions have been resolved. -/
def isComplete (m : G.FrontierMachine) : Prop :=
  G.CompleteAt m.done

/-- Resolve all enabled actions and move to the next frontier. -/
def resolveEnabled (m : G.FrontierMachine) : G.FrontierMachine where
  done := G.advance m.done
  done_subset_actions := G.advance_subset_actions m.done_subset_actions

@[simp] theorem initial_done
    (G : ActionGraph Player Action Field Param Guard Join) :
    (initial G).done = ∅ := rfl

@[simp] theorem enabled_eq_frontier (m : G.FrontierMachine) :
    m.enabled = G.frontier m.done := rfl

@[simp] theorem resolveEnabled_done (m : G.FrontierMachine) :
    m.resolveEnabled.done = G.advance m.done := rfl

theorem enabled_nonempty_of_not_complete
    (m : G.FrontierMachine) (hcomplete : ¬ m.isComplete) :
    m.enabled.Nonempty := by
  exact G.frontier_nonempty_of_not_completeAt hcomplete

theorem resolveEnabled_done_ssubset
    (m : G.FrontierMachine) (hcomplete : ¬ m.isComplete) :
    m.done ⊂ m.resolveEnabled.done := by
  exact G.done_ssubset_advance_of_not_completeAt hcomplete

theorem resolveEnabled_complete_iff (m : G.FrontierMachine) :
    m.resolveEnabled.done = m.done ↔ m.isComplete := by
  exact G.advance_eq_done_iff_completeAt m.done

/-- Finite enumeration of frontier states over a finite action carrier. -/
noncomputable def finset
    (G : ActionGraph Player Action Field Param Guard Join)
    [Fintype Action] : Finset G.FrontierMachine := by
  classical
  let dones :=
    (Finset.univ : Finset (Finset Action)).filter
      (fun done => done ⊆ G.actions)
  exact dones.attach.image fun done =>
    { done := done.val
      done_subset_actions := by
        have h := (Finset.mem_filter.mp done.property).2
        simpa using h }

theorem mem_finset
    (G : ActionGraph Player Action Field Param Guard Join)
    [Fintype Action] (m : G.FrontierMachine) :
    m ∈ finset G := by
  classical
  let dones :=
    (Finset.univ : Finset (Finset Action)).filter
      (fun done => done ⊆ G.actions)
  have hdone : m.done ∈ dones := by
    simp [dones, m.done_subset_actions]
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨m.done, hdone⟩, ?_⟩
  constructor
  · simp
  · exact FrontierMachine.ext rfl

noncomputable instance instFintype
    (G : ActionGraph Player Action Field Param Guard Join)
    [Fintype Action] : Fintype G.FrontierMachine :=
  Fintype.mk (finset G) (mem_finset G)

end FrontierMachine

/-- Bounded runtime history for an action-graph configuration.

The abstract `History` API remains list-shaped, but executable graph
configurations keep only a bounded stack. This keeps the machine state finite
when fields and values are finite. `push` preserves the newest slice and drops
old tail entries after the bound, which is enough for the frontier machine:
reachable executions perform at most one push per graph frontier before
completion. -/
structure BoundedHistory
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type) where
  stack : History Field (StoredValue Value)
  length_le : stack.length ≤ G.actions.card + 1

namespace BoundedHistory

variable {G : ActionGraph Player Action Field Param Guard Join}
variable {Value : Type}

@[ext] theorem ext
    {left right : G.BoundedHistory Value}
    (hstack : left.stack = right.stack) :
    left = right := by
  cases left
  cases right
  cases hstack
  rfl

/-- Empty bounded history. -/
def empty (G : ActionGraph Player Action Field Param Guard Join) :
    G.BoundedHistory Value where
  stack := []
  length_le := by simp

/-- Push a newest slice, dropping old tail entries beyond the finite bound. -/
def push (history : G.BoundedHistory Value)
    (slice : Slice Field (StoredValue Value)) : G.BoundedHistory Value where
  stack := (History.push history.stack slice).take (G.actions.card + 1)
  length_le := by
    exact List.length_take_le _ _

@[simp] theorem empty_stack
    (G : ActionGraph Player Action Field Param Guard Join) :
    (empty (Value := Value) G).stack = [] := rfl

@[simp] theorem push_stack
    (history : G.BoundedHistory Value)
    (slice : Slice Field (StoredValue Value)) :
    (history.push slice).stack =
      (History.push history.stack slice).take (G.actions.card + 1) := rfl

theorem lookup_push
    (history : G.BoundedHistory Value)
    (slice : Slice Field (StoredValue Value)) (field : Field) :
    History.lookup (history.push slice).stack field =
      match slice field with
      | some value => some value
      | none =>
          History.lookup (history.stack.take G.actions.card) field := by
  cases hslice : slice field with
  | none =>
      simp [push, History.push, History.lookup, hslice]
  | some value =>
      simp [push, History.push, History.lookup, hslice]

/-- Finite enumeration of bounded histories over finite field/value domains. -/
noncomputable def finset
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type)
    [Fintype Field] [DecidableEq Value] [Fintype Value] :
    Finset (G.BoundedHistory Value) := by
  classical
  let stored : Finset (StoredValue Value) :=
    ((Finset.univ : Finset Value).image StoredValue.clear) ∪
      ((Finset.univ : Finset Value).image StoredValue.hidden) ∪
        {StoredValue.quit}
  let values : Finset (Option (StoredValue Value)) :=
    stored.image some ∪ {none}
  let slices : Finset (Slice Field (StoredValue Value)) :=
    Fintype.piFinset (fun _field : Field => values)
  let stacks :=
    (Math.BoundedLists.listsUpToLength slices (G.actions.card + 1)).filter
      (fun stack => List.length stack ≤ G.actions.card + 1)
  exact stacks.attach.image fun stack =>
    { stack := stack.val
      length_le := by
        have h := (Finset.mem_filter.mp stack.property).2
        simpa using h }

theorem mem_finset
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type)
    [Fintype Field] [DecidableEq Value] [Fintype Value]
    (history : G.BoundedHistory Value) :
    history ∈ finset G Value := by
  classical
  let stored : Finset (StoredValue Value) :=
    ((Finset.univ : Finset Value).image StoredValue.clear) ∪
      ((Finset.univ : Finset Value).image StoredValue.hidden) ∪
        {StoredValue.quit}
  let values : Finset (Option (StoredValue Value)) :=
    stored.image some ∪ {none}
  let slices : Finset (Slice Field (StoredValue Value)) :=
    Fintype.piFinset (fun _field : Field => values)
  let stacks :=
    (Math.BoundedLists.listsUpToLength slices (G.actions.card + 1)).filter
      (fun stack => List.length stack ≤ G.actions.card + 1)
  refine Finset.mem_image.mpr ?_
  have hstack : history.stack ∈ stacks := by
    exact Finset.mem_filter.mpr
      ⟨Math.BoundedLists.mem_listsUpToLength_of_forall_mem
          history.length_le
          (by
            intro slice _hslice
            exact Fintype.mem_piFinset.mpr (by
              intro field
              cases hvalue : slice field with
              | none =>
                  simp [values]
              | some value =>
                  cases value <;> simp [values, stored])),
        history.length_le⟩
  refine ⟨⟨history.stack, hstack⟩, ?_⟩
  constructor
  · simp
  · exact BoundedHistory.ext (G := G) (Value := Value) rfl

noncomputable instance instFintype
    (G : ActionGraph Player Action Field Param Guard Join)
    [Fintype Field] [DecidableEq Value] [Fintype Value] :
    Fintype (G.BoundedHistory Value) :=
  Fintype.mk (finset G Value) (mem_finset G Value)

end BoundedHistory

/-- Tag identifying the source of a player move. This is the Lean version of
the prototype `PlayTag`: either an explicit action in the frontier or a quit
packet for the player's currently enabled parameterized actions. -/
inductive PlayTag (Action : Type) where
  | action (action : Action)
  | quit
  deriving Repr

/-- A labelled move in the frontier LTS. `play` accumulates one player's
frontier delta; `finalizeFrontier` commits the partial frontier slice to
history and advances the frontier machine. Value/guard validity of a delta is
supplied by the frontend/backend interpretation, while the structural
scheduling side is captured by `Configuration.StructurallyLegalLabel`. -/
inductive FrontierLabel
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type) where
  | play (who : Player) (delta : Slice Field (StoredValue Value))
      (tag : PlayTag Action)
  | finalizeFrontier

/-- Frontier-based runtime configuration, mirroring the Kotlin semantic
configuration: frontier machine, committed global history, and current partial
frontier assignment. -/
structure Configuration
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type) where
  frontier : G.FrontierMachine
  history : G.BoundedHistory Value
  partialFrontierAssignment : Slice Field (StoredValue Value)

namespace Configuration

variable {G : ActionGraph Player Action Field Param Guard Join}
variable {Value : Type}

@[ext] theorem ext
    {left right : G.Configuration Value}
    (hfrontier : left.frontier = right.frontier)
    (hhistory : left.history = right.history)
    (hpartial :
      left.partialFrontierAssignment = right.partialFrontierAssignment) :
    left = right := by
  cases left
  cases right
  cases hfrontier
  cases hhistory
  cases hpartial
  rfl

/-- Finite enumeration of graph configurations over finite carriers. -/
noncomputable def finset
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type)
    [Fintype Action] [Fintype Field] [DecidableEq Value] [Fintype Value] :
    Finset (G.Configuration Value) := by
  classical
  let frontiers : Finset G.FrontierMachine := Finset.univ
  let histories : Finset (G.BoundedHistory Value) := Finset.univ
  let stored : Finset (StoredValue Value) :=
    ((Finset.univ : Finset Value).image StoredValue.clear) ∪
      ((Finset.univ : Finset Value).image StoredValue.hidden) ∪
        {StoredValue.quit}
  let values : Finset (Option (StoredValue Value)) :=
    stored.image some ∪ {none}
  let slices : Finset (Slice Field (StoredValue Value)) :=
    Fintype.piFinset (fun _field : Field => values)
  exact ((frontiers ×ˢ histories) ×ˢ slices).image fun item =>
    { frontier := item.1.1
      history := item.1.2
      partialFrontierAssignment := item.2 }

theorem mem_finset
    (G : ActionGraph Player Action Field Param Guard Join) (Value : Type)
    [Fintype Action] [Fintype Field] [DecidableEq Value] [Fintype Value]
    (cfg : G.Configuration Value) :
    cfg ∈ finset G Value := by
  classical
  let frontiers : Finset G.FrontierMachine := Finset.univ
  let histories : Finset (G.BoundedHistory Value) := Finset.univ
  let stored : Finset (StoredValue Value) :=
    ((Finset.univ : Finset Value).image StoredValue.clear) ∪
      ((Finset.univ : Finset Value).image StoredValue.hidden) ∪
        {StoredValue.quit}
  let values : Finset (Option (StoredValue Value)) :=
    stored.image some ∪ {none}
  let slices : Finset (Slice Field (StoredValue Value)) :=
    Fintype.piFinset (fun _field : Field => values)
  have hslice : cfg.partialFrontierAssignment ∈ slices := by
    exact Fintype.mem_piFinset.mpr (by
      intro field
      cases hvalue : cfg.partialFrontierAssignment field with
      | none =>
          simp [values]
      | some value =>
          cases value <;> simp [values, stored])
  refine Finset.mem_image.mpr ?_
  refine
    ⟨((cfg.frontier, cfg.history), cfg.partialFrontierAssignment), ?_⟩
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨by simp, by simp⟩,
        hslice⟩
  · exact Configuration.ext rfl rfl rfl

/-- Graph configurations are finite when action, field, and value carriers are
finite. -/
noncomputable instance instFintype
    (G : ActionGraph Player Action Field Param Guard Join)
    [Fintype Action] [Fintype Field] [DecidableEq Value] [Fintype Value] :
    Fintype (G.Configuration Value) :=
  Fintype.mk (finset G Value) (mem_finset G Value)

/-- Initial frontier configuration. -/
def initial (G : ActionGraph Player Action Field Param Guard Join) :
    G.Configuration Value where
  frontier := FrontierMachine.initial G
  history := BoundedHistory.empty G
  partialFrontierAssignment := fun _ => none

/-- Terminal configurations have no unresolved graph action. -/
def isTerminal (cfg : G.Configuration Value) : Prop :=
  cfg.frontier.isComplete

/-- Currently enabled action frontier. -/
def enabled (cfg : G.Configuration Value) : Finset Action :=
  cfg.frontier.enabled

/-- Enabled actions owned by one player. -/
def actionsByActor [DecidableEq Player]
    (cfg : G.Configuration Value) (who : Player) : Finset Action :=
  cfg.enabled.filter (fun action => G.actor action = some who)

@[simp] theorem mem_actionsByActor_iff [DecidableEq Player]
    (cfg : G.Configuration Value) (who : Player) (action : Action) :
    action ∈ cfg.actionsByActor who ↔
      action ∈ cfg.enabled ∧ G.actor action = some who := by
  simp [actionsByActor]

/-- Players that have at least one enabled action with explicit parameters in
the current frontier. This is a set because finalization only needs membership;
the finite carrier is still `cfg.enabled`. -/
def actorsWithParams (cfg : G.Configuration Value) : Set Player :=
  { who | ∃ action,
      action ∈ cfg.enabled ∧
        G.actor action = some who ∧
          (G.spec action).params.isEmpty = false }

/-- A player has already submitted a partial assignment in this frontier if
the partial slice touches one of their fields. -/
def HasActed (cfg : G.Configuration Value) (who : Player) : Prop :=
    ∃ field value,
    G.fieldOwner field = some who ∧
      cfg.partialFrontierAssignment field = some value

/-- Structural side condition for one player move tag. This deliberately does
not validate the submitted `delta`: domains, guards, hidden/revealed value
construction, and backend-specific packet shape belong to the graph
interpretation that enumerates concrete choices. -/
def StructurallyLegalPlayTag [DecidableEq Player]
    (cfg : G.Configuration Value) (who : Player) : PlayTag Action → Prop
  | .action action =>
      ¬ cfg.isTerminal ∧
        ¬ History.quit G.fieldOwner who cfg.history.stack ∧
        ¬ cfg.HasActed who ∧
        action ∈ cfg.actionsByActor who ∧
        (G.spec action).params.isEmpty = false
  | .quit =>
      ¬ cfg.isTerminal ∧
        ¬ History.quit G.fieldOwner who cfg.history.stack ∧
        ¬ cfg.HasActed who ∧
        ∃ action,
          action ∈ cfg.actionsByActor who ∧
            (G.spec action).params.isEmpty = false

/-- Finalization is enabled once every non-quitted player with parameterized
enabled actions has acted. Zero-parameter action submission can be represented
by a frontend tag discipline on top of this semantic predicate. -/
def CanFinalizeFrontier [DecidableEq Player]
    (cfg : G.Configuration Value) : Prop :=
  ¬ cfg.isTerminal ∧
    ∀ who,
      who ∈ cfg.actorsWithParams →
        ¬ History.quit G.fieldOwner who cfg.history.stack →
          cfg.HasActed who

theorem not_canFinalizeFrontier_of_terminal [DecidableEq Player]
    (cfg : G.Configuration Value) :
    cfg.isTerminal → ¬ cfg.CanFinalizeFrontier := by
  intro hterminal hfinal
  exact hfinal.1 hterminal

/-- Structural legality of a frontier LTS label. For player labels this checks
only scheduling/role facts; value-level legality of the packet is supplied by
the interpretation that turns the graph into a machine. -/
def StructurallyLegalLabel [DecidableEq Player]
    (cfg : G.Configuration Value) : FrontierLabel G Value → Prop
  | .play who _delta tag => cfg.StructurallyLegalPlayTag who tag
  | .finalizeFrontier => cfg.CanFinalizeFrontier

/-- A quit slice assigning `quit` to every field written by `who`'s selected
actions. Frontends that distinguish parameters from storage fields can use this
as the graph-level support lemma and prove their syntax-specific quit packet
maps to it. -/
noncomputable def quitSlice [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join)
    (who : Player) (actions : Finset Action) :
    Slice Field (StoredValue Value) := by
  classical
  exact fun field =>
    if ∃ action,
        action ∈ actions ∧ G.actor action = some who ∧ field ∈ G.writes action
    then some StoredValue.quit
    else none

theorem quitSlice_eq_some_iff [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join)
    (who : Player) (actions : Finset Action) (field : Field) :
    quitSlice (Value := Value) G who actions field =
        some StoredValue.quit ↔
      ∃ action,
        action ∈ actions ∧ G.actor action = some who ∧
          field ∈ G.writes action := by
  classical
  simp [quitSlice]

theorem quitSlice_eq_none_iff [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join)
    (who : Player) (actions : Finset Action) (field : Field) :
    quitSlice (Value := Value) G who actions field = none ↔
      ¬ ∃ action,
        action ∈ actions ∧ G.actor action = some who ∧
          field ∈ G.writes action := by
  classical
  simp [quitSlice]

/-- Apply a frontier label. This is the pure transition function of the
frontier LTS; legality of labels is stated separately by
`CanFinalizeFrontier` and frontend-specific move enumeration. -/
def applyLabel
    (cfg : G.Configuration Value) :
    FrontierLabel G Value → G.Configuration Value
  | .play _who delta _tag =>
      { cfg with
        partialFrontierAssignment :=
          History.mergeSlice cfg.partialFrontierAssignment delta }
  | .finalizeFrontier =>
      { frontier := cfg.frontier.resolveEnabled
        history := cfg.history.push cfg.partialFrontierAssignment
        partialFrontierAssignment := fun _ => none }

@[simp] theorem applyLabel_play_frontier
    (cfg : G.Configuration Value) (who : Player)
    (delta : Slice Field (StoredValue Value)) (tag : PlayTag Action) :
    (cfg.applyLabel (.play who delta tag)).frontier = cfg.frontier := rfl

@[simp] theorem applyLabel_play_history
    (cfg : G.Configuration Value) (who : Player)
    (delta : Slice Field (StoredValue Value)) (tag : PlayTag Action) :
    (cfg.applyLabel (.play who delta tag)).history = cfg.history := rfl

@[simp] theorem applyLabel_play_partial
    (cfg : G.Configuration Value) (who : Player)
    (delta : Slice Field (StoredValue Value)) (tag : PlayTag Action) :
    (cfg.applyLabel (.play who delta tag)).partialFrontierAssignment =
      History.mergeSlice cfg.partialFrontierAssignment delta := rfl

@[simp] theorem applyLabel_finalize_frontier
    (cfg : G.Configuration Value) :
    (cfg.applyLabel FrontierLabel.finalizeFrontier).frontier =
      cfg.frontier.resolveEnabled := rfl

@[simp] theorem applyLabel_finalize_history
    (cfg : G.Configuration Value) :
    (cfg.applyLabel FrontierLabel.finalizeFrontier).history =
      cfg.history.push cfg.partialFrontierAssignment := rfl

@[simp] theorem applyLabel_finalize_partial
    (cfg : G.Configuration Value) :
    (cfg.applyLabel FrontierLabel.finalizeFrontier).partialFrontierAssignment =
      (fun _ => none) := rfl

end Configuration

/-- Done set obtained by repeatedly resolving frontiers. The list records the
frontier layers for documentation/proofs; advancement itself is deterministic. -/
def doneAfterFrontiers (G : ActionGraph Player Action Field Param Guard Join) :
    Finset Action → List (Finset Action) → Finset Action
  | done, [] => done
  | done, _frontier :: rest => G.doneAfterFrontiers (G.advance done) rest

@[simp] theorem doneAfterFrontiers_nil
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) :
    G.doneAfterFrontiers done [] = done := rfl

@[simp] theorem doneAfterFrontiers_cons
    (G : ActionGraph Player Action Field Param Guard Join)
    (done frontier : Finset Action) (rest : List (Finset Action)) :
    G.doneAfterFrontiers done (frontier :: rest) =
      G.doneAfterFrontiers (G.advance done) rest := rfl

/-- A sequence of frontier layers generated by repeated `advance`. The empty
sequence is valid exactly at completion; a nonempty sequence records the current
nonempty frontier and continues from `advance done`. -/
def FrontierSequenceFrom (G : ActionGraph Player Action Field Param Guard Join) :
    Finset Action → List (Finset Action) → Prop
  | done, [] => G.CompleteAt done
  | done, frontier :: rest =>
      frontier = G.frontier done ∧
        frontier.Nonempty ∧
        G.FrontierSequenceFrom (G.advance done) rest

/-- A complete frontier execution from the initial empty done set. -/
def FrontierSequence
    (G : ActionGraph Player Action Field Param Guard Join)
    (frontiers : List (Finset Action)) : Prop :=
  G.FrontierSequenceFrom ∅ frontiers

theorem doneAfterFrontiers_subset_actions_of_frontierSequenceFrom
    (G : ActionGraph Player Action Field Param Guard Join) :
    ∀ {done : Finset Action} {frontiers : List (Finset Action)},
      done ⊆ G.actions →
        G.FrontierSequenceFrom done frontiers →
          G.doneAfterFrontiers done frontiers ⊆ G.actions
  | done, [] => by
      intro hdone _hseq
      exact hdone
  | done, frontier :: rest => by
      intro hdone hseq
      exact G.doneAfterFrontiers_subset_actions_of_frontierSequenceFrom
        (done := G.advance done)
        (frontiers := rest)
        (G.advance_subset_actions hdone)
        hseq.2.2

theorem completeAt_doneAfterFrontiers_of_frontierSequenceFrom
    (G : ActionGraph Player Action Field Param Guard Join) :
    ∀ {done : Finset Action} {frontiers : List (Finset Action)},
      G.FrontierSequenceFrom done frontiers →
        G.CompleteAt (G.doneAfterFrontiers done frontiers)
  | _done, [] => by
      intro hseq
      exact hseq
  | done, frontier :: rest => by
      intro hseq
      exact G.completeAt_doneAfterFrontiers_of_frontierSequenceFrom
        (done := G.advance done) (frontiers := rest) hseq.2.2

theorem doneAfterFrontiers_eq_actions_of_frontierSequence
    (G : ActionGraph Player Action Field Param Guard Join)
    {frontiers : List (Finset Action)}
    (hseq : G.FrontierSequence frontiers) :
    G.doneAfterFrontiers ∅ frontiers = G.actions := by
  apply SetLike.ext'
  exact Set.Subset.antisymm
    (G.doneAfterFrontiers_subset_actions_of_frontierSequenceFrom
      (done := ∅) (frontiers := frontiers)
      (by intro action h; simp at h) hseq)
    (G.completeAt_doneAfterFrontiers_of_frontierSequenceFrom hseq)

/-- Frontier execution is deterministic at the graph level: from a fixed done
set there is at most one complete frontier sequence. Any scheduler appears only
when a later view serializes or refines a frontier layer. -/
theorem frontierSequenceFrom_unique
    (G : ActionGraph Player Action Field Param Guard Join) :
    ∀ {done : Finset Action} {frontiers₁ frontiers₂ : List (Finset Action)},
      G.FrontierSequenceFrom done frontiers₁ →
        G.FrontierSequenceFrom done frontiers₂ →
          frontiers₁ = frontiers₂
  | done, [], [] => by
      intro _h₁ _h₂
      rfl
  | done, [], frontier₂ :: rest₂ => by
      intro h₁ h₂
      have hempty : G.frontier done = ∅ :=
        (G.frontier_eq_empty_iff_completeAt done).mpr h₁
      have hfrontier₂_empty : frontier₂ = ∅ := by
        simpa [hempty] using h₂.1
      exact False.elim (h₂.2.1.ne_empty hfrontier₂_empty)
  | done, frontier₁ :: rest₁, [] => by
      intro h₁ h₂
      have hempty : G.frontier done = ∅ :=
        (G.frontier_eq_empty_iff_completeAt done).mpr h₂
      have hfrontier₁_empty : frontier₁ = ∅ := by
        simpa [hempty] using h₁.1
      exact False.elim (h₁.2.1.ne_empty hfrontier₁_empty)
  | done, frontier₁ :: rest₁, frontier₂ :: rest₂ => by
      intro h₁ h₂
      have hfrontiers : frontier₁ = frontier₂ := by
        rw [h₁.1, h₂.1]
      have hrests :
          rest₁ = rest₂ :=
        G.frontierSequenceFrom_unique h₁.2.2 h₂.2.2
      simp [hfrontiers, hrests]

theorem frontierSequence_unique
    (G : ActionGraph Player Action Field Param Guard Join)
    {frontiers₁ frontiers₂ : List (Finset Action)}
    (h₁ : G.FrontierSequence frontiers₁)
    (h₂ : G.FrontierSequence frontiers₂) :
    frontiers₁ = frontiers₂ :=
  G.frontierSequenceFrom_unique h₁ h₂

/-- A field is observable after `done` when it was observable in the initial
state, or some already done action wrote it with visibility available to
`who`. -/
def ObservableFieldAfter
    (G : ActionGraph Player Action Field Param Guard Join)
    (done : Finset Action) (who : Player) (field : Field) : Prop :=
  (field ∈ G.initialFields ∧
    (G.fieldOwner field = none ∨ G.fieldOwner field = some who)) ∨
  ∃ src,
    src ∈ done ∧
    src ∈ G.actions ∧
    field ∈ G.writes src ∧
    G.CanObserveWrite who src field

theorem observableFieldAfter_mono
    (G : ActionGraph Player Action Field Param Guard Join)
    {done₁ done₂ : Finset Action} {who : Player} {field : Field}
    (hsubset : done₁ ⊆ done₂)
    (h : G.ObservableFieldAfter done₁ who field) :
    G.ObservableFieldAfter done₂ who field := by
  rcases h with hinitial | hprior
  · exact Or.inl hinitial
  · rcases hprior with ⟨src, hdone, hsrc, hwrite, hobs⟩
    exact Or.inr ⟨src, hsubset hdone, hsrc, hwrite, hobs⟩

theorem exists_actor_initial_or_prior_write_canObserveWrite_of_guardRead
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action} {field : Field}
    (haction : action ∈ G.actions)
    (hfield : field ∈ G.guardReads action) :
    ∃ who,
      G.actor action = some who ∧
      ((field ∈ G.initialFields ∧
          (G.fieldOwner field = none ∨ G.fieldOwner field = some who)) ∨
        ∃ prior,
          prior ∈ G.actions ∧
          G.precedes prior action ∧
          field ∈ G.writes prior ∧
          G.CanObserveWrite who prior field) := by
  exact G.guardReads_observable_from_prior haction hfield

theorem exists_prior_commit_of_reveal_write
    (G : ActionGraph Player Action Field Param Guard Join)
    {action : Action} {field : Field}
    (haction : action ∈ G.actions)
    (hwrite : field ∈ G.writes action)
    (hvis : G.visibility action field = .reveal) :
    ∃ commitAction,
      commitAction ∈ G.actions ∧
      G.precedes commitAction action ∧
      field ∈ G.writes commitAction ∧
      G.visibility commitAction field = .commit := by
  exact G.reveal_has_prior_commit haction hwrite hvis

/-- A guard read of a ready action is observable after the current `done` set.

This theorem uses only the graph's static guard-read invariant and readiness;
it does not claim that every visible field is guard-relevant, nor that every
graph transformation preserves observations. -/
theorem guardRead_observableFieldAfter_of_ready
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action} {field : Field}
    (hready : G.Ready done action)
    (hfield : field ∈ G.guardReads action) :
    ∃ who,
      G.actor action = some who ∧
      G.ObservableFieldAfter done who field := by
  rcases G.exists_actor_initial_or_prior_write_canObserveWrite_of_guardRead
      hready.1 hfield with
    ⟨who, hactor, hobsField⟩
  refine ⟨who, hactor, ?_⟩
  rcases hobsField with hinitial | hprior
  · exact Or.inl hinitial
  · rcases hprior with ⟨src, hsrc, hprecedes, hwrite, hobs⟩
    exact Or.inr ⟨src,
      hready.2.2 ((G.precedes_iff_mem_predecessors).mp hprecedes),
      hsrc,
      hwrite,
      hobs⟩

theorem guardRead_observableFieldAfter_of_mem_frontier
    (G : ActionGraph Player Action Field Param Guard Join)
    {done : Finset Action} {action : Action} {field : Field}
    (hfrontier : action ∈ G.frontier done)
    (hfield : field ∈ G.guardReads action) :
    ∃ who,
      G.actor action = some who ∧
      G.ObservableFieldAfter done who field := by
  exact G.guardRead_observableFieldAfter_of_ready
    ((G.mem_frontier_iff done action).mp hfrontier) hfield

/-- Phase of a prerequisite action that a dependent action must wait for.

Reveal actions must wait for reveal, public actions for choice, and commit
actions expose only their commit event to other players while the same actor
can use the choice by recall. Mixed actions are deliberately conservative and
wait for reveal. -/
def prereqSourcePhase [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join)
    (src dst : Action) : Phase :=
  match G.kind src with
  | .reveal => .revealEvent
  | .pub => .choice
  | .commit =>
      match G.actor src, G.actor dst with
      | some srcPlayer, some dstPlayer =>
          if srcPlayer = dstPlayer then .choice else .commitEvent
      | _, _ => .commitEvent
  | .mixed => .revealEvent

/-- Edges of the visibility-expanded phase graph generated by an action graph.
This relation is intentionally structural: it specifies the scheduling
constraints that a later executable phase-DAG implementation should realize. -/
inductive PhaseEdge [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join) :
    PhaseNode Action → PhaseNode Action → Prop where
  | commit_choice {action : Action} :
      action ∈ G.actions →
        PhaseEdge G
          ⟨action, .commitEvent⟩
          ⟨action, .choice⟩
  | choice_reveal {action : Action} :
      action ∈ G.actions →
        PhaseEdge G
          ⟨action, .choice⟩
          ⟨action, .revealEvent⟩
  | prereq {src dst : Action} :
      dst ∈ G.actions →
      src ∈ G.prereqs dst →
        PhaseEdge G
          ⟨src, G.prereqSourcePhase src dst⟩
          ⟨dst, .commitEvent⟩

/-- The source action of every phase edge belongs to the graph. -/
theorem phaseEdge_source_action_mem [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join)
    {source target : PhaseNode Action}
    (h : PhaseEdge G source target) :
    source.action ∈ G.actions := by
  cases h with
  | commit_choice haction => exact haction
  | choice_reveal haction => exact haction
  | prereq hdst hpre => exact G.prereqs_subset_actions hdst hpre

/-- The target action of every phase edge belongs to the graph. -/
theorem phaseEdge_target_action_mem [DecidableEq Player]
    (G : ActionGraph Player Action Field Param Guard Join)
    {source target : PhaseNode Action}
    (h : PhaseEdge G source target) :
    target.action ∈ G.actions := by
  cases h with
  | commit_choice haction => exact haction
  | choice_reveal haction => exact haction
  | prereq hdst _hpre => exact hdst

end ActionGraph

end Vegas
