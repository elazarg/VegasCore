/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Schedule-free event-graph execution

Execution exposes graph events together with the evidence that they are
available.  It does not choose a schedule: traces, tests, runtimes, and game
presentations provide external laws over available primitive events.
-/

namespace Vegas

namespace EventGraph

namespace Store

variable {L : IExpr}

/-- Update one graph field in a runtime store. -/
def set (store : Store L) (field : Nat) (value : TypedValue L) : Store L :=
  fun query => if query = field then some value else store query

@[simp] theorem set_eq (store : Store L) (field : Nat) (value : TypedValue L) :
    set store field value field = some value := by
  simp [set]

@[simp] theorem set_ne (store : Store L) {field query : Nat}
    (hne : query ≠ field) (value : TypedValue L) :
    set store field value query = store query := by
  simp [set, hne]

theorem getAs_set_ne (store : Store L) {field query : Nat}
    (hne : query ≠ field) (value : TypedValue L) (ty : L.Ty) :
    Store.getAs (set store field value) query ty =
      Store.getAs store query ty := by
  simp [Store.getAs, set, hne]

theorem set_comm (store : Store L) {field₁ field₂ : Nat}
    (hne : field₁ ≠ field₂) (value₁ value₂ : TypedValue L) :
    set (set store field₁ value₁) field₂ value₂ =
      set (set store field₂ value₂) field₁ value₁ := by
  funext query
  by_cases hq₂ : query = field₂
  · subst query
    simp [set, hne.symm]
  · by_cases hq₁ : query = field₁
    · subst query
      simp [set, hq₂]
    · simp [set, hq₁, hq₂]

end Store

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A runtime configuration for an event graph. `done` records completed graph
nodes; `store` records field values. -/
structure Config (G : Graph Player L) where
  done : Finset (Fin G.nodeCount)
  store : Store L

namespace Config

variable {G : Graph Player L}

/-- Initial configuration: no graph node has run and the store contains
initial fields. -/
def initial (G : Graph Player L) : Config G where
  done := ∅
  store := G.initialStore

/-- Completed nodes as numeric ids, for comparison with graph-level dependency
sets and field origins. -/
def doneIds (cfg : Config G) : Finset Nat :=
  cfg.done.image (fun node : Fin G.nodeCount => (node : Nat))

/-- Whether a numeric graph node id is complete in this configuration. -/
def nodeDone (cfg : Config G) (node : Nat) : Prop :=
  node ∈ cfg.doneIds

/-- Complete a node by writing its canonical output field and recording the
node as done. -/
def completeNode (cfg : Config G) (node : Fin G.nodeCount)
    (value : TypedValue L) : Config G :=
  { done := insert node cfg.done
    store := Store.set cfg.store (G.nodeTarget node) value }

theorem nodeTarget_ne_of_ne {G : Graph Player L}
    {left right : Fin G.nodeCount} (hne : left ≠ right) :
    G.nodeTarget left ≠ G.nodeTarget right := by
  intro htarget
  apply hne
  apply Fin.ext
  unfold Graph.nodeTarget at htarget
  omega

theorem completeNode_comm {G : Graph Player L} (cfg : Config G)
    {left right : Fin G.nodeCount}
    (valueLeft valueRight : TypedValue L)
    (hne : left ≠ right) :
    (cfg.completeNode left valueLeft).completeNode right valueRight =
      (cfg.completeNode right valueRight).completeNode left valueLeft := by
  cases cfg with
  | mk done store =>
      simp [completeNode, Finset.insert_comm,
        Store.set_comm store (nodeTarget_ne_of_ne (G := G) hne)
          valueLeft valueRight]

end Config

/-- A graph node is ready when it is valid, unfinished, and all of its
graph-causal prerequisites are complete. -/
def Ready (G : Graph Player L) (cfg : Config G)
    (node : Fin G.nodeCount) : Prop :=
  node ∉ cfg.done ∧
    G.prereqs node ⊆ cfg.done

theorem Ready.completeNode_of_ne
    {G : Graph Player L} {cfg : Config G}
    {node other : Fin G.nodeCount} {value : TypedValue L}
    (hready : Ready G cfg node)
    (hne : node ≠ other) :
    Ready G (cfg.completeNode other value) node := by
  constructor
  · intro hdone
    have hmem :
        node = other ∨ node ∈ cfg.done := by
      simpa [Config.completeNode] using hdone
    cases hmem with
    | inl heq => exact hne heq
    | inr hold => exact hready.1 hold
  · intro prior hprior
    exact
      Finset.mem_insert_of_mem
        (hready.2 hprior)

theorem Ready.nodeTarget_not_mem_reads_of_ready
    {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF)
    {node other : Fin G.nodeCount}
    {event otherEvent : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (hother : G.nodes[other]? = some otherEvent)
    (hready : Ready G cfg node)
    (hotherReady : Ready G cfg other) :
    G.nodeTarget other ∉ event.sem.reads := by
  intro hread
  have havailable :
      G.fieldAvailableBefore (node : Nat) (G.nodeTarget other) = true :=
    (hwf node event hnode).1 (G.nodeTarget other) hread
  unfold Graph.fieldAvailableBefore at havailable
  rw [G.field?_nodeTarget hother] at havailable
  simp only [decide_eq_true_eq] at havailable
  have hprereq : other ∈ G.prereqs node :=
    G.nodeTarget_mem_prereqs_of_read
      hnode hother havailable hread
  exact hotherReady.1 (hready.2 hprereq)

theorem ReadEnv.ofStore?_completeNode_of_not_read
    {G : Graph Player L} {cfg : Config G}
    {node : Fin G.nodeCount} {value : TypedValue L}
    {refs : Finset (FieldRef L)} {env : ReadEnv L refs}
    (henv : ReadEnv.ofStore? cfg.store refs = some env)
    (hnotRead :
      ∀ ref, ref ∈ refs → ref.field ≠ G.nodeTarget node) :
    ReadEnv.ofStore? (cfg.completeNode node value).store refs = some env := by
  exact
    ReadEnv.ofStore?_eq_of_getAs_eq henv
      (by
        intro ref href
        exact
          (Store.getAs_set_ne cfg.store (hnotRead ref href) value ref.ty).symm)

noncomputable instance instDecidableReady (G : Graph Player L) (cfg : Config G)
    (node : Fin G.nodeCount) : Decidable (Ready G cfg node) := by
  classical
  unfold Ready
  infer_instance

/-- A graph configuration is terminal exactly when every graph node is done. -/
def Terminal (G : Graph Player L) (cfg : Config G) : Prop :=
  ∀ node : Fin G.nodeCount, node ∈ cfg.done

/-- Every nonterminal graph configuration has a ready node.

This uses the canonical dependency invariant that prerequisites always point
to earlier node ids: choose the least unfinished node, then all of its
prerequisites are already complete. -/
theorem exists_ready_of_not_terminal
    (G : Graph Player L) (cfg : Config G)
    (hterminal : ¬ Terminal G cfg) :
    ∃ node : Fin G.nodeCount, Ready G cfg node := by
  classical
  have hexNode : ∃ node : Fin G.nodeCount, node ∉ cfg.done := by
    by_contra hnone
    apply hterminal
    intro node
    by_contra hnot
    exact hnone ⟨node, hnot⟩
  have hexNat :
      ∃ n : Nat, ∃ hlt : n < G.nodeCount,
        (⟨n, hlt⟩ : Fin G.nodeCount) ∉ cfg.done := by
    rcases hexNode with ⟨node, hnode⟩
    exact ⟨node, node.isLt, hnode⟩
  let n := Nat.find hexNat
  rcases Nat.find_spec hexNat with ⟨hnlt, hnnot⟩
  let node : Fin G.nodeCount := ⟨n, hnlt⟩
  refine ⟨node, hnnot, ?_⟩
  intro prior hprior
  by_contra hpriorNotDone
  have hpriorCandidate :
      ∃ hlt : (prior : Nat) < G.nodeCount,
        (⟨(prior : Nat), hlt⟩ : Fin G.nodeCount) ∉ cfg.done :=
    ⟨prior.isLt, by simpa using hpriorNotDone⟩
  have hmin := Nat.find_min hexNat (G.prereq_lt hprior)
  exact hmin hpriorCandidate

/-- Store coherence for reachable graph states.

Initial fields must always be present at their declared type. Event fields
must be present at their declared type once their writer node is complete. -/
def StoreCoherent (G : Graph Player L) (cfg : Config G) : Prop :=
  ∀ field spec, G.field? field = some spec →
    (match spec.source with
     | .initial _ => True
     | .event node => cfg.nodeDone node) →
      ∃ value : L.Val spec.ty, Store.getAs cfg.store field spec.ty = some value

theorem initial_storeCoherent (G : Graph Player L) :
    StoreCoherent G (Config.initial G) := by
  intro field spec hget hready
  rcases spec with ⟨ty, owner, source⟩
  change ∃ value : L.Val ty,
    Store.getAs (Graph.initialStore G) field ty = some value
  cases source with
  | initial value =>
      refine ⟨value, ?_⟩
      dsimp [Graph.initialStore, Store.getAs]
      rw [hget]
      simp [FieldSpec.initialValue?, TypedValue.as?]
  | event node =>
      simp [Config.initial, Config.nodeDone, Config.doneIds] at hready

theorem StoreCoherent.completeNodeTyped
    {G : Graph Player L} {cfg : Config G}
    (hcoherent : StoreCoherent G cfg)
    {node : Fin G.nodeCount} {event : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (value : TypedValue L)
    (hty : value.ty = event.ty) :
    StoreCoherent G (cfg.completeNode node value) := by
  intro field spec hget hready
  rcases spec with ⟨specTy, specOwner, specSource⟩
  by_cases hfield : field = G.nodeTarget node
  · subst hfield
    have htarget := G.field?_nodeTarget hnode
    rw [htarget] at hget
    cases hget
    refine
      ⟨cast (by rw [hty]) value.value, ?_⟩
    simp [Config.completeNode, Store.getAs, TypedValue.as?, hty]
  · cases specSource with
    | initial initValue =>
        rcases hcoherent field
            { ty := specTy, owner := specOwner,
              source := .initial initValue }
            hget trivial with
          ⟨oldValue, hold⟩
        exact
          ⟨oldValue, by
            simpa [Config.completeNode, Store.getAs, Store.set, hfield]
              using hold⟩
    | event writer =>
        have hdone : cfg.nodeDone writer := by
          by_cases hwriter : writer = (node : Nat)
          · subst writer
            have heq :
                field = G.nodeTarget node :=
              G.field_eq_nodeTarget_of_event_source hget rfl
            exact False.elim (hfield heq)
          · have hdoneOr :
                writer = (node : Nat) ∨ writer ∈ cfg.doneIds := by
              simpa [Config.completeNode, Config.nodeDone, Config.doneIds]
                using hready
            exact hdoneOr.resolve_left hwriter
        rcases hcoherent field
            { ty := specTy, owner := specOwner, source := .event writer }
            hget hdone with
          ⟨oldValue, hold⟩
        exact
          ⟨oldValue, by
            simpa [Config.completeNode, Store.getAs, Store.set, hfield]
              using hold⟩

theorem StoreCoherent.completeNode
    {G : Graph Player L} {cfg : Config G}
    (hcoherent : StoreCoherent G cfg)
    {node : Fin G.nodeCount} {event : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (value : L.Val event.ty) :
    StoreCoherent G
      (cfg.completeNode node { ty := event.ty, value := value }) := by
  exact hcoherent.completeNodeTyped hnode { ty := event.ty, value := value } rfl

theorem StoreCoherent.hasRefOfAvailable
    {G : Graph Player L} {cfg : Config G}
    (hcoherent : StoreCoherent G cfg)
    (hterminal : Terminal G cfg)
    {ref : FieldRef L}
    (href : G.fieldRefPublic ref)
    (havailable : G.fieldAvailableBefore G.nodeCount ref.field = true) :
    ∃ value : L.Val ref.ty,
      Store.getAs cfg.store ref.field ref.ty = some value := by
  rcases href with ⟨spec, hget, hty, _howner⟩
  have hready :
      match spec.source with
      | .initial _ => True
      | .event node => cfg.nodeDone node := by
    unfold Graph.fieldAvailableBefore at havailable
    rw [hget] at havailable
    cases hsource : spec.source with
    | initial value => trivial
    | event node =>
        have hlt : node < G.nodeCount := by
          simpa [hsource] using havailable
        change node ∈ cfg.doneIds
        exact
          Finset.mem_image.mpr
            ⟨⟨node, hlt⟩, hterminal ⟨node, hlt⟩, rfl⟩
  rcases hcoherent ref.field spec hget hready with ⟨value, hvalue⟩
  rw [← hty]
  exact ⟨value, hvalue⟩

/-- A concrete commit choice for player `who`. -/
structure CommitAction (G : Graph Player L) (who : Player) where
  node : Fin G.nodeCount
  value : TypedValue L

/-- An internal graph event: sampling or reveal. -/
structure InternalEvent (G : Graph Player L) where
  node : Fin G.nodeCount

/-- Evidence that a concrete commit action is currently available. -/
structure CommitStep (G : Graph Player L) (cfg : Config G)
    (who : Player) (action : CommitAction G who) where
  row : EventNode Player L
  guard : EventGuard L
  row_get : G.nodes[action.node]? = some row
  sem_eq : row.sem = .commit who guard
  ready : Ready G cfg action.node
  value : L.Val guard.ty
  value_ok : action.value.as? guard.ty = some value
  env : ReadEnv L guard.choiceReads
  env_ok : ReadEnv.ofStore? cfg.store guard.choiceReads = some env
  guard_ok : guard.eval value env = true

/-- Evidence that an internal graph event is currently available. -/
inductive InternalStep (G : Graph Player L) (cfg : Config G)
    (event : InternalEvent G) where
  | sample
      (row : EventNode Player L) (dist : EventDist L)
      (row_get : G.nodes[event.node]? = some row)
      (sem_eq : row.sem = .sample dist)
      (ready : Ready G cfg event.node)
      (env : ReadEnv L dist.reads)
      (env_ok : ReadEnv.ofStore? cfg.store dist.reads = some env)
  | reveal
      (row : EventNode Player L) (source : Nat)
      (row_get : G.nodes[event.node]? = some row)
      (sem_eq : row.sem = .reveal source)
      (ready : Ready G cfg event.node)
      (value : L.Val row.ty)
      (value_ok : Store.getAs cfg.store source row.ty = some value)

/-- Commit action availability. A ready commit is available to its owner when
the proposed typed value has the guard's action type and satisfies the guard
against the current graph store. -/
noncomputable def CommitAvailable (G : Graph Player L) (cfg : Config G)
    (who : Player) (action : CommitAction G who) : Prop :=
  Nonempty (CommitStep G cfg who action)

/-- Internal event availability. Internal nodes are available when ready and
their local computation can evaluate from the current store. -/
noncomputable def InternalAvailable (G : Graph Player L) (cfg : Config G)
    (event : InternalEvent G) : Prop :=
  Nonempty (InternalStep G cfg event)

theorem InternalAvailable.ready
    {G : Graph Player L} {cfg : Config G}
    {event : InternalEvent G}
    (h : InternalAvailable G cfg event) :
    ∃ row, G.nodes[event.node]? = some row ∧ Ready G cfg event.node := by
  rcases h with ⟨step⟩
  cases step with
  | sample row _ row_get _ ready _ _ =>
      exact ⟨row, row_get, ready⟩
  | reveal row _ row_get _ ready _ _ =>
      exact ⟨row, row_get, ready⟩

/-- Commit availability persists after another ready node writes its canonical
output field. -/
theorem CommitAvailable.persist_after_other_ready_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    {who : Player}
    {action : CommitAction G who}
    (h₁ : CommitAvailable G cfg who action)
    {other : Fin G.nodeCount} {otherRow : EventNode Player L}
    (hotherRow : G.nodes[other]? = some otherRow)
    (hotherReady : Ready G cfg other)
    (written : TypedValue L)
    (hne : action.node ≠ other) :
    CommitAvailable G
      (cfg.completeNode other written)
      who action := by
  rcases h₁ with ⟨step₁⟩
  have htargetNot :
      G.nodeTarget other ∉ step₁.row.sem.reads :=
    Ready.nodeTarget_not_mem_reads_of_ready
      hwf step₁.row_get hotherRow step₁.ready hotherReady
  have hnotRead :
      ∀ ref, ref ∈ step₁.guard.choiceReads →
        ref.field ≠ G.nodeTarget other := by
    intro ref href heq
    apply htargetNot
    rw [step₁.sem_eq]
    exact Finset.mem_image.mpr ⟨ref, href, heq⟩
  exact
    ⟨{ row := step₁.row
       guard := step₁.guard
       row_get := step₁.row_get
       sem_eq := step₁.sem_eq
       ready := step₁.ready.completeNode_of_ne hne
       value := step₁.value
       value_ok := step₁.value_ok
       env := step₁.env
       env_ok :=
        ReadEnv.ofStore?_completeNode_of_not_read
          (value := written) step₁.env_ok hnotRead
       guard_ok := step₁.guard_ok }⟩

theorem CommitAvailable.persist_after_other_commit_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    {who₁ who₂ : Player}
    {action₁ : CommitAction G who₁}
    {action₂ : CommitAction G who₂}
    (h₁ : CommitAvailable G cfg who₁ action₁)
    (h₂ : CommitAvailable G cfg who₂ action₂)
    (written : TypedValue L)
    (hne : action₁.node ≠ action₂.node) :
    CommitAvailable G
      (cfg.completeNode action₂.node written)
      who₁ action₁ := by
  rcases h₂ with ⟨step₂⟩
  exact
    h₁.persist_after_other_ready_write
      hwf step₂.row_get step₂.ready written hne

theorem CommitAvailable.persist_after_other_commit
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    {who₁ who₂ : Player}
    {action₁ : CommitAction G who₁}
    {action₂ : CommitAction G who₂}
    (h₁ : CommitAvailable G cfg who₁ action₁)
    (h₂ : CommitAvailable G cfg who₂ action₂)
    (hne : action₁.node ≠ action₂.node) :
    CommitAvailable G
      (cfg.completeNode action₂.node action₂.value)
      who₁ action₁ :=
  h₁.persist_after_other_commit_write hwf h₂ action₂.value hne

/-- Internal event availability persists after another ready node writes its
canonical output field. -/
theorem InternalAvailable.persist_after_other_ready_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    {event : InternalEvent G}
    (h₁ : InternalAvailable G cfg event)
    {other : Fin G.nodeCount} {otherRow : EventNode Player L}
    (hotherRow : G.nodes[other]? = some otherRow)
    (hotherReady : Ready G cfg other)
    (written : TypedValue L)
    (hne : event.node ≠ other) :
    InternalAvailable G
      (cfg.completeNode other written)
      event := by
  rcases h₁ with ⟨step₁⟩
  cases step₁ with
  | sample row dist row_get sem_eq ready env env_ok =>
      have htargetNot :
          G.nodeTarget other ∉ row.sem.reads :=
        Ready.nodeTarget_not_mem_reads_of_ready
          hwf row_get hotherRow ready hotherReady
      have hnotRead :
          ∀ ref, ref ∈ dist.reads →
            ref.field ≠ G.nodeTarget other := by
        intro ref href heq
        apply htargetNot
        rw [sem_eq]
        exact Finset.mem_image.mpr ⟨ref, href, heq⟩
      exact
        ⟨InternalStep.sample row dist row_get sem_eq
          (ready.completeNode_of_ne hne) env
          (ReadEnv.ofStore?_completeNode_of_not_read
            (value := written) env_ok hnotRead)⟩
  | reveal row source row_get sem_eq ready value value_ok =>
      have htargetNot :
          G.nodeTarget other ∉ row.sem.reads :=
        Ready.nodeTarget_not_mem_reads_of_ready
          hwf row_get hotherRow ready hotherReady
      have hsourceNe : source ≠ G.nodeTarget other := by
        intro heq
        apply htargetNot
        rw [sem_eq]
        simp [NodeSem.reads, heq]
      have hvalue :
          Store.getAs (cfg.completeNode other written).store
            source row.ty = some value := by
        rw [Config.completeNode]
        exact
          (Store.getAs_set_ne cfg.store hsourceNe written row.ty).trans
            value_ok
      exact
        ⟨InternalStep.reveal row source row_get sem_eq
          (ready.completeNode_of_ne hne) value hvalue⟩

/-- A primitive graph event with the evidence needed to execute it. -/
inductive AvailableEvent (G : Graph Player L) (cfg : Config G) where
  | commit (who : Player) (action : CommitAction G who)
      (step : CommitStep G cfg who action)
  | internal (event : InternalEvent G) (step : InternalStep G cfg event)

namespace AvailableEvent

variable {G : Graph Player L} {cfg : Config G}

/-- The graph node completed by an available primitive event. -/
def node : AvailableEvent G cfg → Fin G.nodeCount
  | .commit _ action _ => action.node
  | .internal event _ => event.node

@[simp] theorem node_commit {who : Player}
    (action : CommitAction G who)
    (step : CommitStep G cfg who action) :
    (AvailableEvent.commit who action step).node = action.node := rfl

@[simp] theorem node_internal
    (event : InternalEvent G)
    (step : InternalStep G cfg event) :
    (AvailableEvent.internal event step).node = event.node := rfl

/-- Available events are ready at their completed node. -/
theorem ready (event : AvailableEvent G cfg) :
    Ready G cfg event.node := by
  cases event with
  | commit _ _ step => exact step.ready
  | internal _ step =>
      cases step with
      | sample _ _ _ _ ready _ _ => exact ready
      | reveal _ _ _ _ ready _ _ => exact ready

/-- Available events refer to a graph row. -/
theorem row_get (event : AvailableEvent G cfg) :
    ∃ row : EventNode Player L, G.nodes[event.node]? = some row := by
  cases event with
  | commit _ _ step => exact ⟨step.row, step.row_get⟩
  | internal _ step =>
      cases step with
      | sample row _ row_get _ _ _ _ => exact ⟨row, row_get⟩
      | reveal row _ row_get _ _ _ _ => exact ⟨row, row_get⟩

end AvailableEvent

/-- Execute a commit action from its concrete availability evidence. -/
noncomputable def stepCommit (G : Graph Player L) (cfg : Config G)
    {who : Player} {action : CommitAction G who}
    (step : CommitStep G cfg who action) : PMF (Config G) :=
  PMF.pure
    (cfg.completeNode action.node
      { ty := step.guard.ty, value := step.value })

/-- Execute an internal graph event from its concrete availability evidence. -/
noncomputable def stepInternal (G : Graph Player L) (cfg : Config G)
    {event : InternalEvent G}
    (step : InternalStep G cfg event) : PMF (Config G) :=
  match step with
  | .sample _ dist _ _ _ env _ =>
      (dist.eval env).map fun value =>
        cfg.completeNode event.node { ty := dist.ty, value := value }
  | .reveal row _ _ _ _ value _ =>
      PMF.pure
        (cfg.completeNode event.node { ty := row.ty, value := value })

/-- Execute an available primitive graph event. -/
noncomputable def stepAvailableEvent (G : Graph Player L) (cfg : Config G)
    (event : AvailableEvent G cfg) : PMF (Config G) :=
  match event with
  | .commit _ _ step => stepCommit G cfg step
  | .internal _ step => stepInternal G cfg step

/-- Completing two distinct ready events with fixed output values is
schedule-independent at the raw graph configuration level.  Later execution
theorems refine concrete commit/sample/reveal steps to this common shape. -/
theorem complete_two_distinct_nodes_comm
    {G : Graph Player L} {cfg : Config G}
    {left right : Fin G.nodeCount}
    (valueLeft valueRight : TypedValue L)
    (hne : left ≠ right) :
    (cfg.completeNode left valueLeft).completeNode right valueRight =
      (cfg.completeNode right valueRight).completeNode left valueLeft :=
  Config.completeNode_comm cfg valueLeft valueRight hne

/-- Every supported available primitive event completes its own graph node
with a concrete typed value. -/
theorem stepAvailableEvent_support_completeNode
    {G : Graph Player L} {cfg next : Config G}
    (event : AvailableEvent G cfg)
    (hnext : next ∈ (stepAvailableEvent G cfg event).support) :
    ∃ written : TypedValue L,
      next = cfg.completeNode event.node written := by
  cases event with
  | commit who action step =>
      have hpmf :
          stepAvailableEvent G cfg (.commit who action step) =
            PMF.pure
              (cfg.completeNode action.node
                { ty := step.guard.ty, value := step.value }) := by
        rfl
      rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
      subst next
      exact ⟨{ ty := step.guard.ty, value := step.value }, rfl⟩
  | internal event step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal event
                    (.sample row dist row_get sem_eq ready env env_ok)) =
                PMF.map
                  (fun value =>
                    cfg.completeNode event.node
                      { ty := dist.ty, value := value })
                  (dist.eval env) := by
            rfl
          rw [hpmf] at hnext
          rcases (PMF.mem_support_map_iff _ _ _).mp hnext with
            ⟨value, _hvalue, hnextEq⟩
          subst next
          exact ⟨{ ty := dist.ty, value := value }, rfl⟩
      | reveal row source row_get sem_eq ready value value_ok =>
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal event
                    (.reveal row source row_get sem_eq ready value
                      value_ok)) =
                PMF.pure
                  (cfg.completeNode event.node
                    { ty := row.ty, value := value }) := by
            rfl
          rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
          subst next
          exact ⟨{ ty := row.ty, value := value }, rfl⟩

/-- Availability of an event persists after a distinct ready node completes. -/
theorem AvailableEvent.persist_after_other_ready_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    (event : AvailableEvent G cfg)
    {other : Fin G.nodeCount} {otherRow : EventNode Player L}
    (hotherRow : G.nodes[other]? = some otherRow)
    (hotherReady : Ready G cfg other)
    (written : TypedValue L)
    (hne : event.node ≠ other) :
    ∃ event' : AvailableEvent G (cfg.completeNode other written),
      event'.node = event.node := by
  cases event with
  | commit who action step =>
      rcases
          (show CommitAvailable G
              (cfg.completeNode other written) who action from
            (show CommitAvailable G cfg who action from ⟨step⟩)
              |>.persist_after_other_ready_write
                hwf hotherRow hotherReady written hne) with
        ⟨step'⟩
      exact ⟨.commit who action step', rfl⟩
  | internal internal step =>
      rcases
          (show InternalAvailable G
              (cfg.completeNode other written) internal from
            (show InternalAvailable G cfg internal from ⟨step⟩)
              |>.persist_after_other_ready_write
                hwf hotherRow hotherReady written hne) with
        ⟨step'⟩
      exact ⟨.internal internal step', rfl⟩

/-- Availability of an event persists after a distinct available event
completes with a fixed typed value. -/
theorem AvailableEvent.persist_after_other_available_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    (event other : AvailableEvent G cfg)
    (written : TypedValue L)
    (hne : event.node ≠ other.node) :
    ∃ event' : AvailableEvent G
        (cfg.completeNode other.node written),
      event'.node = event.node := by
  rcases other.row_get with ⟨otherRow, hotherRow⟩
  exact
    event.persist_after_other_ready_write
      hwf hotherRow other.ready written hne

/-- Availability of an event persists after a supported step of a distinct
available event. -/
theorem AvailableEvent.persist_after_other_supported_step
    {G : Graph Player L} (hwf : G.WF)
    {cfg next : Config G}
    (event other : AvailableEvent G cfg)
    (hne : event.node ≠ other.node)
    (hnext : next ∈ (stepAvailableEvent G cfg other).support) :
    ∃ event' : AvailableEvent G next,
      event'.node = event.node := by
  rcases stepAvailableEvent_support_completeNode other hnext with
    ⟨written, hnextEq⟩
  subst next
  exact event.persist_after_other_available_write hwf other written hne

/-- A supported result of an available event remains supported after a
distinct ready node is completed. The target configuration is the same two
node completions, just with the other node completed first. -/
theorem AvailableEvent.support_after_other_ready_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg next : Config G}
    (event : AvailableEvent G cfg)
    {other : Fin G.nodeCount} {otherRow : EventNode Player L}
    (hotherRow : G.nodes[other]? = some otherRow)
    (hotherReady : Ready G cfg other)
    (otherWritten : TypedValue L)
    (hne : event.node ≠ other)
    (hnext : next ∈ (stepAvailableEvent G cfg event).support) :
    ∃ event' : AvailableEvent G (cfg.completeNode other otherWritten),
      event'.node = event.node ∧
        next.completeNode other otherWritten ∈
          (stepAvailableEvent G
            (cfg.completeNode other otherWritten) event').support := by
  cases event with
  | commit who action step =>
      have htargetNot :
          G.nodeTarget other ∉ step.row.sem.reads :=
        Ready.nodeTarget_not_mem_reads_of_ready
          hwf step.row_get hotherRow step.ready hotherReady
      have hnotRead :
          ∀ ref, ref ∈ step.guard.choiceReads →
            ref.field ≠ G.nodeTarget other := by
        intro ref href heq
        apply htargetNot
        rw [step.sem_eq]
        exact Finset.mem_image.mpr ⟨ref, href, heq⟩
      let step' : CommitStep G
          (cfg.completeNode other otherWritten) who action :=
        { row := step.row
          guard := step.guard
          row_get := step.row_get
          sem_eq := step.sem_eq
          ready := step.ready.completeNode_of_ne hne
          value := step.value
          value_ok := step.value_ok
          env := step.env
          env_ok :=
            ReadEnv.ofStore?_completeNode_of_not_read
              (value := otherWritten) step.env_ok hnotRead
          guard_ok := step.guard_ok }
      refine ⟨.commit who action step', rfl, ?_⟩
      have hpmf :
          stepAvailableEvent G cfg (.commit who action step) =
            PMF.pure
              (cfg.completeNode action.node
                { ty := step.guard.ty, value := step.value }) := by
        rfl
      rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
      subst next
      change
        (cfg.completeNode action.node
            { ty := step.guard.ty, value := step.value }).completeNode
            other otherWritten ∈
          (stepAvailableEvent G
            (cfg.completeNode other otherWritten)
            (.commit who action step')).support
      dsimp [stepAvailableEvent, stepCommit]
      rw [PMF.support_pure, Set.mem_singleton_iff]
      exact Config.completeNode_comm cfg
        { ty := step.guard.ty, value := step.value } otherWritten hne
  | internal internalEvent step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          have htargetNot :
              G.nodeTarget other ∉ row.sem.reads :=
            Ready.nodeTarget_not_mem_reads_of_ready
              hwf row_get hotherRow ready hotherReady
          have hnotRead :
              ∀ ref, ref ∈ dist.reads →
                ref.field ≠ G.nodeTarget other := by
            intro ref href heq
            apply htargetNot
            rw [sem_eq]
            exact Finset.mem_image.mpr ⟨ref, href, heq⟩
          let step' : InternalStep G
              (cfg.completeNode other otherWritten) internalEvent :=
            .sample row dist row_get sem_eq
              (ready.completeNode_of_ne hne) env
              (ReadEnv.ofStore?_completeNode_of_not_read
                (value := otherWritten) env_ok hnotRead)
          refine ⟨.internal internalEvent step', rfl, ?_⟩
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal internalEvent
                    (.sample row dist row_get sem_eq ready env env_ok)) =
                PMF.map
                  (fun value =>
                    cfg.completeNode internalEvent.node
                      { ty := dist.ty, value := value })
                  (dist.eval env) := by
            rfl
          rw [hpmf] at hnext
          rcases (PMF.mem_support_map_iff _ _ _).mp hnext with
            ⟨value, hvalue, hnextEq⟩
          subst next
          change
            (cfg.completeNode internalEvent.node
                { ty := dist.ty, value := value }).completeNode
                other otherWritten ∈
              (stepAvailableEvent G
                (cfg.completeNode other otherWritten)
                (.internal internalEvent step')).support
          dsimp [stepAvailableEvent, stepInternal]
          exact
            (PMF.mem_support_map_iff _ _ _).mpr
              ⟨value, hvalue,
                (Config.completeNode_comm cfg
                  { ty := dist.ty, value := value }
                  otherWritten hne).symm⟩
      | reveal row source row_get sem_eq ready value value_ok =>
          have htargetNot :
              G.nodeTarget other ∉ row.sem.reads :=
            Ready.nodeTarget_not_mem_reads_of_ready
              hwf row_get hotherRow ready hotherReady
          have hsourceNe : source ≠ G.nodeTarget other := by
            intro heq
            apply htargetNot
            rw [sem_eq]
            simp [NodeSem.reads, heq]
          have hvalue :
              Store.getAs (cfg.completeNode other otherWritten).store
                source row.ty = some value := by
            rw [Config.completeNode]
            exact
              (Store.getAs_set_ne cfg.store hsourceNe
                otherWritten row.ty).trans value_ok
          let step' : InternalStep G
              (cfg.completeNode other otherWritten) internalEvent :=
            .reveal row source row_get sem_eq
              (ready.completeNode_of_ne hne) value hvalue
          refine ⟨.internal internalEvent step', rfl, ?_⟩
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal internalEvent
                    (.reveal row source row_get sem_eq ready value
                      value_ok)) =
                PMF.pure
                  (cfg.completeNode internalEvent.node
                    { ty := row.ty, value := value }) := by
            rfl
          rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
          subst next
          change
            (cfg.completeNode internalEvent.node
                { ty := row.ty, value := value }).completeNode
                other otherWritten ∈
              (stepAvailableEvent G
                (cfg.completeNode other otherWritten)
                (.internal internalEvent step')).support
          dsimp [stepAvailableEvent, stepInternal]
          rw [PMF.support_pure, Set.mem_singleton_iff]
          exact Config.completeNode_comm cfg
            { ty := row.ty, value := value } otherWritten hne

/-- Two distinct available primitive graph events form a diamond: choosing
one supported result for each event at the source gives supported executions in
both orders, and the resulting graph configurations are equal. -/
theorem supported_available_events_diamond
    {G : Graph Player L} (hwf : G.WF)
    {cfg leftNext rightNext : Config G}
    (left right : AvailableEvent G cfg)
    (hne : left.node ≠ right.node)
    (hleft :
      leftNext ∈ (stepAvailableEvent G cfg left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G cfg right).support) :
    ∃ rightAfterLeft : AvailableEvent G leftNext,
      ∃ leftAfterRight : AvailableEvent G rightNext,
        ∃ finalLeft finalRight : Config G,
          finalLeft ∈
            (stepAvailableEvent G leftNext rightAfterLeft).support ∧
          finalRight ∈
            (stepAvailableEvent G rightNext leftAfterRight).support ∧
          finalLeft = finalRight := by
  rcases stepAvailableEvent_support_completeNode left hleft with
    ⟨leftWritten, hleftEq⟩
  rcases stepAvailableEvent_support_completeNode right hright with
    ⟨rightWritten, hrightEq⟩
  rcases left.row_get with ⟨leftRow, hleftRow⟩
  rcases right.row_get with ⟨rightRow, hrightRow⟩
  rcases
      right.support_after_other_ready_write
        hwf hleftRow left.ready leftWritten hne.symm hright with
    ⟨rightAfterLeft, hrightAfterLeftNode, hrightAfterLeft⟩
  rcases
      left.support_after_other_ready_write
        hwf hrightRow right.ready rightWritten hne hleft with
    ⟨leftAfterRight, hleftAfterRightNode, hleftAfterRight⟩
  subst leftNext
  subst rightNext
  refine
    ⟨rightAfterLeft, leftAfterRight,
      (cfg.completeNode right.node rightWritten).completeNode left.node
        leftWritten,
      (cfg.completeNode left.node leftWritten).completeNode right.node
        rightWritten,
      ?_, ?_, ?_⟩
  · simpa using hrightAfterLeft
  · simpa using hleftAfterRight
  · exact
      (Config.completeNode_comm cfg
        leftWritten rightWritten hne).symm

/-- Supported completions of two distinct available primitive events commute
at the raw configuration level. -/
theorem supported_available_events_complete_comm
    {G : Graph Player L} {cfg leftNext rightNext : Config G}
    (left right : AvailableEvent G cfg)
    (hne : left.node ≠ right.node)
    (hleft :
      leftNext ∈ (stepAvailableEvent G cfg left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G cfg right).support) :
    ∃ leftWritten rightWritten : TypedValue L,
      leftNext = cfg.completeNode left.node leftWritten ∧
      rightNext = cfg.completeNode right.node rightWritten ∧
      leftNext.completeNode right.node rightWritten =
        rightNext.completeNode left.node leftWritten := by
  rcases stepAvailableEvent_support_completeNode left hleft with
    ⟨leftWritten, hleftEq⟩
  rcases stepAvailableEvent_support_completeNode right hright with
    ⟨rightWritten, hrightEq⟩
  refine ⟨leftWritten, rightWritten, hleftEq, hrightEq, ?_⟩
  subst leftNext
  subst rightNext
  exact Config.completeNode_comm cfg leftWritten rightWritten hne

theorem Config.done_ssubset_completeNode
    {G : Graph Player L} {cfg : Config G}
    {node : Fin G.nodeCount} (hnotDone : node ∉ cfg.done)
    (value : TypedValue L) :
    cfg.done ⊂ (cfg.completeNode node value).done := by
  dsimp [Config.completeNode]
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_insert node cfg.done, ?_⟩
  intro heq
  exact hnotDone (by
    rw [heq]
    exact Finset.mem_insert_self node cfg.done)

/-- Every supported available primitive event strictly grows the completed-node
downset. -/
theorem done_ssubset_of_stepAvailableEvent_support
    (G : Graph Player L) {cfg next : Config G}
    (event : AvailableEvent G cfg)
    (hnext : next ∈ (stepAvailableEvent G cfg event).support) :
    cfg.done ⊂ next.done := by
  cases event with
  | commit who action step =>
      have hpmf :
          stepAvailableEvent G cfg (.commit who action step) =
            PMF.pure
              (cfg.completeNode action.node
                { ty := step.guard.ty, value := step.value }) := by
        rfl
      rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
      subst next
      exact Config.done_ssubset_completeNode step.ready.1 _
  | internal event step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal event
                    (.sample row dist row_get sem_eq ready env env_ok)) =
                PMF.map
                  (fun value =>
                    cfg.completeNode event.node
                      { ty := dist.ty, value := value })
                  (dist.eval env) := by
            rfl
          rw [hpmf] at hnext
          rcases (PMF.mem_support_map_iff _ _ _).mp hnext with
            ⟨value, _hvalue, hnextEq⟩
          subst next
          exact Config.done_ssubset_completeNode ready.1 _
      | reveal row source row_get sem_eq ready value value_ok =>
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal event
                    (.reveal row source row_get sem_eq ready value
                      value_ok)) =
                PMF.pure
                  (cfg.completeNode event.node
                    { ty := row.ty, value := value }) := by
            rfl
          rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
          subst next
          exact Config.done_ssubset_completeNode ready.1 _

/-- Configurations reachable by executing available graph events from the
initial configuration. This is the semantic domain for graph-level theorems:
raw `Config` values remain freely constructible, but compiled-game properties
should quantify over `Reachable` configurations. -/
inductive Reachable (G : Graph Player L) : Config G → Prop where
  | initial :
      Reachable G (Config.initial G)
  | step {cfg next : Config G} :
      Reachable G cfg →
      (event : AvailableEvent G cfg) →
      next ∈ (stepAvailableEvent G cfg event).support →
      Reachable G next

theorem reachable_storeCoherent
    {G : Graph Player L} (hwf : G.WF) :
    ∀ {cfg : Config G}, Reachable G cfg → StoreCoherent G cfg := by
  intro cfg hreach
  induction hreach with
  | initial =>
      exact initial_storeCoherent G
  | step hprev event hnext ih =>
      rename_i source target
      cases event with
      | commit who action step =>
          have hpmf :
              stepAvailableEvent G source (.commit who action step) =
                PMF.pure
                  (source.completeNode action.node
                    { ty := step.guard.ty, value := step.value }) := by
            rfl
          rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
          subst target
          have hnodeWF := hwf action.node step.row step.row_get
          have hty : step.row.ty = step.guard.ty := by
            unfold Graph.nodeWFAt at hnodeWF
            rw [step.sem_eq] at hnodeWF
            exact hnodeWF.2.1
          exact
            ih.completeNodeTyped step.row_get
              { ty := step.guard.ty, value := step.value } hty.symm
      | internal event step =>
          cases step with
          | sample row dist row_get sem_eq ready env env_ok =>
              have hnodeWF := hwf event.node row row_get
              have hty : row.ty = dist.ty := by
                unfold Graph.nodeWFAt at hnodeWF
                rw [sem_eq] at hnodeWF
                exact hnodeWF.2.1
              have hpmf :
                  stepAvailableEvent G source
                      (.internal event
                        (.sample row dist row_get sem_eq ready env env_ok)) =
                    PMF.map
                      (fun value =>
                        source.completeNode event.node
                          { ty := dist.ty, value := value })
                      (dist.eval env) := by
                rfl
              rw [hpmf] at hnext
              rcases (PMF.mem_support_map_iff _ _ _).mp hnext with
                ⟨value, _hvalue, hnextEq⟩
              subst target
              exact
                ih.completeNodeTyped row_get
                  { ty := dist.ty, value := value } hty.symm
          | reveal row sourceField row_get sem_eq ready value value_ok =>
              have hpmf :
                  stepAvailableEvent G source
                      (.internal event
                        (.reveal row sourceField row_get sem_eq ready value
                          value_ok)) =
                    PMF.pure
                      (source.completeNode event.node
                        { ty := row.ty, value := value }) := by
                rfl
              rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
              subst target
              exact ih.completeNode row_get value

theorem StoreCoherent.hasRefOfReadyRead
    {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF)
    (hcoherent : StoreCoherent G cfg)
    {node : Fin G.nodeCount} {event : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (hready : Ready G cfg node)
    {ref : FieldRef L}
    (hread : ref.field ∈ event.sem.reads)
    (href :
      ∃ spec, G.field? ref.field = some spec ∧ spec.ty = ref.ty) :
    ∃ value : L.Val ref.ty,
      Store.getAs cfg.store ref.field ref.ty = some value := by
  rcases href with ⟨spec, hfield, hty⟩
  have hsourceReady :
      match spec.source with
      | .initial _ => True
      | .event writer => cfg.nodeDone writer := by
    cases hsource : spec.source with
    | initial value =>
        trivial
    | event writer =>
        have hfieldEq : ref.field = G.nodeTarget writer :=
          G.field_eq_nodeTarget_of_event_source hfield hsource
        have hwriterNode :
            ∃ writerEvent, G.nodes[writer]? = some writerEvent :=
          G.node_get_of_field_event_source hfield hsource
        rcases hwriterNode with ⟨writerEvent, hwriterEvent⟩
        have hwriterLtNode : writer < (node : Nat) := by
          have hwfAvailable :
              G.fieldAvailableBefore (node : Nat) ref.field = true := by
            exact (hwf node event hnode).1 ref.field hread
          unfold Graph.fieldAvailableBefore at hwfAvailable
          rw [hfield] at hwfAvailable
          simpa [hsource] using hwfAvailable
        let prior : Fin G.nodeCount :=
          ⟨writer, Nat.lt_trans hwriterLtNode node.isLt⟩
        have hpriorGet :
            G.nodes[(prior : Nat)]? = some writerEvent := hwriterEvent
        have hprereq : prior ∈ G.prereqs node := by
          apply G.nodeTarget_mem_prereqs_of_read
            (node := node) (prior := prior)
            (event := event) (priorEvent := writerEvent)
            hnode hpriorGet hwriterLtNode
          simpa [prior, hfieldEq] using hread
        change writer ∈ cfg.doneIds
        exact Finset.mem_image.mpr ⟨prior, hready.2 hprereq, rfl⟩
  rcases hcoherent ref.field spec hfield hsourceReady with ⟨value, hvalue⟩
  exact ⟨cast (congrArg L.Val hty) value,
    Store.getAs_cast cfg.store ref.field hty hvalue⟩

theorem StoreCoherent.readEnvOfReady
    {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF)
    (hcoherent : StoreCoherent G cfg)
    {node : Fin G.nodeCount} {event : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    (hready : Ready G cfg node)
    {refs : Finset (FieldRef L)}
    (hreads :
      ∀ ref, ref ∈ refs → ref.field ∈ event.sem.reads)
    (htyped :
      ∀ ref, ref ∈ refs →
        ∃ spec, G.field? ref.field = some spec ∧ spec.ty = ref.ty) :
    ∃ env : ReadEnv L refs,
      ReadEnv.ofStore? cfg.store refs = some env := by
  unfold ReadEnv.ofStore?
  have havailable :
      ∀ ref, ref ∈ refs →
        ∃ value, Store.getAs cfg.store ref.field ref.ty = some value := by
    intro ref href
    exact hcoherent.hasRefOfReadyRead hwf hnode hready
      (hreads ref href) (htyped ref href)
  refine ⟨ReadEnv.ofStore cfg.store refs havailable, ?_⟩
  rw [dif_pos havailable]

/-- Reachable graph configurations packaged as a state type. -/
abbrev ReachableConfig (G : Graph Player L) := { cfg : Config G // Reachable G cfg }

theorem exists_availableEvent_of_not_terminal
    {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    {state : ReachableConfig G}
    (hterminal : ¬ Terminal G state.1) :
    Nonempty (AvailableEvent G state.1) := by
  classical
  rcases exists_ready_of_not_terminal G state.1 hterminal with
    ⟨node, hready⟩
  rcases G.nodes_get_of_fin node with ⟨row, hrow⟩
  have hcoherent : StoreCoherent G state.1 :=
    reachable_storeCoherent hwf state.2
  cases hsem : row.sem with
  | sample dist =>
      have hnodeWF := hwf node row hrow
      unfold Graph.nodeWFAt at hnodeWF
      rw [hsem] at hnodeWF
      rcases hcoherent.readEnvOfReady hwf hrow hready
          (refs := dist.reads)
          (by
            intro ref href
            rw [hsem]
            exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
          (by
            intro ref href
            rcases hnodeWF.2.2.2 ref href with
              ⟨spec, hget, hty, _howner⟩
            exact ⟨spec, hget, hty⟩) with
        ⟨env, henv⟩
      exact
        ⟨AvailableEvent.internal
          { node := node }
          (InternalStep.sample row dist hrow hsem hready env henv)⟩
  | commit who guard =>
      have hnodeWF := hwf node row hrow
      unfold Graph.nodeWFAt at hnodeWF
      rw [hsem] at hnodeWF
      rcases hcoherent.readEnvOfReady hwf hrow hready
          (refs := guard.choiceReads)
          (by
            intro ref href
            rw [hsem]
            exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
          (by
            intro ref href
            rcases hnodeWF.2.2.2 ref href with
              ⟨spec, hget, hty, _howner⟩
            exact ⟨spec, hget, hty⟩) with
        ⟨env, henv⟩
      rcases hguards hrow hsem env with ⟨value, hvalue⟩
      let action : CommitAction G who :=
        { node := node, value := { ty := guard.ty, value := value } }
      have hvalueOk : action.value.as? guard.ty = some value := by
        simp [action, TypedValue.as?]
      exact
        ⟨AvailableEvent.commit who action
          { row := row
            guard := guard
            row_get := hrow
            sem_eq := hsem
            ready := hready
            value := value
            value_ok := hvalueOk
            env := env
            env_ok := henv
            guard_ok := hvalue }⟩
  | reveal source =>
      have hnodeWF := hwf node row hrow
      unfold Graph.nodeWFAt at hnodeWF
      rw [hsem] at hnodeWF
      rcases hnodeWF.2 with
        ⟨sourceSpec, hsource, hty, _hsourceOwner, _howner⟩
      rcases hcoherent.hasRefOfReadyRead hwf hrow hready
          (ref := { field := source, ty := row.ty })
          (by simp [hsem, NodeSem.reads])
          ⟨sourceSpec, hsource, hty⟩ with
        ⟨value, hvalue⟩
      exact
        ⟨AvailableEvent.internal
          { node := node }
          (InternalStep.reveal row source hrow hsem hready value hvalue)⟩

/-- Step by an available primitive event. Each supported raw successor carries
the corresponding reachability proof. -/
noncomputable def stepAvailable (G : Graph Player L) (state : ReachableConfig G)
    (event : AvailableEvent G state.1) :
    PMF (ReachableConfig G) :=
  (stepAvailableEvent G state.1 event).bindOnSupport fun next hnext =>
    PMF.pure ⟨next, Reachable.step state.2 event hnext⟩

/-- Common public information at a graph state.

The completed-node set is public protocol history. Field lookup exposes only
public fields whose values are available: initial public fields and public
event fields whose writer node has completed. -/
structure PublicObservation (G : Graph Player L) where
  done : Finset (Fin G.nodeCount)
  fieldValue? :
    (field : Fin G.fieldCount) →
      Option (L.Val (G.fieldRow field).ty)

namespace PublicObservation

variable {G : Graph Player L}

@[ext] theorem ext {left right : PublicObservation G}
    (hdone : left.done = right.done)
    (hfields : ∀ field, left.fieldValue? field = right.fieldValue? field) :
    left = right := by
  cases left with
  | mk leftDone leftFields =>
  cases right with
  | mk rightDone rightFields =>
  dsimp at hdone hfields
  subst rightDone
  congr
  funext field
  exact hfields field

noncomputable instance instFintype
    [∀ field : Fin G.fieldCount,
      Fintype (L.Val (G.fieldRow field).ty)] :
    Fintype (PublicObservation G) := by
  classical
  let snapshot :=
    Finset (Fin G.nodeCount) ×
      ((field : Fin G.fieldCount) →
        Option (L.Val (G.fieldRow field).ty))
  let e : snapshot ≃ PublicObservation G :=
    { toFun := fun data =>
        { done := data.1
          fieldValue? := data.2 }
      invFun := fun obs => (obs.done, obs.fieldValue?)
      left_inv := by
        intro data
        rfl
      right_inv := by
        intro obs
        cases obs
        rfl }
  exact Fintype.ofEquiv snapshot e

/-- Lookup a public observation by an external typed field reference. Invalid
or type-mismatched references are absent. -/
noncomputable def value? (obs : PublicObservation G)
    (ref : FieldRef L) : Option (L.Val ref.ty) := by
  classical
  exact
    if hfield : ref.field < G.fieldCount then
      let field : Fin G.fieldCount := ⟨ref.field, hfield⟩
      if hty : (G.fieldRow field).ty = ref.ty then
        match obs.fieldValue? field with
        | none => none
        | some value => some (cast (congrArg L.Val hty) value)
      else
        none
    else
      none

end PublicObservation

/-- Public observation induced by a graph configuration. -/
noncomputable def publicObserve (G : Graph Player L) (cfg : Config G) :
    PublicObservation G := by
  classical
  exact
    { done := cfg.done
      fieldValue? := fun field =>
        let spec := G.fieldRow field
        if spec.owner = none then
          match spec.source with
          | .initial _ =>
              Store.getAs cfg.store field spec.ty
          | .event node =>
              if hnode : node < G.nodeCount then
                if cfg.nodeDone node then
                  Store.getAs cfg.store field spec.ty
                else
                  none
              else
                none
        else
          none }

/-- Player observation at the event-graph layer.

`ready` is the player's current commit frontier. `value?` exposes only fields
in the choice footprint of a ready commit node owned by the player. Values
outside that local commit view are hidden, even if an external schedule happened
to execute unrelated events earlier. -/
structure Observation (G : Graph Player L) (_who : Player) where
  ready : Finset (Fin G.nodeCount)
  fieldValue? :
    Fin G.nodeCount →
      (field : Fin G.fieldCount) →
        Option (L.Val (G.fieldRow field).ty)

namespace Observation

variable {G : Graph Player L} {who : Player}

@[ext] theorem ext {left right : Observation G who}
    (hready : left.ready = right.ready)
    (hfields :
      ∀ node field, left.fieldValue? node field =
        right.fieldValue? node field) :
    left = right := by
  cases left with
  | mk leftReady leftFields =>
  cases right with
  | mk rightReady rightFields =>
  dsimp at hready hfields
  subst rightReady
  congr
  funext node field
  exact hfields node field

noncomputable instance instFintype
    [∀ field : Fin G.fieldCount,
      Fintype (L.Val (G.fieldRow field).ty)] :
    Fintype (Observation G who) := by
  classical
  let snapshot :=
    Finset (Fin G.nodeCount) ×
      ((node : Fin G.nodeCount) →
        (field : Fin G.fieldCount) →
          Option (L.Val (G.fieldRow field).ty))
  let e : snapshot ≃ Observation G who :=
    { toFun := fun data =>
        { ready := data.1
          fieldValue? := data.2 }
      invFun := fun obs => (obs.ready, obs.fieldValue?)
      left_inv := by
        intro data
        rfl
      right_inv := by
        intro obs
        cases obs
        rfl }
  exact Fintype.ofEquiv snapshot e

/-- Lookup a player observation by a ready commit node and an external typed
field reference. Invalid or type-mismatched references are absent. -/
noncomputable def value? (obs : Observation G who)
    (node : Fin G.nodeCount) (ref : FieldRef L) :
    Option (L.Val ref.ty) := by
  classical
  exact
    if hfield : ref.field < G.fieldCount then
      let field : Fin G.fieldCount := ⟨ref.field, hfield⟩
      if hty : (G.fieldRow field).ty = ref.ty then
        match obs.fieldValue? node field with
        | none => none
        | some value => some (cast (congrArg L.Val hty) value)
      else
        none
    else
      none

end Observation

/-- The graph-causal view visible to `who` at the current configuration. -/
noncomputable def observe (G : Graph Player L) (cfg : Config G)
    (who : Player) : Observation G who := by
  classical
  exact
    { ready :=
        (Finset.univ : Finset (Fin G.nodeCount)).filter fun node =>
          match G.node? node with
          | some (.commit actor _guard) => actor = who ∧ Ready G cfg node
          | _ => False
      fieldValue? := fun node field =>
        match G.node? node with
        | some (.commit actor guard) =>
            if _hactor : actor = who then
              if _hready : Ready G cfg node then
                let ref : FieldRef L :=
                  { field := field, ty := (G.fieldRow field).ty }
                if _hread : ref ∈ guard.choiceReads then
                  Store.getAs cfg.store field ref.ty
                else
                  none
              else
                none
            else
              none
        | _ => none }

theorem publicObserve_completeNode_comm
    (G : Graph Player L) (cfg : Config G)
    {left right : Fin G.nodeCount}
    (valueLeft valueRight : TypedValue L)
    (hne : left ≠ right) :
    publicObserve G
        ((cfg.completeNode left valueLeft).completeNode right valueRight) =
      publicObserve G
        ((cfg.completeNode right valueRight).completeNode left valueLeft) := by
  rw [Config.completeNode_comm cfg valueLeft valueRight hne]

theorem observe_completeNode_comm
    (G : Graph Player L) (cfg : Config G)
    {left right : Fin G.nodeCount}
    (valueLeft valueRight : TypedValue L)
    (hne : left ≠ right) (who : Player) :
    observe G
        ((cfg.completeNode left valueLeft).completeNode right valueRight)
        who =
      observe G
        ((cfg.completeNode right valueRight).completeNode left valueLeft)
        who := by
  rw [Config.completeNode_comm cfg valueLeft valueRight hne]

end EventGraph

end Vegas
