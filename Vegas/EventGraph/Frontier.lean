import GameTheory.Core.JointAction
import Vegas.EventGraph.Execution

/-!
# Event-graph frontiers

The frontier API is the game-facing boundary of an event graph state: ready
strategic commit nodes grouped by player, ready internal nodes, and player
round actions over the ready commit frontier.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A commit node owned by `who` is ready at `cfg`. -/
def ReadyCommitNode (G : Graph Player L) (cfg : Config G)
    (who : Player) (node : Fin G.nodeCount) : Prop :=
  ∃ row guard,
    G.nodes[node]? = some row ∧
      row.sem = .commit who guard ∧
        Ready G cfg node

/-- An internal node is ready at `cfg`. -/
def ReadyInternalNode (G : Graph Player L) (cfg : Config G)
    (node : Fin G.nodeCount) : Prop :=
  ∃ row,
    G.nodes[node]? = some row ∧
      (match row.sem with
       | .sample _ => True
       | .reveal _ => True
       | .commit _ _ => False) ∧
        Ready G cfg node

noncomputable instance instDecidableReadyCommitNode
    (G : Graph Player L) (cfg : Config G)
    (who : Player) (node : Fin G.nodeCount) :
    Decidable (ReadyCommitNode G cfg who node) := by
  classical
  unfold ReadyCommitNode
  infer_instance

noncomputable instance instDecidableReadyInternalNode
    (G : Graph Player L) (cfg : Config G)
    (node : Fin G.nodeCount) :
    Decidable (ReadyInternalNode G cfg node) := by
  classical
  unfold ReadyInternalNode
  infer_instance

/-- Ready strategic commit nodes owned by one player. -/
noncomputable def readyCommitNodes (G : Graph Player L)
    (cfg : Config G) (who : Player) : Finset (Fin G.nodeCount) :=
  (Finset.univ : Finset (Fin G.nodeCount)).filter
    (ReadyCommitNode G cfg who)

/-- Player observations expose exactly the player's ready commit frontier. -/
theorem observe_ready_eq_readyCommitNodes
    (G : Graph Player L) (cfg : Config G) (who : Player) :
    (observe G cfg who).ready = readyCommitNodes G cfg who := by
  classical
  ext node
  unfold observe readyCommitNodes
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change
    (match G.node? (node : Nat) with
     | some (.commit actor _guard) => actor = who ∧ Ready G cfg node
     | _ => False) ↔
      ReadyCommitNode G cfg who node
  rw [Graph.node?_nodeRow]
  cases hsem : (G.nodeRow node).sem with
  | sample dist =>
      simp [ReadyCommitNode, hsem]
  | reveal source =>
      simp [ReadyCommitNode, hsem]
  | commit actor guard =>
      by_cases hactor : actor = who
      · subst actor
        simp [ReadyCommitNode, hsem]
      · simp [ReadyCommitNode, hsem, hactor]

/-- Equal player observations have the same ready commit frontier. -/
theorem readyCommitNodes_eq_of_observe_eq
    {G : Graph Player L} {left right : Config G} {who : Player}
    (hobs : observe G left who = observe G right who) :
    readyCommitNodes G left who = readyCommitNodes G right who := by
  rw [← observe_ready_eq_readyCommitNodes G left who,
    ← observe_ready_eq_readyCommitNodes G right who, hobs]

/-- Ready operational/chance nodes. -/
noncomputable def readyInternalNodes (G : Graph Player L)
    (cfg : Config G) : Finset (Fin G.nodeCount) :=
  (Finset.univ : Finset (Fin G.nodeCount)).filter
    (ReadyInternalNode G cfg)

/-- Public observations determine the ready internal frontier. -/
theorem readyInternalNodes_eq_of_publicObserve_eq
    {G : Graph Player L} {left right : Config G}
    (hobs : publicObserve G left = publicObserve G right) :
    readyInternalNodes G left = readyInternalNodes G right := by
  have hdone : left.done = right.done :=
    congrArg PublicObservation.done hobs
  ext node
  unfold readyInternalNodes ReadyInternalNode Ready
  simp [hdone]

/-- Players with at least one ready strategic commit node. -/
noncomputable def activePlayers [Fintype Player]
    (G : Graph Player L) (cfg : Config G) : Finset Player :=
  (Finset.univ : Finset Player).filter fun who =>
    (readyCommitNodes G cfg who).Nonempty

/-- Frontier terminality is graph terminality: every graph node is complete. -/
abbrev terminal (G : Graph Player L) (cfg : Config G) : Prop :=
  Terminal G cfg

namespace ReadyCommitNode

theorem ready {G : Graph Player L} {cfg : Config G} {who : Player}
    {node : Fin G.nodeCount}
    (h : ReadyCommitNode G cfg who node) :
    Ready G cfg node := by
  rcases h with ⟨_row, _guard, _hget, _hsem, hready⟩
  exact hready

end ReadyCommitNode

theorem activePlayers_eq_empty_of_terminal [Fintype Player]
    (G : Graph Player L) {cfg : Config G}
    (hterminal : Terminal G cfg) :
    activePlayers G cfg = ∅ := by
  classical
  ext who
  constructor
  · intro hmem
    rcases (Finset.mem_filter.mp hmem).2 with ⟨node, hnodeMem⟩
    have hreadyCommit : ReadyCommitNode G cfg who node :=
      (Finset.mem_filter.mp hnodeMem).2
    exact False.elim (hreadyCommit.ready.1 (hterminal node))
  · intro hmem
    cases hmem

theorem InternalAvailable.of_readyInternalNode
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G}
    (hcoherent : StoreCoherent G cfg)
    {node : Fin G.nodeCount}
    (hreadyInternal : ReadyInternalNode G cfg node) :
    InternalAvailable G cfg { node := node } := by
  rcases hreadyInternal with ⟨row, hrow, hinternal, hready⟩
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
        ⟨InternalStep.sample row dist hrow hsem hready env henv⟩
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
        ⟨InternalStep.reveal row source hrow hsem hready value hvalue⟩
  | commit _ _ =>
      rw [hsem] at hinternal
      cases hinternal

theorem InternalAvailable.readyInternalNode
    {G : Graph Player L} {cfg : Config G}
    {event : InternalEvent G}
    (havailable : InternalAvailable G cfg event) :
    ReadyInternalNode G cfg event.node := by
  rcases havailable with ⟨step⟩
  cases step with
  | sample row _ row_get sem_eq ready _ _ =>
      exact ⟨row, row_get, by simp [sem_eq], ready⟩
  | reveal row _ row_get sem_eq ready _ _ =>
      exact ⟨row, row_get, by simp [sem_eq], ready⟩

/-- A player round action assigns node-typed values to graph nodes.  Local
availability requires assigning exactly the player's ready commit frontier. -/
structure FrontierAction (G : Graph Player L) (who : Player) where
  value? : (node : Fin G.nodeCount) →
    Option (L.Val (G.nodeRow node).ty)

namespace FrontierAction

noncomputable instance instFintype
    (G : Graph Player L) (who : Player)
    [∀ node : Fin G.nodeCount, Fintype (L.Val (G.nodeRow node).ty)] :
    Fintype (FrontierAction G who) := by
  classical
  let values :=
    (node : Fin G.nodeCount) → Option (L.Val (G.nodeRow node).ty)
  let actionEquiv : values ≃ FrontierAction G who :=
    { toFun := fun value? => { value? := value? }
      invFun := fun action => action.value?
      left_inv := by
        intro value?
        rfl
      right_inv := by
        intro action
        cases action
        rfl }
  exact Fintype.ofEquiv values actionEquiv

/-- Local legality of a frontier action for one player at one graph state. -/
noncomputable def Available (G : Graph Player L) (cfg : Config G)
    (who : Player) (action : FrontierAction G who) : Prop :=
  ∀ node,
    if _hready : ReadyCommitNode G cfg who node then
      ∃ value,
        action.value? node = some value ∧
          CommitAvailable G cfg who
            { node := node, value := G.nodeTypedValue node value }
    else
      action.value? node = none

/-- The empty action assigns no commit values. -/
def none (G : Graph Player L) (who : Player) : FrontierAction G who where
  value? := fun _ => Option.none

theorem Available.commitAvailable_of_value
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : Available G cfg who action)
    {node : Fin G.nodeCount} {value : L.Val (G.nodeRow node).ty}
    (hvalue : action.value? node = some value) :
    CommitAvailable G cfg who
      { node := node, value := G.nodeTypedValue node value } := by
  classical
  have hnode := havailable node
  by_cases hready : ReadyCommitNode G cfg who node
  · rw [dif_pos hready] at hnode
    rcases hnode with ⟨selected, hselected, havailableCommit⟩
    rw [hvalue] at hselected
    cases hselected
    exact havailableCommit
  · rw [dif_neg hready] at hnode
    rw [hvalue] at hnode
    cases hnode

/-- The domain of a locally available frontier action is exactly the player's
ready commit frontier. -/
theorem Available.value?_isSome_iff_readyCommitNode
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : Available G cfg who action)
    {node : Fin G.nodeCount} :
    (∃ value, action.value? node = some value) ↔
      ReadyCommitNode G cfg who node := by
  classical
  constructor
  · intro hsome
    rcases hsome with ⟨value, hvalue⟩
    have hnode := havailable node
    by_cases hready : ReadyCommitNode G cfg who node
    · exact hready
    · rw [dif_neg hready] at hnode
      rw [hvalue] at hnode
      cases hnode
  · intro hready
    have hnode := havailable node
    rw [dif_pos hready] at hnode
    rcases hnode with ⟨value, hvalue, _hcommit⟩
    exact ⟨value, hvalue⟩

/-- The domain of a locally available frontier action is determined by the
player observation's ready frontier. -/
theorem Available.value?_isSome_iff_observe_ready
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : Available G cfg who action)
  {node : Fin G.nodeCount} :
    (∃ value, action.value? node = some value) ↔
      node ∈ (observe G cfg who).ready := by
  rw [observe_ready_eq_readyCommitNodes G cfg who]
  unfold readyCommitNodes
  rw [Finset.mem_filter, havailable.value?_isSome_iff_readyCommitNode]
  simp

theorem commitAvailable_of_observe_eq
    {G : Graph Player L} {left right : Config G} {who : Player}
    {node : Fin G.nodeCount} {value : L.Val (G.nodeRow node).ty}
    (hwf : G.WF)
    (hobs : observe G left who = observe G right who)
    (havailable :
      CommitAvailable G left who
        { node := node, value := G.nodeTypedValue node value }) :
    CommitAvailable G right who
      { node := node, value := G.nodeTypedValue node value } := by
  classical
  rcases havailable with ⟨step⟩
  have hrowEq : G.nodeRow node = step.row := by
    have hcanonical := G.nodes_get?_nodeRow node
    have hrowGet : G.nodes[(node : Nat)]? = some step.row := step.row_get
    rw [hrowGet] at hcanonical
    exact (Option.some.inj hcanonical).symm
  have hnodeSem :
      (G.nodeRow node).sem = NodeSem.commit who step.guard := by
    rw [hrowEq, step.sem_eq]
  have hreadyLeft :
      node ∈ (observe G left who).ready := by
    rw [observe_ready_eq_readyCommitNodes G left who]
    unfold readyCommitNodes ReadyCommitNode
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ node, step.row, step.guard, step.row_get,
        step.sem_eq, step.ready⟩
  have hreadyRight :
      Ready G right node := by
    have hmem : node ∈ (observe G right who).ready := by
      simpa [hobs] using hreadyLeft
    rw [observe_ready_eq_readyCommitNodes G right who] at hmem
    exact (Finset.mem_filter.mp hmem).2.ready
  have hgetEq :
      ∀ ref, ref ∈ step.guard.choiceReads →
        Store.getAs left.store ref.field ref.ty =
          Store.getAs right.store ref.field ref.ty := by
    intro ref href
    rcases ref with ⟨refField, refTy⟩
    have hnodeWF := hwf node step.row step.row_get
    unfold Graph.nodeWFAt at hnodeWF
    rw [step.sem_eq] at hnodeWF
    rcases hnodeWF.2.2.2
        ({ field := refField, ty := refTy } : FieldRef L) href with
      ⟨spec, hfield, hty, _hvisible⟩
    have hfieldLt : refField < G.fieldCount :=
      G.field_lt_fieldCount_of_field?_some hfield
    let field : Fin G.fieldCount := ⟨refField, hfieldLt⟩
    have hrow : G.fieldRow field = spec :=
      G.fieldRow_eq_of_field?_some hfield hfieldLt
    have htyRow : (G.fieldRow field).ty = refTy := by
      rw [hrow, hty]
    have hvalue :
        (observe G left who).value? node
            ({ field := refField, ty := refTy } : FieldRef L) =
          Store.getAs left.store refField refTy := by
      cases htyRow
      have hrefActual :
          ({ field := (field : Nat), ty := (G.fieldRow field).ty } :
            FieldRef L) ∈ step.guard.choiceReads := by
        simpa [field] using href
      simp [Observation.value?, observe, hnodeSem, step.ready,
        hfieldLt, hrefActual, field]
      cases left.store.getAs refField (G.fieldRow field).ty <;> rfl
    have hvalueRight :
        (observe G right who).value? node
            ({ field := refField, ty := refTy } : FieldRef L) =
          Store.getAs right.store refField refTy := by
      cases htyRow
      have hrefActual :
          ({ field := (field : Nat), ty := (G.fieldRow field).ty } :
            FieldRef L) ∈ step.guard.choiceReads := by
        simpa [field] using href
      simp [Observation.value?, observe, hnodeSem, hreadyRight,
        hfieldLt, hrefActual, field]
      cases right.store.getAs refField (G.fieldRow field).ty <;> rfl
    rw [← hvalue, hobs, hvalueRight]
  have henvRight :
      ReadEnv.ofStore? right.store step.guard.choiceReads = some step.env :=
    ReadEnv.ofStore?_eq_of_getAs_eq step.env_ok hgetEq
  refine
    ⟨{ row := step.row
       guard := step.guard
       row_get := step.row_get
       sem_eq := step.sem_eq
       ready := hreadyRight
       value := step.value
       value_ok := step.value_ok
       env := step.env
       env_ok := henvRight
       guard_ok := step.guard_ok }⟩

/-- Local frontier-action legality is determined by the player's graph
observation. -/
theorem Available.of_observe_eq
    {G : Graph Player L} {left right : Config G} {who : Player}
    {action : FrontierAction G who}
    (hwf : G.WF)
    (hobs : observe G left who = observe G right who)
    (havailable : Available G left who action) :
    Available G right who action := by
  classical
  intro node
  by_cases hreadyRight : ReadyCommitNode G right who node
  · rw [dif_pos hreadyRight]
    have hnodeObs : node ∈ (observe G left who).ready := by
      rw [hobs, observe_ready_eq_readyCommitNodes G right who]
      unfold readyCommitNodes
      simp [hreadyRight]
    have hsome :
        ∃ value, action.value? node = some value := by
      exact
        (havailable.value?_isSome_iff_observe_ready).2 hnodeObs
    rcases hsome with ⟨value, hvalue⟩
    refine ⟨value, hvalue, ?_⟩
    exact
      commitAvailable_of_observe_eq hwf hobs
        (havailable.commitAvailable_of_value hvalue)
  · rw [dif_neg hreadyRight]
    by_cases hsome : ∃ value, action.value? node = some value
    · have hnodeObs :
          node ∈ (observe G right who).ready := by
        rw [← hobs]
        exact (havailable.value?_isSome_iff_observe_ready).1 hsome
      rw [observe_ready_eq_readyCommitNodes G right who] at hnodeObs
      exact False.elim
        (hreadyRight (Finset.mem_filter.mp hnodeObs).2)
    · cases hvalue : action.value? node with
      | none => rfl
      | some value =>
          exact False.elim (hsome ⟨value, hvalue⟩)

/-- Equal player observations determine the same local frontier-action menu. -/
theorem available_iff_of_observe_eq
    {G : Graph Player L} {left right : Config G} {who : Player}
    {action : FrontierAction G who}
    (hwf : G.WF)
    (hobs : observe G left who = observe G right who) :
    Available G left who action ↔ Available G right who action :=
  ⟨fun h => h.of_observe_eq hwf hobs,
   fun h => h.of_observe_eq hwf hobs.symm⟩

end FrontierAction

theorem FrontierAction.Available.readyCommitNode_of_value
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : action.Available G cfg who)
    {node : Fin G.nodeCount} {value : L.Val (G.nodeRow node).ty}
    (hvalue : action.value? node = some value) :
    ReadyCommitNode G cfg who node := by
  classical
  have hnode := havailable node
  by_cases hready : ReadyCommitNode G cfg who node
  · exact hready
  · rw [dif_neg hready] at hnode
    rw [hvalue] at hnode
    cases hnode

theorem exists_commitValue_of_readyCommitNode
    {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF) (hcoherent : StoreCoherent G cfg)
    (hguards : GuardLive G)
    {who : Player} {node : Fin G.nodeCount}
    (hreadyCommit : ReadyCommitNode G cfg who node) :
    ∃ value : L.Val (G.nodeRow node).ty,
      CommitAvailable G cfg who
        { node := node, value := G.nodeTypedValue node value } := by
  classical
  rcases hreadyCommit with ⟨row, guard, hrow, hsem, hready⟩
  have hrowEq : G.nodeRow node = row := by
    have hcanonical := G.nodes_get?_nodeRow node
    change G.nodes[(node : Nat)]? = some row at hrow
    rw [hrow] at hcanonical
    exact (Option.some.inj hcanonical).symm
  have hnodeWF := hwf node row hrow
  unfold Graph.nodeWFAt at hnodeWF
  rw [hsem] at hnodeWF
  have hrowTy : row.ty = guard.ty := hnodeWF.2.1
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
  rcases hguards hrow hsem env with ⟨choice, hchoice⟩
  have hnodeTy : (G.nodeRow node).ty = guard.ty := by
    rw [hrowEq]
    exact hrowTy
  let value : L.Val (G.nodeRow node).ty :=
    cast (congrArg L.Val hnodeTy.symm) choice
  have hvalueOk :
      (G.nodeTypedValue node value).as? guard.ty = some choice := by
    simp [value, Graph.nodeTypedValue, TypedValue.as?, hnodeTy]
  refine ⟨value, ?_⟩
  exact
    ⟨{ row := row
       guard := guard
       row_get := hrow
       sem_eq := hsem
       ready := hready
       value := choice
       value_ok := hvalueOk
       env := env
       env_ok := henv
       guard_ok := hchoice }⟩

/-- Canonical live frontier action for one player: choose an arbitrary legal
commit value for every ready commit owned by that player, and no value for all
other nodes. -/
noncomputable def liveFrontierAction
    (G : Graph Player L) (cfg : Config G)
    (hwf : G.WF) (hcoherent : StoreCoherent G cfg)
    (hguards : GuardLive G) (who : Player) :
    FrontierAction G who where
  value? := fun node =>
    if hready : ReadyCommitNode G cfg who node then
      some (Classical.choose
        (exists_commitValue_of_readyCommitNode
          hwf hcoherent hguards hready))
    else
      none

theorem liveFrontierAction_available
    {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF) (hcoherent : StoreCoherent G cfg)
    (hguards : GuardLive G) (who : Player) :
    FrontierAction.Available G cfg who
      (liveFrontierAction G cfg hwf hcoherent hguards who) := by
  classical
  intro node
  by_cases hready : ReadyCommitNode G cfg who node
  · let witness :=
      exists_commitValue_of_readyCommitNode
        hwf hcoherent hguards hready
    rw [dif_pos hready]
    refine
      ⟨Classical.choose witness, ?_,
        Classical.choose_spec witness⟩
    simp [liveFrontierAction, hready]
  · rw [dif_neg hready]
    simp [liveFrontierAction, hready]

theorem exists_legal_frontier_action [Fintype Player]
    {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF) (hcoherent : StoreCoherent G cfg)
    (hguards : GuardLive G)
    (hterminal : ¬ Terminal G cfg) :
    ∃ action : JointAction (fun who => FrontierAction G who),
      JointActionLegal (fun who => FrontierAction G who)
        (activePlayers G) (Terminal G)
        (fun cfg who =>
          { action | FrontierAction.Available G cfg who action })
        cfg action := by
  classical
  refine
    ⟨fun who =>
      if hactive : who ∈ activePlayers G cfg then
        some (liveFrontierAction G cfg hwf hcoherent hguards who)
      else
        none,
      hterminal,
      ?_⟩
  intro who
  by_cases hactive : who ∈ activePlayers G cfg
  · simp [hactive, liveFrontierAction_available hwf hcoherent hguards who]
  · simp [hactive]

theorem exists_legal_frontier_action_of_reachable [Fintype Player]
    {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    {state : ReachableConfig G}
    (hterminal : ¬ Terminal G state.1) :
    ∃ action : JointAction (fun who => FrontierAction G who),
      JointActionLegal (fun who => FrontierAction G who)
        (fun state : ReachableConfig G => activePlayers G state.1)
        (fun state : ReachableConfig G => Terminal G state.1)
        (fun state who =>
          { action | FrontierAction.Available G state.1 who action })
        state action := by
  classical
  have hcoherent : StoreCoherent G state.1 :=
    reachable_storeCoherent hwf state.2
  rcases exists_legal_frontier_action
      (G := G) (cfg := state.1)
      hwf hcoherent hguards hterminal with
    ⟨action, hlegal⟩
  exact ⟨action, hlegal⟩

/-- If no player has a ready commit at a reachable nonterminal graph state,
progress is operational/chance work: an internal event is available. -/
theorem exists_internal_available_of_no_active [Fintype Player]
    {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    {state : ReachableConfig G}
    (hterminal : ¬ Terminal G state.1)
    (hactive : activePlayers G state.1 = ∅) :
    ∃ event : InternalEvent G, InternalAvailable G state.1 event := by
  classical
  rcases exists_availableEvent_of_not_terminal
      hwf hguards hterminal with
    ⟨event⟩
  cases event with
  | commit who action step =>
      have hreadyCommit :
          ReadyCommitNode G state.1 who action.node :=
        ⟨step.row, step.guard, step.row_get, step.sem_eq, step.ready⟩
      have hnodeMem :
          action.node ∈ readyCommitNodes G state.1 who := by
        unfold readyCommitNodes
        simp [hreadyCommit]
      have hnonempty :
          (readyCommitNodes G state.1 who).Nonempty :=
        ⟨action.node, hnodeMem⟩
      have hwhoActive : who ∈ activePlayers G state.1 := by
        unfold activePlayers
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ who, hnonempty⟩
      rw [hactive] at hwhoActive
      cases hwhoActive
  | internal event step =>
      exact ⟨event, ⟨step⟩⟩

end EventGraph

end Vegas
