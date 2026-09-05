/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Information
import Vegas.EventGraph.Frontier

/-!
# Event graphs as informed execution protocols

An event graph executes in two kinds of atomic protocol rounds:

* one ready internal sample or reveal step, with no active player;
* one strategic frontier step, in which every active player submits a packet
  assigning all of its currently ready commit nodes.

The strategic packet is essential: serializing hidden commitments as separate
player observations would introduce decision sites that are absent from the
source game. Internal work remains explicit because samples and reveals emit
information and may change the next legal menu.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability
open GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-! ## Explicit frontier writes -/

/-- The writes selected by one player's frontier, in canonical graph-node
order. This is shared by the atomic game semantics and serialized runtimes. -/
def actionWrites {G : Graph Player L} {who : Player}
    (action : FrontierAction G who) :
    List (Fin G.nodeCount × TypedValue L) :=
  G.nodeOrder.filterMap fun node =>
    (action.value? node).map fun value =>
      (node, G.nodeTypedValue node value)

omit [Fintype Player] in
@[simp] theorem mem_actionWrites_iff {G : Graph Player L} {who : Player}
    (action : FrontierAction G who)
    (step : Fin G.nodeCount × TypedValue L) :
    step ∈ actionWrites action ↔
      ∃ value, action.value? step.1 = some value ∧
        step.2 = G.nodeTypedValue step.1 value := by
  rcases step with ⟨node, written⟩
  rw [actionWrites, List.mem_filterMap]
  constructor
  · rintro ⟨selected, _hselected, hmap⟩
    cases hvalue : action.value? selected with
    | none => simp [hvalue] at hmap
    | some value =>
        simp only [hvalue, Option.map_some, Option.some.injEq] at hmap
        have hnode : selected = node := congrArg Prod.fst hmap
        subst node
        exact ⟨value, hvalue, (congrArg Prod.snd hmap).symm⟩
  · rintro ⟨value, hvalue, hwritten⟩
    refine ⟨node, G.mem_nodeOrder node, ?_⟩
    simpa [hvalue] using
      congrArg (fun value => some (node, value)) hwritten.symm

omit [Fintype Player] in
theorem actionWrites_nodes_nodup {G : Graph Player L} {who : Player}
    (action : FrontierAction G who) :
    ((actionWrites action).map Prod.fst).Nodup := by
  have helper : ∀ nodes : List (Fin G.nodeCount), nodes.Nodup →
      ((nodes.filterMap fun node =>
        (action.value? node).map fun value =>
          (node, G.nodeTypedValue node value)).map Prod.fst).Nodup := by
    intro nodes hnodes
    induction nodes with
    | nil => simp
    | cons node rest ih =>
        rw [List.nodup_cons] at hnodes
        cases hvalue : action.value? node with
        | none => simpa [hvalue] using ih hnodes.2
        | some value =>
            simp only [List.filterMap_cons, hvalue, Option.map_some,
              List.map_cons, List.nodup_cons]
            constructor
            · intro hmem
              have hmem' : node ∈ rest ∧
                  ∃ value, action.value? node = some value := by
                simpa [List.mem_map] using hmem
              exact hnodes.1 hmem'.1
            · exact ih hnodes.2
  exact helper G.nodeOrder G.nodeOrder_nodup

omit [Fintype Player] in
theorem commitAvailable_of_mem_actionWrites
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : FrontierAction.Available G cfg who action)
    {step : Fin G.nodeCount × TypedValue L}
    (hstep : step ∈ actionWrites action) :
    CommitAvailable G cfg who { node := step.1, value := step.2 } := by
  obtain ⟨value, hvalue, hwritten⟩ :=
    (mem_actionWrites_iff action step).mp hstep
  rw [hwritten]
  exact havailable.commitAvailable_of_value hvalue

omit [Fintype Player] in
theorem readyCommitNode_of_mem_actionWrites
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : FrontierAction.Available G cfg who action)
    {step : Fin G.nodeCount × TypedValue L}
    (hstep : step ∈ actionWrites action) :
    ReadyCommitNode G cfg who step.1 := by
  obtain ⟨value, hvalue, _hwritten⟩ :=
    (mem_actionWrites_iff action step).mp hstep
  exact havailable.readyCommitNode_of_value hvalue

/-- The writes contributed by one player coordinate. -/
def playerWrites {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who)) (who : Player) :
    List (Fin G.nodeCount × TypedValue L) :=
  match joint who with
  | none => []
  | some action => actionWrites action

omit [Fintype Player] in
@[simp] theorem mem_playerWrites_iff {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who)) (who : Player)
    (step : Fin G.nodeCount × TypedValue L) :
    step ∈ playerWrites joint who ↔
      ∃ action, joint who = some action ∧ step ∈ actionWrites action := by
  cases haction : joint who with
  | none => simp [playerWrites, haction]
  | some action => simp [playerWrites, haction]

/-- All frontier writes in a proposed player order. -/
def roundWrites {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who))
    (order : List Player) : List (Fin G.nodeCount × TypedValue L) :=
  order.flatMap (playerWrites joint)

omit [Fintype Player] in
@[simp] theorem roundWrites_append {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who))
    (left right : List Player) :
    roundWrites joint (left ++ right) =
      roundWrites joint left ++ roundWrites joint right := by
  simp [roundWrites]

omit [Fintype Player] in
@[simp] theorem mem_roundWrites_iff {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who))
    (order : List Player) (step : Fin G.nodeCount × TypedValue L) :
    step ∈ roundWrites joint order ↔
      ∃ who ∈ order, step ∈ playerWrites joint who := by
  simp [roundWrites]

omit [Fintype Player] in
/-- Locally legal player submissions contribute pairwise distinct graph nodes,
including across player coordinates. -/
theorem roundWrites_nodes_nodup {G : Graph Player L} {cfg : Config G}
    {joint : ∀ who, Option (FrontierAction G who)}
    (hlegal : ∀ who action, joint who = some action →
      FrontierAction.Available G cfg who action)
    {order : List Player} (horder : order.Nodup) :
    ((roundWrites joint order).map Prod.fst).Nodup := by
  induction order with
  | nil => simp [roundWrites]
  | cons who rest ih =>
      rw [List.nodup_cons] at horder
      cases haction : joint who with
      | none =>
          simpa [roundWrites, playerWrites, haction] using ih horder.2
      | some action =>
          rw [roundWrites, List.flatMap_cons, playerWrites, haction,
            List.map_append, List.nodup_append]
          refine ⟨actionWrites_nodes_nodup action, ih horder.2, ?_⟩
          intro first hfirst second hsecond heq
          obtain ⟨firstWrite, hfirstWrite, hfirstEq⟩ :=
            List.mem_map.mp hfirst
          obtain ⟨secondWrite, hsecondWrite, hsecondEq⟩ :=
            List.mem_map.mp hsecond
          obtain ⟨other, hother, hsecondPlayer⟩ :=
            (mem_roundWrites_iff joint rest secondWrite).mp hsecondWrite
          obtain ⟨otherAction, hotherAction, hsecondAction⟩ :=
            (mem_playerWrites_iff joint other secondWrite).mp hsecondPlayer
          have hfirstReady : ReadyCommitNode G cfg who firstWrite.1 :=
            readyCommitNode_of_mem_actionWrites
              (hlegal who action haction) hfirstWrite
          have hsecondReady : ReadyCommitNode G cfg other secondWrite.1 :=
            readyCommitNode_of_mem_actionWrites
              (hlegal other otherAction hotherAction) hsecondAction
          have hnodes : firstWrite.1 = secondWrite.1 :=
            hfirstEq.trans (heq.trans hsecondEq.symm)
          rw [← hnodes] at hsecondReady
          have howners : who = other :=
            hfirstReady.owner_unique hsecondReady
          exact horder.1 (howners.symm ▸ hother)

omit [Fintype Player] in
theorem commitAvailable_of_mem_roundWrites
    {G : Graph Player L} {cfg : Config G}
    {joint : ∀ who, Option (FrontierAction G who)}
    (hlegal : ∀ who action, joint who = some action →
      FrontierAction.Available G cfg who action)
    {order : List Player} {step : Fin G.nodeCount × TypedValue L}
    (hstep : step ∈ roundWrites joint order) :
    ∃ who, CommitAvailable G cfg who
      { node := step.1, value := step.2 } := by
  obtain ⟨who, _hwho, hplayer⟩ :=
    (mem_roundWrites_iff joint order step).mp hstep
  obtain ⟨action, haction, hactionWrite⟩ :=
    (mem_playerWrites_iff joint who step).mp hplayer
  exact ⟨who, commitAvailable_of_mem_actionWrites
    (hlegal who action haction) hactionWrite⟩

omit [Fintype Player] in
theorem roundWrites_perm {G : Graph Player L}
    (joint : ∀ who, Option (FrontierAction G who))
    {left right : List Player} (hperm : left.Perm right) :
    (roundWrites joint left).Perm (roundWrites joint right) := by
  exact hperm.flatMap fun _ _ => List.Perm.refl _

omit [Fintype Player] in
/-- A duplicate-free list of commits available at one checkpoint can be
executed in the listed order. Availability persists because distinct ready
nodes cannot read one another's output fields. -/
theorem reachable_completeNodes_of_commitAvailable
    {G : Graph Player L} (hwf : G.WF) {cfg : Config G}
    (hreachable : Reachable G cfg)
    {steps : List (Fin G.nodeCount × TypedValue L)}
    (hnodup : (steps.map Prod.fst).Nodup)
    (havailable : ∀ step ∈ steps,
      ∃ who, CommitAvailable G cfg who
        { node := step.1, value := step.2 }) :
    Reachable G (cfg.completeNodes steps) := by
  induction steps generalizing cfg with
  | nil => simpa using hreachable
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨headWho, headAvailable⟩ :=
        havailable head (by simp)
      let headStep := Classical.choice headAvailable
      let event : AvailableEvent G cfg :=
        .commit headWho { node := head.1, value := head.2 } headStep
      have hnext : cfg.completeNode head.1 head.2 ∈
          (stepAvailableEvent G cfg event).support := by
        change cfg.completeNode head.1 head.2 ∈
          (FinDist.pure
            (cfg.completeNode head.1
              { ty := headStep.guard.ty, value := headStep.value })).support
        rw [headStep.written_eq_action]
        exact FinDist.mem_support_pure.mpr rfl
      have hreachableHead : Reachable G (cfg.completeNode head.1 head.2) :=
        Reachable.step hreachable event hnext
      rw [Config.completeNodes_cons]
      apply ih hreachableHead hnodup.2
      intro tail htail
      obtain ⟨tailWho, tailAvailable⟩ :=
        havailable tail (by simp [htail])
      refine ⟨tailWho,
        tailAvailable.persist_after_other_commit_write
          hwf headAvailable head.2 ?_⟩
      intro heq
      change tail.1 = head.1 at heq
      apply hnodup.1
      have htailNode : tail.1 ∈ rest.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) htail
      exact heq ▸ htailNode

/-- Apply a simultaneous frontier packet using one shared explicit write list.

The canonical player order is operational only: the protocol exposes the whole
packet as one joint action, and distinct locally legal writes commute. The
fallback makes the function total on malformed direct calls; protocol steps
always establish `havailable`. -/
noncomputable def applyFrontier
    (G : Graph Player L) (hwf : G.WF)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who)) : ReachableConfig G := by
  classical
  if havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action then
    let steps := roundWrites joint (Finset.univ.toList : List Player)
    exact
      ⟨state.1.completeNodes steps,
        reachable_completeNodes_of_commitAvailable hwf state.2
          (roundWrites_nodes_nodup havailable Finset.univ.nodup_toList)
          (fun _step hstep =>
            commitAvailable_of_mem_roundWrites havailable hstep)⟩
  else
    exact state

/-- On its legal surface, the atomic frontier operation is exactly the shared
canonical list of submitted writes. -/
theorem applyFrontier_val_of_available
    (G : Graph Player L) (hwf : G.WF)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action) :
    (applyFrontier G hwf state joint).1 =
      state.1.completeNodes
        (roundWrites joint (Finset.univ.toList : List Player)) := by
  unfold applyFrontier
  rw [dif_pos havailable]

private theorem applyFrontier_done_ssubset_of_legal
    (G : Graph Player L) (hwf : G.WF)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hactive : (activePlayers G state.1).Nonempty)
    (hlegal : GameTheory.Protocol.IsLegalJoint
      (fun who => who ∈ activePlayers G state.1)
      (fun who => { action | FrontierAction.Available G state.1 who action })
      joint) :
    state.1.done ⊂ (applyFrontier G hwf state joint).1.done := by
  classical
  have havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action := by
    intro who action haction
    have hlocal := hlegal who
    rw [haction] at hlocal
    exact hlocal.2
  rw [applyFrontier_val_of_available G hwf state joint havailable,
    Config.completeNodes_done]
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_union_left, ?_⟩
  intro heq
  rcases hactive with ⟨who, hwho⟩
  cases haction : joint who with
  | none =>
      have hlocal := hlegal who
      rw [haction] at hlocal
      exact hlocal hwho
  | some action =>
      have hlocal := hlegal who
      rw [haction] at hlocal
      rcases (Finset.mem_filter.mp hwho).2 with ⟨node, hnodeMem⟩
      have hready : ReadyCommitNode G state.1 who node :=
        (Finset.mem_filter.mp hnodeMem).2
      rcases (hlocal.2.value?_isSome_iff_readyCommitNode.mpr hready) with
        ⟨value, hvalue⟩
      let written : Fin G.nodeCount × TypedValue L :=
        (node, G.nodeTypedValue node value)
      have hactionWrite : written ∈ actionWrites action :=
        (mem_actionWrites_iff action written).mpr ⟨value, hvalue, rfl⟩
      have hplayerWrite : written ∈ playerWrites joint who :=
        (mem_playerWrites_iff joint who written).mpr
          ⟨action, haction, hactionWrite⟩
      have hroundWrite : written ∈
          roundWrites joint (Finset.univ.toList : List Player) :=
        (mem_roundWrites_iff joint _ written).mpr
          ⟨who, by simp, hplayerWrite⟩
      have hnodeWritten : node ∈
          (roundWrites joint (Finset.univ.toList : List Player)).map Prod.fst :=
        List.mem_map.mpr ⟨written, hroundWrite, rfl⟩
      have hnodeUnion : node ∈ state.1.done ∪
          ((roundWrites joint
            (Finset.univ.toList : List Player)).map Prod.fst).toFinset := by
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hnodeWritten)
      have hnodeDone : node ∈ state.1.done := by
        rw [heq]
        exact hnodeUnion
      exact hready.ready.1 hnodeDone

private theorem activePlayers_nonempty_of_no_internal
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (hterminal : ¬ Terminal G state.1)
    (hinternal : readyInternalNodes G state.1 = ∅) :
    (activePlayers G state.1).Nonempty := by
  classical
  by_contra hactive
  have hempty : activePlayers G state.1 = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hactive
  rcases exists_internal_available_of_no_active
      hwf hguards hterminal hempty with ⟨event, havailable⟩
  have hready : ReadyInternalNode G state.1 event.node :=
    havailable.readyInternalNode
  have hmem : event.node ∈ readyInternalNodes G state.1 := by
    unfold readyInternalNodes
    simp [hready]
  rw [hinternal] at hmem
  simp at hmem

/-- The GameTheory execution protocol denoted by a well-formed live event
graph. State-dependent guards become native `available` menus rather than
total actions with an invalid-action convention. -/
noncomputable def toExecutionProtocol
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    ExecutionProtocol Player where
  State := ReachableConfig G
  Action := FrontierAction G
  init := ⟨Config.initial G, Reachable.initial⟩
  active := fun state who =>
    ¬ Terminal G state.1 ∧
      readyInternalNodes G state.1 = ∅ ∧
      who ∈ activePlayers G state.1
  available := fun state who =>
    { action | FrontierAction.Available G state.1 who action }
  terminal := fun state => Terminal G state.1
  step := fun state legal => by
    classical
    if hinternal : (readyInternalNodes G state.1).Nonempty then
      let node := Classical.choose hinternal
      have hready : ReadyInternalNode G state.1 node :=
        (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
      have havailable : InternalAvailable G state.1 { node := node } :=
        InternalAvailable.of_readyInternalNode hwf
          (reachable_storeCoherent hwf state.2) hready
      exact stepAvailable G state
        (.internal { node := node } (Classical.choice havailable))
    else
      exact FinDist.pure (applyFrontier G hwf state legal.1)
  progress := fun state hterminal => by
    classical
    by_cases hinternal : readyInternalNodes G state.1 = ∅
    · obtain ⟨joint, hjoint⟩ :=
        exists_legal_frontier_action_of_reachable
          hwf hguards (state := state)
      refine ⟨joint, ?_⟩
      intro who
      have hlocal := hjoint who
      cases hchoice : joint who with
      | none =>
          simp only [hchoice] at hlocal
          simp only
          intro hactive
          exact hlocal hactive.2.2
      | some action =>
          simp only [hchoice] at hlocal
          simp only
          exact ⟨⟨hterminal, hinternal, hlocal.1⟩, hlocal.2⟩
    · refine ⟨fun _ => none, ?_⟩
      intro who hactive
      exact hinternal hactive.2.1

/-- At a strategic checkpoint with no ready internal work, protocol execution
is exactly the deterministic canonical serialization of the simultaneous
frontier packet. -/
theorem toExecutionProtocol_step_eq_pure_applyFrontier
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (legal : { joint : ∀ who, Option (FrontierAction G who) //
      (toExecutionProtocol G hwf hguards).Legal state joint })
    (noInternal : readyInternalNodes G state.1 = ∅) :
    (toExecutionProtocol G hwf hguards).step state legal =
      GameTheory.Math.Probability.FinDist.pure
        (applyFrontier G hwf state legal.1) := by
  unfold toExecutionProtocol
  change
    (if _hinternal : (readyInternalNodes G state.1).Nonempty then _ else _) = _
  simp [noInternal]

/-- Every realized protocol round completes at least one graph node. This is
the progress measure that turns the finite graph into a certified finite game,
including strategic rounds that atomically apply an entire frontier packet. -/
theorem toExecutionProtocol_step_done_ssubset
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (legal : { joint : ∀ who, Option (FrontierAction G who) //
      (toExecutionProtocol G hwf hguards).Legal state joint })
    {target : ReachableConfig G}
    (htarget : target ∈
      ((toExecutionProtocol G hwf hguards).step state legal).support) :
    state.1.done ⊂ target.1.done := by
  classical
  change target ∈
    (if hinternal : (readyInternalNodes G state.1).Nonempty then
      let node := Classical.choose hinternal
      let hready : ReadyInternalNode G state.1 node :=
        (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
      let havailable : InternalAvailable G state.1 { node := node } :=
        InternalAvailable.of_readyInternalNode hwf
          (reachable_storeCoherent hwf state.2) hready
      stepAvailable G state
        (.internal { node := node } (Classical.choice havailable))
    else
      FinDist.pure (applyFrontier G hwf state legal.1)).support at htarget
  by_cases hinternal : (readyInternalNodes G state.1).Nonempty
  · rw [dif_pos hinternal] at htarget
    exact done_ssubset_of_stepAvailable_support G state _ htarget
  · rw [dif_neg hinternal, FinDist.mem_support_pure] at htarget
    subst target
    have hinternalEmpty : readyInternalNodes G state.1 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hinternal
    have hactive : (activePlayers G state.1).Nonempty :=
      activePlayers_nonempty_of_no_internal
        G hwf hguards state legal.2.1 hinternalEmpty
    have hfrontier : GameTheory.Protocol.IsLegalJoint
        (fun who => who ∈ activePlayers G state.1)
        (fun who =>
          { action | FrontierAction.Available G state.1 who action })
        legal.1 := by
      intro who
      have hcoord := legal.2.2 who
      cases hchoice : legal.1 who with
      | none =>
          rw [hchoice] at hcoord
          change ¬ who ∈ activePlayers G state.1
          intro hmem
          exact hcoord ⟨legal.2.1, hinternalEmpty, hmem⟩
      | some action =>
          rw [hchoice] at hcoord
          change who ∈ activePlayers G state.1 ∧
            FrontierAction.Available G state.1 who action
          exact ⟨hcoord.1.2.2, hcoord.2⟩
    exact applyFrontier_done_ssubset_of_legal
      G hwf state legal.1 hactive hfrontier

/-- A protocol trace cannot be longer than the number of graph nodes already
completed at its endpoint. -/
theorem toExecutionProtocol_trace_length_le_done_card
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    ∀ (state : (toExecutionProtocol G hwf hguards).State)
      (trace : (toExecutionProtocol G hwf hguards).Trace state),
      trace.length ≤ state.1.done.card := by
  intro state trace
  induction trace with
  | start =>
      rfl
  | @extend source target prior joint isLegal realized ih =>
      have hgrow := toExecutionProtocol_step_done_ssubset
        G hwf hguards source ⟨joint, isLegal⟩ realized
      have hcard := Finset.card_lt_card hgrow
      simp only [ExecutionProtocol.Trace.length]
      omega

/-- The number of graph nodes is a uniform horizon for every strategy and
every chance realization. -/
theorem toExecutionProtocol_boundedHorizon
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    (toExecutionProtocol G hwf hguards).BoundedHorizon G.nodeCount := by
  intro state trace hlength
  have hdoneCard : G.nodeCount ≤ state.1.done.card :=
    le_trans hlength
      (toExecutionProtocol_trace_length_le_done_card
        G hwf hguards state trace)
  change Terminal G state.1
  intro node
  by_contra hnotDone
  have hstrict : state.1.done ⊂ insert node state.1.done := by
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_insert node state.1.done, by
        intro heq
        exact hnotDone (by rw [heq]; exact Finset.mem_insert_self node _)⟩
  have hstrictUniv : state.1.done ⊂ (Finset.univ : Finset (Fin G.nodeCount)) :=
    Finset.ssubset_of_ssubset_of_subset hstrict (Finset.subset_univ _)
  have hcardLt := Finset.card_lt_card hstrictUniv
  simp only [Finset.card_univ, Fintype.card_fin] at hcardLt
  omega

/-! ## Information -/

/-- The complete information-local snapshot at a graph checkpoint. Public and
private components remain factored so common knowledge is not duplicated in
the private signal alphabet. -/
abbrev LocalSnapshot (G : Graph Player L) (who : Player) :=
  PublicObservation G × Observation G who

/-- A player's information consists of the current graph-local snapshot and
exactly its own earlier decision record. Unrelated transition ordering is not
retained. Graph storage is immutable and completion is monotone, so the current
snapshot retains all game data disclosed by inactive transitions. -/
structure PlayerInformation (G : Graph Player L) (who : Player) where
  current : LocalSnapshot G who
  own : List (LocalSnapshot G who × FrontierAction G who)

namespace PlayerInformation

variable {G : Graph Player L} {who : Player}

omit [Fintype Player] in
@[ext] theorem ext {left right : PlayerInformation G who}
    (hcurrent : left.current = right.current) (hown : left.own = right.own) :
    left = right := by
  cases left
  cases right
  cases hcurrent
  cases hown
  rfl

/-- Extend local information after one transition. Only the player's own
action is remembered; inactive transitions merely replace the current
snapshot. -/
def push (prior : PlayerInformation G who)
    (choice : Option (FrontierAction G who))
    (current : LocalSnapshot G who) : PlayerInformation G who where
  current := current
  own := match choice with
    | none => prior.own
    | some action => (prior.current, action) :: prior.own

/-- Reconstruct GameTheory's `ownPlay` representation from the compact local
decision record. -/
def recalledOwnPlayFrom :
    List (LocalSnapshot G who × FrontierAction G who) →
      List (PlayerInformation G who × FrontierAction G who)
  | [] => []
  | (snapshot, action) :: prior =>
      ({ current := snapshot, own := prior }, action) ::
        recalledOwnPlayFrom prior

def recalledOwnPlay (info : PlayerInformation G who) :
    List (PlayerInformation G who × FrontierAction G who) :=
  recalledOwnPlayFrom info.own

omit [Fintype Player] in
@[simp] theorem recalledOwnPlay_push_none
    (prior : PlayerInformation G who) (current : LocalSnapshot G who) :
    recalledOwnPlay (prior.push none current) = recalledOwnPlay prior :=
  rfl

omit [Fintype Player] in
@[simp] theorem recalledOwnPlay_push_some
    (prior : PlayerInformation G who) (action : FrontierAction G who)
    (current : LocalSnapshot G who) :
    recalledOwnPlay (prior.push (some action) current) =
      (prior, action) :: recalledOwnPlay prior := by
  cases prior
  rfl

end PlayerInformation

/-- Event-graph observations as GameTheory protocol signals. The information
state retains the latest snapshot and the player's own earlier decisions. -/
noncomputable def toInfoSignals
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    InfoSignals (toExecutionProtocol G hwf hguards) where
  PublicSignal := PublicObservation G
  PrivateSignal := Observation G
  initialPublic := publicObserve G (Config.initial G)
  initialPrivate := fun who => observe G (Config.initial G) who
  publicSignal := fun event => publicObserve G event.target.1
  privateSignal := fun who event => observe G event.target.1 who
  InfoState := PlayerInformation G
  initInfo := fun _ privateView publicView =>
    { current := (publicView, privateView), own := [] }
  pushInfo := fun _ prior choice privateView publicView =>
    prior.push choice (publicView, privateView)

/-- The current component of accumulated information is the graph snapshot at
the trace endpoint. -/
theorem infoOf_toInfoSignals_current
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state) :
    ((toInfoSignals G hwf hguards).infoOf who trace).current =
      (publicObserve G state.1, observe G state.1 who) := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih => rfl

/-- The compact decision record agrees exactly with GameTheory's canonical
record of the player's information states and actions. -/
theorem ownPlay_toInfoSignals_eq_recalled
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state) :
    (toInfoSignals G hwf hguards).ownPlay who trace =
      PlayerInformation.recalledOwnPlay
        ((toInfoSignals G hwf hguards).infoOf who trace) := by
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
      rw [InfoSignals.ownPlay_extend, InfoSignals.infoOf_extend]
      cases hchoice : joint who with
      | none =>
          rw [ih]
          exact
            (PlayerInformation.recalledOwnPlay_push_none
              ((toInfoSignals G hwf hguards).infoOf who prior)
              (publicObserve G target.1, observe G target.1 who)).symm
      | some action =>
          rw [ih]
          exact
            (PlayerInformation.recalledOwnPlay_push_some
              ((toInfoSignals G hwf hguards).infoOf who prior) action
              (publicObserve G target.1, observe G target.1 who)).symm

/-- The event-graph information model has perfect recall: equality of current
information includes equality of the player's complete own-decision record. -/
theorem toInfoSignals_perfectRecall
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    (toInfoSignals G hwf hguards).PerfectRecall := by
  intro who first second traceFirst traceSecond hinfo
  rw [ownPlay_toInfoSignals_eq_recalled G hwf hguards who traceFirst,
    ownPlay_toInfoSignals_eq_recalled G hwf hguards who traceSecond,
    hinfo]

private theorem active_iff_of_observations
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    {left right : ReachableConfig G} {who : Player}
    (hpublic : publicObserve G left.1 = publicObserve G right.1)
    (hprivate : observe G left.1 who = observe G right.1 who) :
    (toExecutionProtocol G hwf hguards).active left who ↔
      (toExecutionProtocol G hwf hguards).active right who := by
  have hdone : left.1.done = right.1.done :=
    congrArg PublicObservation.done hpublic
  have hterminal : Terminal G left.1 ↔ Terminal G right.1 := by
    unfold Terminal
    rw [hdone]
  have hinternal :
      readyInternalNodes G left.1 = ∅ ↔
        readyInternalNodes G right.1 = ∅ := by
    rw [readyInternalNodes_eq_of_publicObserve_eq hpublic]
  have hactive :
      who ∈ activePlayers G left.1 ↔ who ∈ activePlayers G right.1 := by
    unfold activePlayers
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [readyCommitNodes_eq_of_observe_eq hprivate]
  change
    (¬ Terminal G left.1 ∧ readyInternalNodes G left.1 = ∅ ∧
        who ∈ activePlayers G left.1) ↔
      (¬ Terminal G right.1 ∧ readyInternalNodes G right.1 = ∅ ∧
        who ∈ activePlayers G right.1)
  exact and_congr (not_congr hterminal) (and_congr hinternal hactive)

private theorem legalOption_iff_of_observations
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    {left right : ReachableConfig G} {who : Player}
    (hpublic : publicObserve G left.1 = publicObserve G right.1)
    (hprivate : observe G left.1 who = observe G right.1 who)
    (choice : Option (FrontierAction G who)) :
    LegalOption (toExecutionProtocol G hwf hguards) left who choice ↔
      LegalOption (toExecutionProtocol G hwf hguards) right who choice := by
  cases choice with
  | none =>
      exact not_congr (active_iff_of_observations G hwf hguards hpublic hprivate)
  | some action =>
      exact and_congr
        (active_iff_of_observations G hwf hguards hpublic hprivate)
        (FrontierAction.available_iff_of_observe_eq hwf hprivate)

noncomputable def localMenu
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) (info : PlayerInformation G who) :
    Set (Option (FrontierAction G who)) := by
  classical
  if _hrealizable : ∃ state : ReachableConfig G,
      publicObserve G state.1 = info.current.1 ∧
      observe G state.1 who = info.current.2 then
    exact
      { choice | ∃ state : ReachableConfig G,
          publicObserve G state.1 = info.current.1 ∧
          observe G state.1 who = info.current.2 ∧
          LegalOption (toExecutionProtocol G hwf hguards) state who choice }
  else
    exact {none}

/-- Every information-local menu is inhabited. Unrealizable information states
receive the unique idle option; realizable states inherit a legal coordinate
from protocol progress (or idle at termination). -/
theorem localMenu_nonempty
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) (info : PlayerInformation G who) :
    (localMenu G hwf hguards who info).Nonempty := by
  classical
  unfold localMenu
  split
  next hrealizable =>
    rcases hrealizable with ⟨state, hpublic, hprivate⟩
    by_cases hterminal : Terminal G state.1
    · refine ⟨none, ⟨state, hpublic, hprivate, ?_⟩⟩
      change ¬ (toExecutionProtocol G hwf hguards).active state who
      intro hactive
      exact hactive.1 hterminal
    · rcases
        (toExecutionProtocol G hwf hguards).progress state hterminal with
        ⟨joint, hjoint⟩
      let hlegal : (toExecutionProtocol G hwf hguards).Legal state joint :=
        ⟨hterminal, hjoint⟩
      refine ⟨joint who, ⟨state, hpublic, hprivate, ?_⟩⟩
      exact
        (toExecutionProtocol G hwf hguards).legalOption_of_legal hlegal who
  next _ =>
    exact ⟨none, by simp⟩

/-- The canonical information model of a live event graph. Policies receive
only factored graph observations. Menu adequacy follows from the compiler's
visibility theorem: equal observations have equal active status and exactly
the same guarded frontier actions. -/
noncomputable def toInformationModel
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) :
    InformationModel (toExecutionProtocol G hwf hguards) where
  toInfoSignals := toInfoSignals G hwf hguards
  menu := localMenu G hwf hguards
  menu_adequate := by
    intro who state trace choice
    have hcurrent :=
      infoOf_toInfoSignals_current G hwf hguards who trace
    have hrealizable : ∃ witness : ReachableConfig G,
        publicObserve G witness.1 =
            ((toInfoSignals G hwf hguards).infoOf who trace).current.1 ∧
          observe G witness.1 who =
            ((toInfoSignals G hwf hguards).infoOf who trace).current.2 := by
      exact ⟨state, by rw [hcurrent], by rw [hcurrent]⟩
    unfold localMenu
    rw [dif_pos hrealizable]
    constructor
    · rintro ⟨witness, hpublic, hprivate, hlegal⟩
      rw [hcurrent] at hpublic hprivate
      exact
        (legalOption_iff_of_observations G hwf hguards
          hpublic hprivate choice).mp hlegal
    · intro hlegal
      refine ⟨state, ?_, ?_, hlegal⟩
      · rw [hcurrent]
      · rw [hcurrent]

/-- Every GameTheory choice carrier of the compiled information model is
inhabited, including at unreachable information values. -/
theorem choice_nonempty
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) (info : PlayerInformation G who) :
    Nonempty ((toInformationModel G hwf hguards).Choice who info) := by
  let choice := Classical.choose (localMenu_nonempty G hwf hguards who info)
  exact ⟨⟨choice,
    Classical.choose_spec (localMenu_nonempty G hwf hguards who info)⟩⟩

end Vegas.EventGraph
