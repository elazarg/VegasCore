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

/-- A node/value selected by one coordinate of a frontier packet. -/
private structure PacketChoice
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who))
    (node : Fin G.nodeCount) where
  owner : Player
  action : FrontierAction G owner
  value : L.Val (G.nodeRow node).ty
  action_eq : joint owner = some action
  value_eq : action.value? node = some value

/-- Execute one selected commit node. The availability check totalizes the
function outside the legal surface. On a legal frontier packet the first
selected node is available, and availability of every other selected node
persists while its peers are written. -/
private noncomputable def applyCommitNode
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who))
    (state : ReachableConfig G)
    (node : Fin G.nodeCount) : ReachableConfig G := by
  classical
  if henabled : ∃ choice : PacketChoice G joint node,
      CommitAvailable G state.1 choice.owner
        { node := node, value := G.nodeTypedValue node choice.value } then
    let choice := Classical.choose henabled
    let step := Classical.choice (Classical.choose_spec henabled)
    let event : AvailableEvent G state.1 :=
      .commit choice.owner
        { node := node, value := G.nodeTypedValue node choice.value }
        step
    let next := state.1.completeNode node
      { ty := step.guard.ty, value := step.value }
    exact
      ⟨next, Reachable.step state.2 event (by
        simp [event, next, stepAvailableEvent, stepCommit])⟩
  else
    exact state

/-- The nodes mentioned by a frontier packet, in canonical graph order. -/
private noncomputable def selectedNodes
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who)) :
    List (Fin G.nodeCount) := by
  classical
  exact G.nodeOrder.filter fun node =>
    decide (Nonempty (PacketChoice G joint node))

/-- Apply a simultaneous frontier packet in canonical graph-node order.
Independent ready commits commute, so the chosen serialization is operational
only; the protocol exposes the whole packet as one joint action. -/
noncomputable def applyFrontier
    (G : Graph Player L)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who)) : ReachableConfig G :=
  (selectedNodes G joint).foldl (applyCommitNode G joint) state

omit [Fintype Player] in
private theorem applyCommitNode_done_subset
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who))
    (state : ReachableConfig G)
    (node : Fin G.nodeCount) :
    state.1.done ⊆ (applyCommitNode G joint state node).1.done := by
  classical
  unfold applyCommitNode
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl

omit [Fintype Player] in
private theorem fold_applyCommitNode_done_subset
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who))
    (nodes : List (Fin G.nodeCount))
    (state : ReachableConfig G) :
    state.1.done ⊆
      (nodes.foldl (applyCommitNode G joint) state).1.done := by
  induction nodes generalizing state with
  | nil => exact Finset.Subset.rfl
  | cons node rest ih =>
      exact Finset.Subset.trans
        (applyCommitNode_done_subset G joint state node)
        (ih (applyCommitNode G joint state node))

omit [Fintype Player] in
private theorem applyCommitNode_done_ssubset
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who))
    (state : ReachableConfig G)
    (node : Fin G.nodeCount)
    (henabled : ∃ choice : PacketChoice G joint node,
      CommitAvailable G state.1 choice.owner
        { node := node, value := G.nodeTypedValue node choice.value }) :
    state.1.done ⊂ (applyCommitNode G joint state node).1.done := by
  classical
  unfold applyCommitNode
  rw [dif_pos henabled]
  exact Config.done_ssubset_completeNode
    (Classical.choice (Classical.choose_spec henabled)).ready.1 _

omit [Fintype Player] in
private theorem mem_selectedNodes_iff
    (G : Graph Player L)
    (joint : ∀ who, Option (FrontierAction G who))
    (node : Fin G.nodeCount) :
    node ∈ selectedNodes G joint ↔ Nonempty (PacketChoice G joint node) := by
  classical
  simp [selectedNodes]

private theorem selectedNodes_nonempty_of_legal
    (G : Graph Player L)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hactive : (activePlayers G state.1).Nonempty)
    (hlegal : GameTheory.Protocol.IsLegalJoint
      (fun who => who ∈ activePlayers G state.1)
      (fun who => { action | FrontierAction.Available G state.1 who action })
      joint) :
    ∃ node, node ∈ selectedNodes G joint := by
  classical
  rcases hactive with ⟨who, hwho⟩
  cases haction : joint who with
  | none =>
      have hlocal := hlegal who
      rw [haction] at hlocal
      exact False.elim (hlocal hwho)
  | some action =>
      have hlocal := hlegal who
      rw [haction] at hlocal
      have hreadySet : (readyCommitNodes G state.1 who).Nonempty :=
        (Finset.mem_filter.mp hwho).2
      rcases hreadySet with ⟨node, hnode⟩
      have hready : ReadyCommitNode G state.1 who node :=
        (Finset.mem_filter.mp hnode).2
      rcases
          (hlocal.2.value?_isSome_iff_readyCommitNode.mpr hready) with
        ⟨value, hvalue⟩
      exact
        ⟨node, (mem_selectedNodes_iff G joint node).2
          ⟨{ owner := who
             action := action
             value := value
             action_eq := haction
             value_eq := hvalue }⟩⟩

private theorem applyFrontier_done_ssubset_of_legal
    (G : Graph Player L)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hactive : (activePlayers G state.1).Nonempty)
    (hlegal : GameTheory.Protocol.IsLegalJoint
      (fun who => who ∈ activePlayers G state.1)
      (fun who => { action | FrontierAction.Available G state.1 who action })
      joint) :
    state.1.done ⊂ (applyFrontier G state joint).1.done := by
  classical
  have hselected := selectedNodes_nonempty_of_legal G state joint hactive hlegal
  cases hnodes : selectedNodes G joint with
  | nil =>
      rcases hselected with ⟨node, hmem⟩
      rw [hnodes] at hmem
      cases hmem
  | cons node rest =>
      have hchoice : Nonempty (PacketChoice G joint node) :=
        (mem_selectedNodes_iff G joint node).1 (by simp [hnodes])
      let choice := Classical.choice hchoice
      have hlocal := hlegal choice.owner
      rw [choice.action_eq] at hlocal
      have henabled : ∃ selected : PacketChoice G joint node,
          CommitAvailable G state.1 selected.owner
            { node := node,
              value := G.nodeTypedValue node selected.value } :=
        ⟨choice,
          hlocal.2.commitAvailable_of_value choice.value_eq⟩
      have hfirst :=
        applyCommitNode_done_ssubset G joint state node henabled
      have hrest :=
        fold_applyCommitNode_done_subset G joint rest
          (applyCommitNode G joint state node)
      unfold applyFrontier
      rw [hnodes]
      exact Finset.ssubset_of_ssubset_of_subset hfirst hrest

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
      exact FinDist.pure (applyFrontier G state legal.1)
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
      FinDist.pure (applyFrontier G state legal.1)).support at htarget
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
      G state legal.1 hactive hfrontier

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
retained. -/
structure PlayerInformation (G : Graph Player L) (who : Player) where
  current : LocalSnapshot G who
  own : List (LocalSnapshot G who × FrontierAction G who)

namespace PlayerInformation

variable {G : Graph Player L} {who : Player}

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

private noncomputable def localMenu
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
