/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Frontier
import Vegas.EventGraph.ToMachine
import Vegas.Machine.RoundView

/-!
# Event-graph frontier round views

This module contains the graph-level strategic round vocabulary.  It is
runtime-general and source-compiler independent: a round view is parameterized
by an `EventGraph.ToMachine.GraphMachineSpec`, not by a compiled Vegas source
program.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- The primitive machine associated with an event-graph machine spec. -/
noncomputable abbrev PrimitiveMachineOf
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G) :
    Machine Player :=
  ToMachine.primitiveMachine spec

/-- Canonical player action alphabet for graph-frontier rounds. -/
abbrev FrontierAct (G : Graph Player L) (who : Player) : Type :=
  FrontierAction G who

/-- Active players at a checkpoint.

Strategic commit choices are offered only after currently-ready internal graph
work has closed.  If an internal node is ready, the checkpoint should advance
operational/chance work rather than expose a strategic frontier. -/
noncomputable def frontierActive (G : Graph Player L) :
    ReachableConfig G → Finset Player :=
  fun state =>
    if (readyInternalNodes G state.1).Nonempty then
      ∅
    else
      activePlayers G state.1

/-- Locally available frontier actions for one player. -/
noncomputable def frontierAvailableActions
    (G : Graph Player L) :
    ReachableConfig G → (who : Player) → Set (FrontierAct G who) :=
  fun state who =>
    { action | FrontierAction.Available G state.1 who action }

omit [Fintype Player] in
/-- The local frontier action menu is determined by the player's graph
observation. -/
theorem frontierAvailableActions_iff_of_observe_eq
    {G : Graph Player L}
    {left right : ReachableConfig G} {who : Player}
    (hwf : G.WF)
    (hobs : observe G left.1 who = observe G right.1 who)
    {action : FrontierAct G who} :
    action ∈ frontierAvailableActions G left who ↔
      action ∈ frontierAvailableActions G right who := by
  exact FrontierAction.available_iff_of_observe_eq hwf hobs

omit [Fintype Player] in
/-- Equal player observations give exactly the same local frontier action
menu. -/
theorem frontierAvailableActions_eq_of_observe_eq
    {G : Graph Player L}
    {left right : ReachableConfig G} {who : Player}
    (hwf : G.WF)
    (hobs : observe G left.1 who = observe G right.1 who) :
    frontierAvailableActions G left who =
      frontierAvailableActions G right who := by
  ext action
  exact frontierAvailableActions_iff_of_observe_eq hwf hobs

/-- A player's activity in the frontier round is determined by the public
observation and that player's graph observation. -/
theorem mem_frontierActive_iff_of_observe_eq
    {G : Graph Player L}
    {left right : ReachableConfig G} {who : Player}
    (hpublic :
      publicObserve G left.1 = publicObserve G right.1)
    (hprivate :
      observe G left.1 who = observe G right.1 who) :
    who ∈ frontierActive G left ↔
      who ∈ frontierActive G right := by
  classical
  have hinternal :
      readyInternalNodes G left.1 =
        readyInternalNodes G right.1 :=
    readyInternalNodes_eq_of_publicObserve_eq hpublic
  have hcommits :
      readyCommitNodes G left.1 who =
        readyCommitNodes G right.1 who :=
    readyCommitNodes_eq_of_observe_eq hprivate
  unfold frontierActive
  rw [hinternal]
  by_cases hready :
      (readyInternalNodes G right.1).Nonempty
  · simp [hready]
  · unfold activePlayers
    simp [hready, hcommits]

theorem frontierCommitAvailable_of_legal_value
    (G : Graph Player L)
    {state : ReachableConfig G}
    {joint : JointAction (FrontierAct G)}
    (hlegal :
      JointActionLegal (FrontierAct G)
        (frontierActive G)
        (fun state : ReachableConfig G => Terminal G state.1)
        (frontierAvailableActions G) state joint)
    {who : Player} {frontierAction : FrontierAct G who}
    {node : Fin G.nodeCount} {value : L.Val (G.nodeRow node).ty}
    (haction : joint who = some frontierAction)
    (hvalue : frontierAction.value? node = some value) :
    CommitAvailable G state.1 who
      { node := node, value := G.nodeTypedValue node value } := by
  have hlocal := hlegal.2 who
  rw [haction] at hlocal
  exact
    FrontierAction.Available.commitAvailable_of_value
      hlocal.2 hvalue

/-- A primitive machine event is compatible with a joint frontier action if
player events are exactly values selected by the corresponding player's
frontier action. Internal events are operational/chance work and are not
strategic choices. -/
def FrontierEventSelected
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (action : JointAction (FrontierAct G)) :
    (PrimitiveMachineOf spec).Event → Prop
  | .play who commit =>
      ∃ frontierAction,
        action who = some frontierAction ∧
          ∃ value,
            frontierAction.value? commit.node = some value ∧
              commit.value = G.nodeTypedValue commit.node value
  | .internal _ => True

/-- A primitive event batch realizes a joint frontier action when every
strategic primitive event in the batch is selected by the joint action, and
every selected commit value appears as a primitive play event. Availability and
ordering are certified separately. -/
def FrontierBatchRealizesAction
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (action : JointAction (FrontierAct G))
    (batch : List (PrimitiveMachineOf spec).Event) : Prop :=
  (∀ event, event ∈ batch → FrontierEventSelected spec action event) ∧
    ∀ who frontierAction node value,
      action who = some frontierAction →
        frontierAction.value? node = some value →
          Machine.Event.play (M := PrimitiveMachineOf spec) who
            ({ node := node, value := G.nodeTypedValue node value } :
              (PrimitiveMachineOf spec).Action who) ∈ batch

/-- Certificate attached to one supported frontier-round transition.

The strategic transition kernel is order-free; this certificate records one
primitive explanation for a positive-support destination and connects it to the
checkpoint presentation. -/
structure FrontierRoundStepCertificate
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (presentation : CheckpointPresentation G)
    {state : (PrimitiveMachineOf spec).State}
    (action :
      {a : JointAction (FrontierAct G) //
        JointActionLegal (FrontierAct G)
          (frontierActive G)
          (PrimitiveMachineOf spec).terminal
          (frontierAvailableActions G) state a})
    (dst : (PrimitiveMachineOf spec).State)
    (batch : List (PrimitiveMachineOf spec).Event) where
  realizesAction : FrontierBatchRealizesAction spec action.1 batch
  availableRun : (PrimitiveMachineOf spec).AvailableRunFrom state batch dst
  allowed : presentation.policy.allowed state dst

/-- Support-certified strategic semantics for one frontier round under a
checkpoint presentation.

The local action surface is canonical: players choose values for their ready
commit frontier. The transition kernel is intentionally order-free. Primitive
event batches appear only as certificates for supported transitions.

This structure certifies support, not probability mass: every positive-mass
checkpoint transition has a replayable primitive explanation, but the numeric
mass in `transition` is part of the abstract checkpoint semantics. Checked
programs use the canonical frontier semantics and separate trace/refinement
adequacy theorems when primitive event-batch probabilities matter. -/
structure FrontierRoundSemantics
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (presentation : CheckpointPresentation G) where
  guards : GuardLive G
  transition :
    (state : (PrimitiveMachineOf spec).State) →
      {a : JointAction (FrontierAct G) //
        JointActionLegal (FrontierAct G)
          (frontierActive G)
          (PrimitiveMachineOf spec).terminal
          (frontierAvailableActions G) state a} →
      PMF (PrimitiveMachineOf spec).State
  eventBatch :
    (state : (PrimitiveMachineOf spec).State) →
      {a : JointAction (FrontierAct G) //
        JointActionLegal (FrontierAct G)
          (frontierActive G)
          (PrimitiveMachineOf spec).terminal
          (frontierAvailableActions G) state a} →
      (dst : (PrimitiveMachineOf spec).State) →
        List (PrimitiveMachineOf spec).Event
  certifies :
    ∀ {state}
      (action :
        {a : JointAction (FrontierAct G) //
          JointActionLegal (FrontierAct G)
            (frontierActive G)
            (PrimitiveMachineOf spec).terminal
            (frontierAvailableActions G) state a})
      {dst},
        transition state action dst ≠ 0 →
          FrontierRoundStepCertificate spec presentation
            action dst (eventBatch state action dst)

omit [Fintype Player] in
/-- Primitive commit events selected by a joint frontier action, enumerated
over graph nodes. This is the canonical strategic prefix shape: each graph
node is visited at most once, so selected commit serialization follows graph
identity rather than player-order bookkeeping. -/
def selectedCommitEventsFromNodes
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (nodes : List (Fin G.nodeCount))
    (action : JointAction (FrontierAct G)) :
    List (PrimitiveMachineOf spec).Event :=
  nodes.filterMap fun node : Fin G.nodeCount =>
    match (G.nodeRow node).sem with
    | .commit who _guard =>
        match action who with
        | none => none
        | some frontierAction =>
            (frontierAction.value? node).map fun value =>
              Machine.Event.play (M := PrimitiveMachineOf spec) who
                ({ node := node, value := G.nodeTypedValue node value } :
                  (PrimitiveMachineOf spec).Action who)
    | _ => none

omit [Fintype Player] in
/-- A selected strategic commit event at one graph node. -/
def SelectedCommitAtNode
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (action : JointAction (FrontierAct G))
    (node : Fin G.nodeCount)
    (event : (PrimitiveMachineOf spec).Event) : Prop :=
  ∃ who guard frontierAction value,
    (G.nodeRow node).sem = NodeSem.commit who guard ∧
    action who = some frontierAction ∧
    frontierAction.value? node = some value ∧
    event =
      Machine.Event.play (M := PrimitiveMachineOf spec) who
        ({ node := node, value := G.nodeTypedValue node value } :
          (PrimitiveMachineOf spec).Action who)

omit [Fintype Player] in
theorem mem_selectedCommitEventsFromNodes_iff
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (nodes : List (Fin G.nodeCount))
    (action : JointAction (FrontierAct G))
    {event : (PrimitiveMachineOf spec).Event} :
    event ∈ selectedCommitEventsFromNodes spec nodes action ↔
      ∃ node, node ∈ nodes ∧
        SelectedCommitAtNode spec action node event := by
  classical
  constructor
  · intro hmem
    unfold selectedCommitEventsFromNodes at hmem
    rw [List.mem_filterMap] at hmem
    rcases hmem with ⟨node, hnodeMem, hselected⟩
    cases hnode : (G.nodeRow node).sem with
    | sample dist =>
        simp [hnode] at hselected
    | reveal source =>
        simp [hnode] at hselected
    | commit who guard =>
        cases haction : action who with
        | none =>
            simp [hnode, haction] at hselected
        | some frontierAction =>
            cases hvalue : frontierAction.value? node with
            | none =>
                have hnone :
                    (none : Option (PrimitiveMachineOf spec).Event) =
                      some event := by
                  simpa only [hnode, haction, hvalue, Option.map_none]
                    using hselected
                cases hnone
            | some value =>
                have hsome :
                    some
                      (Machine.Event.play (M := PrimitiveMachineOf spec)
                        who
                        ({ node := node, value := G.nodeTypedValue node value } :
                          (PrimitiveMachineOf spec).Action who)) =
                        some event := by
                  simpa only [hnode, haction, hvalue, Option.map_some]
                    using hselected
                refine
                  ⟨node, hnodeMem, who, guard, frontierAction, value,
                    hnode, haction, hvalue, ?_⟩
                exact (Option.some.inj hsome).symm
  · intro h
    rcases h with
      ⟨node, hnodeMem, who, guard, frontierAction, value,
        hnode, haction, hvalue, hevent⟩
    unfold selectedCommitEventsFromNodes
    rw [List.mem_filterMap]
    refine ⟨node, hnodeMem, ?_⟩
    simp [hnode, haction, hvalue, hevent]

theorem selectedCommitAtNode_available_of_legal
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    {state : (PrimitiveMachineOf spec).State}
    {action : JointAction (FrontierAct G)}
    (hlegal :
      JointActionLegal (FrontierAct G)
        (frontierActive G)
        (PrimitiveMachineOf spec).terminal
        (frontierAvailableActions G) state action)
    {node : Fin G.nodeCount}
    {event : (PrimitiveMachineOf spec).Event}
    (hselected : SelectedCommitAtNode spec action node event) :
    (PrimitiveMachineOf spec).EventAvailable state event := by
  rcases hselected with
    ⟨who, _guard, frontierAction, value,
      _hnode, haction, hvalue, hevent⟩
  rw [hevent]
  change
    CommitAvailable G state.1 who
      { node := node, value := G.nodeTypedValue node value }
  exact
    frontierCommitAvailable_of_legal_value
      G hlegal haction hvalue

omit [Fintype Player] in
/-- Ready internal primitive events, enumerated over graph nodes in the supplied
order. -/
noncomputable def readyInternalEventsFromNodes
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (state : (PrimitiveMachineOf spec).State)
    (nodes : List (Fin G.nodeCount)) :
    List (PrimitiveMachineOf spec).Event := by
  classical
  exact nodes.filterMap fun node : Fin G.nodeCount =>
    if _hready : ReadyInternalNode G state.1 node then
      some (Machine.Event.internal (M := PrimitiveMachineOf spec)
        ({ node := node } : (PrimitiveMachineOf spec).Internal))
    else
      none

omit [Fintype Player] in
theorem mem_readyInternalEventsFromNodes_iff
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (state : (PrimitiveMachineOf spec).State)
    (nodes : List (Fin G.nodeCount))
    {event : (PrimitiveMachineOf spec).Event} :
    event ∈ readyInternalEventsFromNodes spec state nodes ↔
      ∃ node, node ∈ nodes ∧ ReadyInternalNode G state.1 node ∧
        event =
          Machine.Event.internal (M := PrimitiveMachineOf spec)
            ({ node := node } : (PrimitiveMachineOf spec).Internal) := by
  classical
  constructor
  · intro hmem
    unfold readyInternalEventsFromNodes at hmem
    rw [List.mem_filterMap] at hmem
    rcases hmem with ⟨node, hnode, hselected⟩
    by_cases hready : ReadyInternalNode G state.1 node
    · simp [hready] at hselected
      exact ⟨node, hnode, hready, hselected.symm⟩
    · simp [hready] at hselected
  · intro h
    rcases h with ⟨node, hnode, hready, hevent⟩
    unfold readyInternalEventsFromNodes
    rw [List.mem_filterMap]
    refine ⟨node, hnode, ?_⟩
    simp [hready, hevent]

omit [Fintype Player] in
theorem readyInternalEventsFromNodes_available
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    {state : (PrimitiveMachineOf spec).State}
    {nodes : List (Fin G.nodeCount)}
    {event : (PrimitiveMachineOf spec).Event}
    (hmem : event ∈ readyInternalEventsFromNodes spec state nodes) :
    (PrimitiveMachineOf spec).EventAvailable state event := by
  rcases
      (mem_readyInternalEventsFromNodes_iff
        spec state nodes).mp hmem with
    ⟨node, _hnode, hready, hevent⟩
  rw [hevent]
  change InternalAvailable G state.1 { node := node }
  exact
    InternalAvailable.of_readyInternalNode spec.graphWF
      (reachable_storeCoherent spec.graphWF state.2)
      hready

/-- Native machine round view induced by graph frontiers and certified
frontier-round semantics. -/
noncomputable def frontierRoundView
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (presentation : CheckpointPresentation G)
    (semantics : FrontierRoundSemantics spec presentation) :
    (PrimitiveMachineOf spec).RoundView where
  Act := FrontierAct G
  active := frontierActive G
  availableActions := frontierAvailableActions G
  transition := fun state action => semantics.transition state action
  eventBatch := fun state action dst => by
    classical
    if hlegal :
        JointActionLegal (FrontierAct G)
          (frontierActive G)
          (PrimitiveMachineOf spec).terminal
          (frontierAvailableActions G) state action then
      exact semantics.eventBatch state ⟨action, hlegal⟩ dst
    else
      exact []
  terminal_active_eq_empty := by
    intro state hterminal
    classical
    unfold frontierActive
    by_cases hinternal : (readyInternalNodes G state.1).Nonempty
    · simp [hinternal]
    · simpa [hinternal] using
        activePlayers_eq_empty_of_terminal G hterminal
  nonterminal_exists_legal := by
    intro state hterminal
    classical
    by_cases hinternal : (readyInternalNodes G state.1).Nonempty
    · refine ⟨GameTheory.noopAction (FrontierAct G), hterminal, ?_⟩
      intro who
      simp [frontierActive, hinternal]
    · rcases exists_legal_frontier_action_of_reachable
        spec.graphWF semantics.guards hterminal with
        ⟨action, hlegal⟩
      refine ⟨action, ?_⟩
      simpa [GameTheory.JointActionLegal, frontierActive, hinternal,
        frontierAvailableActions, PrimitiveMachineOf,
        ToMachine.primitiveMachine] using hlegal

/-- For the frontier round view, local optional-move legality at a bounded
state is determined by the presentation depth plus the public and player
observations. -/
theorem frontierRoundView_boundedLocallyLegalAtState_iff_of_observe_eq
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (presentation : CheckpointPresentation G)
    (semantics : FrontierRoundSemantics spec presentation)
    {horizon : Nat}
    {left right : (PrimitiveMachineOf spec).BoundedState horizon}
    {who : Player} {move : Option (FrontierAct G who)}
    (hdepth : left.depth = right.depth)
    (hpublic :
      publicObserve G left.state.1 =
        publicObserve G right.state.1)
    (hprivate :
        observe G left.state.1 who =
        observe G right.state.1 who) :
    (frontierRoundView spec presentation semantics).boundedLocallyLegalAtState
        horizon left who move ↔
      (frontierRoundView spec presentation semantics).boundedLocallyLegalAtState
        horizon right who move := by
  classical
  cases move with
  | none =>
      change
        (who ∉
            (if horizon ≤ left.depth then ∅
             else frontierActive G left.state)) ↔
          (who ∉
            (if horizon ≤ right.depth then ∅
             else frontierActive G right.state))
      rw [hdepth]
      by_cases hcut : horizon ≤ right.depth
      · rw [if_pos hcut, if_pos hcut]
      · rw [if_neg hcut, if_neg hcut]
        exact
          not_congr
            (mem_frontierActive_iff_of_observe_eq hpublic hprivate)
  | some action =>
      change
        ((who ∈
            (if horizon ≤ left.depth then ∅
             else frontierActive G left.state)) ∧
          action ∈
            (if horizon ≤ left.depth then ∅
             else frontierAvailableActions G left.state who)) ↔
        ((who ∈
            (if horizon ≤ right.depth then ∅
             else frontierActive G right.state)) ∧
          action ∈
            (if horizon ≤ right.depth then ∅
             else frontierAvailableActions G right.state who))
      rw [hdepth]
      by_cases hcut : horizon ≤ right.depth
      · rw [if_pos hcut, if_pos hcut, if_pos hcut, if_pos hcut]
      · rw [if_neg hcut, if_neg hcut, if_neg hcut, if_neg hcut]
        exact
          and_congr
            (mem_frontierActive_iff_of_observe_eq hpublic hprivate)
            (frontierAvailableActions_iff_of_observe_eq
              spec.graphWF hprivate)

/-- The canonical frontier round view has observable menus: a player's bounded
information state determines exactly which optional moves are legal for that
player. -/
theorem frontierRoundView_menusObservable
    {G : Graph Player L} (spec : ToMachine.GraphMachineSpec G)
    (presentation : CheckpointPresentation G)
    (semantics : FrontierRoundSemantics spec presentation)
    (horizon : Nat) :
    (frontierRoundView spec presentation semantics).MenusObservable
      horizon := by
  classical
  let view := frontierRoundView spec presentation semantics
  intro who left right hview
  have hdepth :
      left.lastState.depth = right.lastState.depth :=
    Machine.RoundView.BoundedHistory.depth_eq_of_playerView_eq
      (view := view) left right who hview
  have hlen :
      left.steps.length = right.steps.length := by
    have hleft :=
      Machine.RoundView.BoundedHistory.observationEvents_playerView_length
        (view := view) left who
    have hright :=
      Machine.RoundView.BoundedHistory.observationEvents_playerView_length
        (view := view) right who
    rw [← hleft, hview, hright]
  have hobs :
      observe G left.lastState.state.1 who =
        observe G right.lastState.state.1 who ∧
      publicObserve G left.lastState.state.1 =
        publicObserve G right.lastState.state.1 := by
    by_cases hleftNil : left.steps = []
    · have hrightNil : right.steps = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hleftNil]
        simp
      have hleftEq :
          left = Machine.RoundView.BoundedHistory.nil view horizon := by
        apply Machine.RoundView.BoundedHistory.ext
        simpa using hleftNil
      have hrightEq :
          right = Machine.RoundView.BoundedHistory.nil view horizon := by
        apply Machine.RoundView.BoundedHistory.ext
        simpa using hrightNil
      rw [hleftEq, hrightEq]
      simp [view, ToMachine.primitiveMachine]
    · have hrightNe : right.steps ≠ [] := by
        intro hrightNil
        apply hleftNil
        apply List.eq_nil_of_length_eq_zero
        rw [hlen, hrightNil]
        simp
      have hleftLatest :=
        Machine.RoundView.BoundedHistory.latestObservation?_history_of_ne_nil
          (view := view) left who hleftNil
      have hrightLatest :=
        Machine.RoundView.BoundedHistory.latestObservation?_history_of_ne_nil
          (view := view) right who hrightNe
      have hlatest :
          some
              ((PrimitiveMachineOf spec).observe who left.lastState.state,
                (PrimitiveMachineOf spec).publicView left.lastState.state) =
            some
              ((PrimitiveMachineOf spec).observe who right.lastState.state,
                (PrimitiveMachineOf spec).publicView right.lastState.state) := by
        rw [← hleftLatest, hview, hrightLatest]
      have hpair :
          ((PrimitiveMachineOf spec).observe who left.lastState.state,
              (PrimitiveMachineOf spec).publicView left.lastState.state) =
            ((PrimitiveMachineOf spec).observe who right.lastState.state,
              (PrimitiveMachineOf spec).publicView right.lastState.state) :=
        Option.some.inj hlatest
      constructor
      · simpa [PrimitiveMachineOf, ToMachine.primitiveMachine] using
          congrArg Prod.fst hpair
      · simpa [PrimitiveMachineOf, ToMachine.primitiveMachine] using
          congrArg Prod.snd hpair
  ext move
  rw [Machine.RoundView.mem_boundedAvailableMoves_iff,
    Machine.RoundView.mem_boundedAvailableMoves_iff]
  exact
    frontierRoundView_boundedLocallyLegalAtState_iff_of_observe_eq
      spec presentation semantics
      (left := left.lastState) (right := right.lastState)
      (who := who) (move := move)
      hdepth hobs.2 hobs.1

end EventGraph

end Vegas
