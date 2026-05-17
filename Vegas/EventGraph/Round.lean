import GameTheory.Core.JointAction
import Vegas.EventGraph.ToMachine
import Vegas.Machine.Trace

/-!
# Event-graph frontier rounds

This module defines the native player-facing round semantics of event graphs.
The definitions are machine/event-graph facts, not FOSG presentation data.  FOSG
and EFG bridges may reuse them as proof obligations.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Player-facing action for a frontier round.  The action supplies a candidate
field patch for each event node; state-local availability uses only the patches
for frontier nodes owned by the player. -/
structure PlayerRoundAction (G : Vegas.EventGraph Player L) (_who : Player) where
  patch : G.Node → G.FieldPatch

namespace PlayerRoundAction

@[reducible] noncomputable instance instFintype
    (G : Vegas.EventGraph Player L) (who : Player)
    [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype (PlayerRoundAction G who) := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (StoredValue (L.Val (G.fieldTy field)))) :=
    fun _ => inferInstance
  letI : Fintype G.FieldPatch := by
    dsimp [EventGraph.FieldPatch]
    infer_instance
  let e : PlayerRoundAction G who ≃ (G.Node → G.FieldPatch) :=
    { toFun := fun action => action.patch
      invFun := fun patch => { patch := patch }
      left_inv := by
        intro action
        cases action
        rfl
      right_inv := by
        intro patch
        rfl }
  exact Fintype.ofEquiv (G.Node → G.FieldPatch) e.symm

end PlayerRoundAction

/-- Players who own at least one node in the current frontier. -/
noncomputable def roundActive
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration) :
    Finset Player := by
  classical
  exact cfg.frontier.biUnion fun node =>
    match (G.sem node).actor with
    | some who => {who}
    | none => ∅

theorem mem_roundActive_iff
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) :
    who ∈ roundActive G cfg ↔
      ∃ node, node ∈ cfg.frontier ∧ (G.sem node).actor = some who := by
  classical
  unfold roundActive
  constructor
  · intro hmem
    rcases Finset.mem_biUnion.mp hmem with ⟨node, hfrontier, hwho⟩
    cases hactor : (G.sem node).actor with
    | none =>
        simp [hactor] at hwho
    | some owner =>
        have howner : who = owner := by
          simpa [hactor] using hwho
        subst who
        exact ⟨node, hfrontier, hactor⟩
  · intro h
    rcases h with ⟨node, hfrontier, hactor⟩
    exact Finset.mem_biUnion.mpr
      ⟨node, hfrontier, by simp [hactor]⟩

/-- Round actions available to a player at a graph configuration. -/
def roundAvailable
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (PlayerRoundAction G who) :=
  { action |
      ∀ {node},
        node ∈ cfg.frontier →
        (G.sem node).actor = some who →
          G.patchLegal node (action.patch node) ∧
            G.actionLegal cfg.result node (action.patch node) }

/-- Player-facing optional menu for a frontier round.

The `none` move means the player is not called in this frontier round. A
`some action` move means the player is active and the round action is legal for
every current frontier node owned by that player. -/
def roundMenu
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (Option (PlayerRoundAction G who)) :=
  { move |
    match move with
    | none => who ∉ roundActive G cfg
    | some action =>
        who ∈ roundActive G cfg ∧ action ∈ roundAvailable G cfg who }

@[simp] theorem mem_roundMenu_none
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) :
    (none : Option (PlayerRoundAction G who)) ∈ roundMenu G cfg who ↔
      who ∉ roundActive G cfg := by
  rfl

@[simp] theorem mem_roundMenu_some
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) (action : PlayerRoundAction G who) :
    some action ∈ roundMenu G cfg who ↔
      who ∈ roundActive G cfg ∧ action ∈ roundAvailable G cfg who := by
  rfl

/-- Execute one node from a frontier round using the joint round action.
Unavailable primitive events stutter through the underlying total machine step;
frontier soundness lemmas show the intended round nodes remain available across
linearizations. -/
noncomputable def roundStepNode
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerRoundAction G))
    (node : G.Node) (cfg : G.Configuration) :
    PMF G.Configuration :=
  match (G.sem node).actor with
  | some who =>
      match joint who with
      | some action =>
          stepPlay G who { node := node, patch := action.patch node } cfg
      | none => PMF.pure cfg
  | none => stepInternal G (.node node) cfg

/-- Primitive machine event selected for one event node by a frontier-round
joint action. Missing player coordinates are represented by the graph machine's
unavailable `idle` internal event, whose total step stutters. Legal round
actions never need this fallback for current frontier nodes. -/
noncomputable def roundPrimitiveEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G)) (node : G.Node) :
    (G.toMachine iface).Event :=
  match (G.sem node).actor with
  | some who =>
      match joint who with
      | some action =>
          .play who { node := node, patch := action.patch node }
      | none => .internal .idle
  | none => .internal (.node node)

@[simp] theorem toMachine_step_roundPrimitiveEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (node : G.Node) (cfg : G.Configuration) :
    (G.toMachine iface).step
        (roundPrimitiveEvent G iface joint node) cfg =
      roundStepNode G joint node cfg := by
  cases hactor : (G.sem node).actor with
  | none =>
      simp [roundPrimitiveEvent, roundStepNode, Machine.step, toMachine,
        hactor]
  | some who =>
      cases hmove : joint who <;>
        simp [roundPrimitiveEvent, roundStepNode, Machine.step, toMachine,
          stepInternal, hactor, hmove]

/-- A legal frontier-round joint action selects an available primitive machine
event for every node in the current frontier. -/
theorem roundPrimitiveEvent_available_of_legal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    {node : G.Node} (hfrontier : node ∈ cfg.frontier) :
    (G.toMachine iface).EventAvailable cfg
      (roundPrimitiveEvent G iface joint node) := by
  classical
  cases hactor : (G.sem node).actor with
  | none =>
      have hevent :
          roundPrimitiveEvent G iface joint node =
            Machine.Event.internal (InternalEvent.node node) := by
        simp [roundPrimitiveEvent, hactor]
      rw [hevent]
      change
        (InternalEvent.node node : InternalEvent G) ∈
          availableInternal G cfg
      exact ⟨hfrontier, hactor⟩
  | some who =>
      have hactive : who ∈ roundActive G cfg :=
        (mem_roundActive_iff G cfg who).mpr
          ⟨node, hfrontier, hactor⟩
      have hcoord := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ roundActive G cfg ∧
                action ∈ roundAvailable G cfg who := by
            simpa [hmove] using hcoord
          have hnodeLegal :
              G.patchLegal node (action.patch node) ∧
                G.actionLegal cfg.result node (action.patch node) :=
            hpair.2 hfrontier hactor
          have hevent :
              roundPrimitiveEvent G iface joint node =
                Machine.Event.play who
                  ({ node := node, patch := action.patch node } :
                    PlayerAction G who) := by
            simp [roundPrimitiveEvent, hactor, hmove]
          rw [hevent]
          change
            { node := node, patch := action.patch node } ∈
              available G cfg who
          exact ⟨hfrontier, hactor, hnodeLegal.1, hnodeLegal.2⟩

/-- Under stable frontier rounds, every primitive event selected for a
different node in a legal frontier round remains available after this frontier
node has executed. -/
theorem roundPrimitiveEvent_available_after_withPatch_of_ne
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hjoint :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    {first second : G.Node}
    {firstPatch : G.FieldPatch}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : G.patchLegal first firstPatch) :
    (G.toMachine iface).EventAvailable
      (cfg.withPatch firstPatch hfirst hfirstLegal)
      (roundPrimitiveEvent G iface joint second) := by
  classical
  cases hactor : (G.sem second).actor with
  | none =>
      have hfrontierAfter :
          second ∈
            (cfg.withPatch firstPatch hfirst hfirstLegal).frontier :=
        cfg.withPatch_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
      have hevent :
          roundPrimitiveEvent G iface joint second =
            Machine.Event.internal
              (InternalEvent.node second : InternalEvent G) := by
        simp [roundPrimitiveEvent, hactor]
      rw [hevent]
      change
        (InternalEvent.node second : InternalEvent G) ∈
          availableInternal G
            (cfg.withPatch firstPatch hfirst hfirstLegal)
      exact ⟨hfrontierAfter, hactor⟩
  | some who =>
      have hactive : who ∈ roundActive G cfg :=
        (mem_roundActive_iff G cfg who).mpr
          ⟨second, hsecond, hactor⟩
      have hcoord := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ roundActive G cfg ∧
                action ∈ roundAvailable G cfg who := by
            simpa [hmove] using hcoord
          have hnodeLegal :
              G.patchLegal second (action.patch second) ∧
                G.actionLegal cfg.result second
                  (action.patch second) :=
            hpair.2 hsecond hactor
          have havailable :
              ({ node := second, patch := action.patch second } :
                PlayerAction G who) ∈
                available G
                  (cfg.withPatch firstPatch hfirst hfirstLegal) who :=
            hsound.actionStable cfg hfirst hsecond hne hfirstLegal
              ⟨hsecond, hactor, hnodeLegal.1, hnodeLegal.2⟩
          have hevent :
              roundPrimitiveEvent G iface joint second =
                Machine.Event.play who
                  ({ node := second, patch := action.patch second } :
                    PlayerAction G who) := by
            simp [roundPrimitiveEvent, hactor, hmove]
          rw [hevent]
          change
            ({ node := second, patch := action.patch second } :
              PlayerAction G who) ∈
              available G
                (cfg.withPatch firstPatch hfirst hfirstLegal) who
          exact havailable

/-- The primitive machine event list represented by one frontier round. The
order is the canonical `Finset.toList` order used by `roundTransition`; order
invariance is a separate theorem about independent frontier nodes. -/
noncomputable def roundPrimitiveEvents
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    List (G.toMachine iface).Event :=
  cfg.frontier.toList.map (roundPrimitiveEvent G iface joint)

/-- Every primitive event listed for a legal frontier round is available at the
round's source configuration. Availability after earlier events in a
linearization is the separate frontier-stability theorem. -/
theorem mem_roundPrimitiveEvents_available_of_legal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    {event : (G.toMachine iface).Event}
    (hmem : event ∈ roundPrimitiveEvents G iface cfg joint) :
    (G.toMachine iface).EventAvailable cfg event := by
  classical
  rcases List.mem_map.mp hmem with ⟨node, hnode, rfl⟩
  have hfrontier : node ∈ cfg.frontier := by
    simpa using hnode
  exact roundPrimitiveEvent_available_of_legal
    G iface hlegal hfrontier

private theorem runEventsFrom_roundPrimitiveEvents_go
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (nodes : List G.Node) (acc : PMF G.Configuration) :
    (nodes.map (roundPrimitiveEvent G iface joint)).foldl
        (fun acc event => acc.bind fun current =>
          (G.toMachine iface).step event current)
        acc =
      nodes.foldl
        (fun acc node => acc.bind fun current =>
          roundStepNode G joint node current)
        acc := by
  induction nodes generalizing acc with
  | nil => rfl
  | cons node nodes ih =>
      simp [List.map, List.foldl,
        toMachine_step_roundPrimitiveEvent, ih]

/-- Execute the current frontier as one native graph round.  The list order is
a definition device; `HasStableFrontierRounds` is the hypothesis that
source-legal player actions do not stutter while this linearization is
executed.  Stronger order-invariance facts are proved for event graphs in
`FrontierStability`. -/
noncomputable def roundTransition
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF G.Configuration :=
  cfg.frontier.toList.foldl
    (fun acc node => acc.bind fun state => roundStepNode G joint node state)
    (PMF.pure cfg)

/-- A graph frontier round is exactly the primitive machine run obtained by
executing the round's canonical frontier event list. -/
theorem roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    roundTransition G cfg joint =
      (G.toMachine iface).runEventsFrom
        (roundPrimitiveEvents G iface cfg joint) cfg := by
  classical
  rw [roundTransition, roundPrimitiveEvents, Machine.runEventsFrom]
  exact
    (runEventsFrom_roundPrimitiveEvents_go G iface joint
      cfg.frontier.toList (PMF.pure cfg)).symm

end EventGraph

end Vegas
