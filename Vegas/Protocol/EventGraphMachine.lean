import Vegas.Protocol.FOSG
import Vegas.Protocol.Trace

/-!
# Event Graph Machines

This module interprets an extensional `EventGraph.Configuration` as the
generic asynchronous `Machine` carrier.

The primitive machine step executes one enabled event node. The FOSG
presentation below exposes whole frontier rounds: it batches the current
frontier into one player-facing transition while the primitive machine remains
the executable carrier.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Player-owned frontier nodes have at least one legal concrete action. -/
def HasAvailablePlayerActions (G : Vegas.EventGraph Player L) : Prop :=
  ∀ (cfg : G.Configuration) {node : G.Node} {who : Player},
    node ∈ cfg.frontier →
    (G.sem node).actor = some who →
      ∃ slice, G.sliceLegal node slice ∧
        G.actionLegal cfg.result node slice

/-- Static player action alphabet for an event graph: choose an event node
and a result slice for that node. State-local availability restricts this to
enabled nodes owned by the player and legal slices for the current result
assignment. -/
structure PlayerAction (G : Vegas.EventGraph Player L) (_who : Player) where
  node : G.Node
  slice : G.WriteSlice

namespace PlayerAction

/-- Player actions are finite when event nodes, fields, and field values are
finite. -/
@[reducible] noncomputable instance instFintype
    (G : Vegas.EventGraph Player L) (who : Player)
    [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype (PlayerAction G who) := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (StoredValue (L.Val (G.fieldTy field)))) :=
    fun _ => inferInstance
  letI : Fintype G.WriteSlice := by
    dsimp [EventGraph.WriteSlice]
    infer_instance
  let e : PlayerAction G who ≃ G.Node × G.WriteSlice :=
    { toFun := fun action => (action.node, action.slice)
      invFun := fun pair => { node := pair.1, slice := pair.2 }
      left_inv := by
        intro action
        cases action
        rfl
      right_inv := by
        intro pair
        cases pair
        rfl }
  exact Fintype.ofEquiv (G.Node × G.WriteSlice) e.symm

end PlayerAction

/-- Player-facing action for a frontier round.  The action supplies a candidate
write slice for each event node; state-local availability uses only the slices
for frontier nodes owned by the player. -/
structure PlayerRoundAction (G : Vegas.EventGraph Player L) (_who : Player) where
  slice : G.Node → G.WriteSlice

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
  letI : Fintype G.WriteSlice := by
    dsimp [EventGraph.WriteSlice]
    infer_instance
  let e : PlayerRoundAction G who ≃ (G.Node → G.WriteSlice) :=
    { toFun := fun action => action.slice
      invFun := fun slice => { slice := slice }
      left_inv := by
        intro action
        cases action
        rfl
      right_inv := by
        intro slice
        rfl }
  exact Fintype.ofEquiv (G.Node → G.WriteSlice) e.symm

end PlayerRoundAction

/-- Internal events execute enabled non-player nodes. `idle` is never
available; it only gives terminal FOSG presentations a total internal turn
without inventing an executable event node. -/
inductive InternalEvent (G : Vegas.EventGraph Player L) where
  | node (node : G.Node)
  | idle

namespace InternalEvent

/-- Internal events are finite when event nodes are finite. -/
@[reducible] noncomputable instance instFintype
    (G : Vegas.EventGraph Player L) [Fintype G.Node] :
    Fintype (InternalEvent G) := by
  classical
  letI : DecidableEq (InternalEvent G) := Classical.decEq _
  refine Fintype.mk
    (((Finset.univ : Finset G.Node).image InternalEvent.node) ∪
      {InternalEvent.idle}) ?_
  intro event
  cases event with
  | node node =>
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨node, Finset.mem_univ _, rfl⟩))
  | idle =>
      simp

end InternalEvent

/-- Observation/outcome interface needed to expose a graph as a `Machine`.

Execution is native to the event graph; this structure only says how completed event-graph state
is observed and scored. -/
structure MachineInterface (G : Vegas.EventGraph Player L) where
  Public : Type
  Obs : Player → Type
  Outcome : Type
  publicView : G.Configuration → Public
  observe : (who : Player) → G.Configuration → Obs who
  outcome : G.Configuration → Outcome
  utility : Outcome → Payoff Player

/-- Player actions available at a graph configuration. -/
def available
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (PlayerAction G who) :=
  { action |
      action.node ∈ cfg.frontier ∧
        (G.sem action.node).actor = some who ∧
          G.sliceLegal action.node action.slice ∧
            G.actionLegal cfg.result action.node action.slice }

/-- Internal events available at a graph configuration. -/
def availableInternal
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration) :
    Set (InternalEvent G) :=
  { event |
      match event with
      | .node node =>
          node ∈ cfg.frontier ∧
            (G.sem node).actor = none
      | .idle => False }

/-- Soundness condition for exposing graph frontiers as whole FOSG rounds.

The first field prevents player-owned frontier nodes from deadlocking.  The
second field says that once a player action for one frontier node is legal, it
remains legal after any different frontier node in the same source frontier has
been recorded.  This is the graph-level condition ruling out player-action
legality races inside a batched frontier round. -/
structure HasStableFrontierRounds (G : Vegas.EventGraph Player L) : Prop where
  availablePlayerActions : G.HasAvailablePlayerActions
  actionStable :
    ∀ (cfg : G.Configuration)
      {first : G.Node} {firstSlice : G.WriteSlice}
      (hfirst : first ∈ cfg.frontier)
      {who : Player} {action : PlayerAction G who}
      (_ : action.node ∈ cfg.frontier)
      (_ : action.node ≠ first)
      (hfirstLegal : G.sliceLegal first firstSlice),
      action ∈ available G cfg who →
        action ∈ available G
          (cfg.withResult firstSlice hfirst hfirstLegal) who

/-- Execute one available player node. Unavailable events stutter, matching the
total-step convention of `Machine`. -/
noncomputable def stepPlay
    (G : Vegas.EventGraph Player L) (who : Player)
    (action : PlayerAction G who) (cfg : G.Configuration) :
    PMF G.Configuration := by
  classical
  exact
    if h : action ∈ available G cfg who then
      PMF.pure (cfg.withResult action.slice h.1 h.2.2.1)
    else
      PMF.pure cfg

/-- Execute one available internal node. The graph's internal kernel chooses
the result slice. Any slice outside the legal predicate stutters. -/
noncomputable def stepInternal
    (G : Vegas.EventGraph Player L) (event : InternalEvent G)
    (cfg : G.Configuration) : PMF G.Configuration := by
  classical
  exact
    match event with
    | .node node =>
        if h : (InternalEvent.node node : InternalEvent G) ∈
            availableInternal G cfg then
          have hnode :
              node ∈ cfg.frontier ∧ (G.sem node).actor = none := by
            simpa [availableInternal] using h
          (G.internalKernel node cfg.result).bind fun slice =>
            if hlegal : G.sliceLegal node slice then
              PMF.pure (cfg.withResult slice hnode.1 hlegal)
            else
              PMF.pure cfg
        else
          PMF.pure cfg
    | .idle => PMF.pure cfg

/-- Canonical asynchronous machine for an event graph. -/
noncomputable def toMachine
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G) :
    Machine Player where
  State := G.Configuration
  Action := PlayerAction G
  Internal := InternalEvent G
  Public := iface.Public
  Obs := iface.Obs
  Outcome := iface.Outcome
  init := Configuration.initial G
  available := available G
  availableInternal := availableInternal G
  stepPlay := stepPlay G
  stepInternal := stepInternal G
  terminal := Configuration.terminal
  publicView := iface.publicView
  observe := iface.observe
  outcome := iface.outcome
  utility := iface.utility

@[simp] theorem toMachine_init
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G) :
    (G.toMachine iface).init = Configuration.initial G := rfl

@[simp] theorem toMachine_terminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : (G.toMachine iface).State) :
    (G.toMachine iface).terminal cfg = cfg.terminal := rfl

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
          G.sliceLegal node (action.slice node) ∧
            G.actionLegal cfg.result node (action.slice node) }

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
          stepPlay G who { node := node, slice := action.slice node } cfg
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
          .play who { node := node, slice := action.slice node }
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
              G.sliceLegal node (action.slice node) ∧
                G.actionLegal cfg.result node (action.slice node) :=
            hpair.2 hfrontier hactor
          have hevent :
              roundPrimitiveEvent G iface joint node =
                Machine.Event.play who
                  ({ node := node, slice := action.slice node } :
                    PlayerAction G who) := by
            simp [roundPrimitiveEvent, hactor, hmove]
          rw [hevent]
          change
            { node := node, slice := action.slice node } ∈
              available G cfg who
          exact ⟨hfrontier, hactor, hnodeLegal.1, hnodeLegal.2⟩

/-- Under stable frontier rounds, every primitive event selected for a
different node in a legal frontier round remains available after this frontier
node has executed. -/
theorem roundPrimitiveEvent_available_after_withResult_of_ne
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hjoint :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    {first second : G.Node}
    {firstSlice : G.WriteSlice}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : G.sliceLegal first firstSlice) :
    (G.toMachine iface).EventAvailable
      (cfg.withResult firstSlice hfirst hfirstLegal)
      (roundPrimitiveEvent G iface joint second) := by
  classical
  cases hactor : (G.sem second).actor with
  | none =>
      have hfrontierAfter :
          second ∈
            (cfg.withResult firstSlice hfirst hfirstLegal).frontier :=
        cfg.withResult_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
      have hevent :
          roundPrimitiveEvent G iface joint second =
            Machine.Event.internal
              (InternalEvent.node second : InternalEvent G) := by
        simp [roundPrimitiveEvent, hactor]
      rw [hevent]
      change
        (InternalEvent.node second : InternalEvent G) ∈
          availableInternal G
            (cfg.withResult firstSlice hfirst hfirstLegal)
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
              G.sliceLegal second (action.slice second) ∧
                G.actionLegal cfg.result second
                  (action.slice second) :=
            hpair.2 hsecond hactor
          have havailable :
              ({ node := second, slice := action.slice second } :
                PlayerAction G who) ∈
                available G
                  (cfg.withResult firstSlice hfirst hfirstLegal) who :=
            hsound.actionStable cfg hfirst hsecond hne hfirstLegal
              ⟨hsecond, hactor, hnodeLegal.1, hnodeLegal.2⟩
          have hevent :
              roundPrimitiveEvent G iface joint second =
                Machine.Event.play who
                  ({ node := second, slice := action.slice second } :
                    PlayerAction G who) := by
            simp [roundPrimitiveEvent, hactor, hmove]
          rw [hevent]
          change
            ({ node := second, slice := action.slice second } :
              PlayerAction G who) ∈
              available G
                (cfg.withResult firstSlice hfirst hfirstLegal) who
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

/-- Execute the current frontier as one FOSG round.  The list order is a
definition device; `HasStableFrontierRounds` is the hypothesis that source-legal
player actions do not stutter while this linearization is executed.  Stronger
order-invariance facts are proved for event graphs in `FrontierStability`. -/
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

/-- FOSG presentation of a protocol-graph machine by stable frontier rounds. -/
noncomputable def toFOSGView
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) :
    (G.toMachine iface).FOSGView where
  Act := PlayerRoundAction G
  active := roundActive G
  availableActions := roundAvailable G
  transition := fun cfg action => roundTransition G cfg action.1
  reward := fun _ _ dst who => iface.utility (iface.outcome dst) who
  terminal_active_eq_empty := by
    intro cfg hterminal
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who hmem
    rcases (mem_roundActive_iff G cfg who).mp hmem with
      ⟨node, hfrontier, _hactor⟩
    exact (cfg.not_terminal_of_mem_frontier hfrontier) hterminal
  nonterminal_exists_legal := by
    intro cfg hterminal
    classical
    let mkSlice (who : Player) (node : G.Node) : G.WriteSlice :=
      if h : node ∈ cfg.frontier ∧ (G.sem node).actor = some who then
        Classical.choose (hsound.availablePlayerActions cfg h.1 h.2)
      else
        fun _ => none
    let joint : JointAction (PlayerRoundAction G) := fun who =>
      if who ∈ roundActive G cfg then
        some { slice := mkSlice who }
      else
        none
    refine ⟨joint, hterminal, ?_⟩
    intro who
    by_cases hactive : who ∈ roundActive G cfg
    · have hjoint : joint who = some { slice := mkSlice who } := by
        simp [joint, hactive]
      rw [hjoint]
      refine ⟨hactive, ?_⟩
      intro node hfrontier hactor
      have hnode : node ∈ cfg.frontier ∧ (G.sem node).actor = some who :=
        ⟨hfrontier, hactor⟩
      change
        G.sliceLegal node (mkSlice who node) ∧
          G.actionLegal cfg.result node (mkSlice who node)
      unfold mkSlice
      split
      · rename_i h
        exact Classical.choose_spec
          (hsound.availablePlayerActions cfg h.1 h.2)
      · rename_i h
        exact False.elim (h hnode)
    · have hjoint : joint who = none := by
        simp [joint, hactive]
      rw [hjoint]
      exact hactive

/-- The optional-move set of the FOSG induced by an event graph is the
graph-level `roundMenu`.  Bridges the strategic FOSG carrier (which pairs
each player's optional round move with a `none` for inactive rounds) and the
direct configuration-level menu. -/
@[simp] theorem toFOSGView_toFOSG_availableMovesAtState_eq_roundMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    (cfg : G.Configuration) (who : Player) :
    (G.toFOSGView iface hsound).toFOSG.availableMovesAtState cfg who =
      G.roundMenu cfg who := by
  ext move
  cases move <;> rfl

/-- The bounded-FOSG version: before the horizon cutoff, optional round moves
agree with the player-facing graph menu. -/
theorem toFOSGView_toBoundedFOSG_availableMovesAtState_eq_roundMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat) (who : Player)
    (state : (G.toMachine iface).BoundedState horizon)
    (hcut : ¬ horizon ≤ state.depth) :
    ((G.toFOSGView iface hsound).toBoundedFOSG horizon).availableMovesAtState
        state who =
      G.roundMenu state.state who := by
  ext move
  rw [GameTheory.FOSG.mem_availableMovesAtState_iff]
  cases move with
  | none =>
      change ¬ who ∈ Machine.FOSGView.boundedActive _ horizon state ↔ _
      simp [Machine.FOSGView.boundedActive, hcut]
      rfl
  | some action =>
      change who ∈ Machine.FOSGView.boundedActive _ horizon state ∧
          action ∈ Machine.FOSGView.boundedAvailableActions _ horizon state who ↔ _
      simp [Machine.FOSGView.boundedActive,
        Machine.FOSGView.boundedAvailableActions, hcut]
      rfl

/-- One bounded graph-FOSG transition, projected back to graph configurations,
is the primitive machine run of the round's canonical frontier event list. -/
theorem toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventsFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action) =
      (G.toMachine iface).runEventsFrom
        (roundPrimitiveEvents G iface state.state action.1)
        state.state := by
  rw [Machine.FOSGView.toBoundedFOSG_transition_map_state]
  change
    roundTransition G state.state action.1 =
      (G.toMachine iface).runEventsFrom
        (roundPrimitiveEvents G iface state.state action.1)
        state.state
  exact roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    G iface state.state action.1

/-- One bounded graph-FOSG transition, projected back to graph configurations,
is one blocked primitive machine run.  This is the one-step form used by
trace-level simulations: FOSG histories compose blocks; primitive machine
traces flatten them. -/
theorem toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action) =
      (G.toMachine iface).runEventBlocksFrom
        [roundPrimitiveEvents G iface state.state action.1]
        state.state := by
  rw [toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventsFrom]
  simp

/-- Primitive event blocks extracted from a bounded graph-FOSG step list.

Each bounded FOSG step is one frontier round.  This projection forgets the
sampled checkpoint destination and keeps the primitive machine event block
selected by the round action at the step source. -/
noncomputable def boundedFOSGStepEventBlocks
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (steps :
      List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)) :
    List (List (G.toMachine iface).Event) :=
  steps.map fun step =>
    roundPrimitiveEvents G iface step.src.state step.act.1

/-- Primitive event blocks extracted from a bounded graph-FOSG history. -/
noncomputable def boundedFOSGHistoryEventBlocks
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    List (List (G.toMachine iface).Event) :=
  boundedFOSGStepEventBlocks G iface hsound horizon h.steps

/-- Every realized bounded graph-FOSG step chain is backed by a primitive
machine blocked run whose support contains the same checkpoint endpoint. -/
theorem boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps :
        List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)},
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).StepChainFrom
          start steps →
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
            start steps).state ∈
          ((G.toMachine iface).runEventBlocksFrom
            (boundedFOSGStepEventBlocks G iface hsound horizon steps)
            start.state).support
  | start, [], _hchain => by
      simp [boundedFOSGStepEventBlocks, GameTheory.FOSG.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      cases hsrc
      let block : List (G.toMachine iface).Event :=
        roundPrimitiveEvents G iface step.src.state step.act.1
      have hblock :
          step.dst.state ∈
            ((G.toMachine iface).runEventBlocksFrom [block]
              step.src.state).support := by
        have hmap :
            step.dst.state ∈
              (PMF.map (fun bounded => bounded.state)
                (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
                  step.src step.act)).support := by
          exact (PMF.mem_support_map_iff _ _ _).2
            ⟨step.dst, (PMF.mem_support_iff _ _).2 step.support, rfl⟩
        rw [toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) (state := step.src) (action := step.act)] at hmap
        simpa [block] using hmap
      have htailSupport :
          (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
              step.dst steps).state ∈
            ((G.toMachine iface).runEventBlocksFrom
              (boundedFOSGStepEventBlocks G iface hsound horizon steps)
              step.dst.state).support :=
        boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
          G iface hsound horizon htail
      change
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
            step.dst steps).state ∈
          ((G.toMachine iface).runEventBlocksFrom
            ([block] ++
              boundedFOSGStepEventBlocks G iface hsound horizon steps)
            step.src.state).support
      rw [Machine.runEventBlocksFrom_append]
      rw [PMF.mem_support_bind_iff]
      exact ⟨step.dst.state, hblock, htailSupport⟩

/-- Every realized bounded graph-FOSG history extracts a primitive machine
blocked trace whose endpoint support contains the history's checkpoint state. -/
theorem boundedFOSGHistory_state_mem_runEventBlocksFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((G.toMachine iface).runEventBlocksFrom
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h)
        (G.toMachine iface).init).support := by
  simpa [boundedFOSGHistoryEventBlocks,
    boundedFOSGStepEventBlocks, GameTheory.FOSG.History.lastState,
    EventGraph.toMachine_init] using
    (boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
      G iface hsound horizon h.chain)

/-- One bounded graph-FOSG transition, projected to the history's extracted
event-block prefix and the successor checkpoint state, is exactly the
corresponding primitive machine blocked run. -/
theorem boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            dst.state))
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            next))
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state) := by
  let attach : (G.toMachine iface).State →
      List (List (G.toMachine iface).Event) × (G.toMachine iface).State :=
    fun next =>
      (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
          [roundPrimitiveEvents G iface h.lastState.state action.1],
        next)
  have hstate :=
    toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon) (state := h.lastState) (action := action)
  change
    PMF.map (fun dst => attach dst.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map attach
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state)
  rw [← hstate]
  rw [PMF.map_comp]
  rfl

/-- Binding a continuation over one bounded graph-FOSG transition is the same
as binding that continuation over the corresponding primitive machine blocked
run, with the bounded presentation depth reattached to the checkpoint state. -/
theorem boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        h.lastState))
    {α : Type}
    (K : (G.toMachine iface).BoundedState horizon → PMF α) :
    ((((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action).bind K) =
      ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind
        (fun next =>
          K (h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next)) := by
  rw [Machine.FOSGView.toBoundedFOSG_transition]
  change
    (PMF.map
        (fun next =>
          h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next)
        (roundTransition G h.lastState.state action.1)).bind K =
      ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind
        (fun next =>
          K (h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next))
  rw [PMF.bind_map]
  rw [roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    (G := G) (iface := iface) (cfg := h.lastState.state)
    (joint := action.1)]
  rw [Machine.runEventBlocksFrom_singleton]
  rfl

/-- History-dependent blocked primitive trace distribution induced by a
bounded graph-FOSG behavioral profile.

The state of this process is still the FOSG history: strategies are allowed to
depend on information-state history.  The machine contribution at each
nonterminal FOSG round is the primitive event block selected by that round. -/
noncomputable def boundedFOSGBlockTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)) :
    Nat →
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History) →
        PMF (List (List (G.toMachine iface).Event) × (G.toMachine iface).State)
  | 0, h =>
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
          h.lastState.state)
  | n + 1, h => by
      classical
      exact
        if hterm :
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
              h.lastState then
          PMF.pure
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
              h.lastState.state)
        else
          (GameTheory.FOSG.legalActionLaw
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon)
            σ h hterm).bind fun action =>
            ((G.toMachine iface).runEventBlocksFrom
              [roundPrimitiveEvents G iface h.lastState.state action.1]
              h.lastState.state).bind fun next =>
                boundedFOSGBlockTraceDistFrom
                  G iface hsound horizon σ n
                  (h.extendByOutcome action
                    (h.lastState.succ
                      (Nat.lt_of_not_ge
                        (fun hle => action.2.1 (Or.inr hle)))
                      next))

@[simp] theorem boundedFOSGBlockTraceDistFrom_zero
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    boundedFOSGBlockTraceDistFrom G iface hsound horizon σ 0 h =
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
          h.lastState.state) := rfl

theorem boundedFOSGBlockTraceDistFrom_succ_terminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (hterm :
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
        h.lastState) :
    boundedFOSGBlockTraceDistFrom G iface hsound horizon σ (n + 1) h =
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
          h.lastState.state) := by
  have hterm' :
      (G.toFOSGView iface hsound).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGBlockTraceDistFrom, hterm']

theorem boundedFOSGBlockTraceDistFrom_succ_nonterminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (hterm :
      ¬ ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
        h.lastState) :
    boundedFOSGBlockTraceDistFrom G iface hsound horizon σ (n + 1) h =
      (GameTheory.FOSG.legalActionLaw
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)
        σ h hterm).bind fun action =>
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind fun next =>
            boundedFOSGBlockTraceDistFrom
              G iface hsound horizon σ n
              (h.extendByOutcome action
                (h.lastState.succ
                  (Nat.lt_of_not_ge
                    (fun hle => action.2.1 (Or.inr hle)))
                  next)) := by
  have hterm' :
      ¬ (G.toFOSGView iface hsound).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGBlockTraceDistFrom, hterm']

/-- Bounded graph-FOSG execution, projected to extracted primitive event blocks
and checkpoint state, equals the history-dependent blocked machine trace
distribution induced by the same behavioral profile. -/
theorem boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)) :
    ∀ (n : Nat)
      (h :
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)),
      PMF.map
          (fun h' =>
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
              h'.lastState.state))
          (GameTheory.FOSG.History.runDistFrom
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h) =
        boundedFOSGBlockTraceDistFrom G iface hsound horizon σ n h
  | 0, h => by
      rw [GameTheory.FOSG.History.runDistFrom_zero]
      rw [boundedFOSGBlockTraceDistFrom_zero]
      rw [PMF.pure_map]
  | n + 1, h => by
      let BFOSG := (G.toFOSGView iface hsound).toBoundedFOSG horizon
      by_cases hterm : BFOSG.terminal h.lastState
      · rw [GameTheory.FOSG.History.runDistFrom_succ_terminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGBlockTraceDistFrom_succ_terminal
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) σ n h hterm]
        rw [PMF.pure_map]
      · rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGBlockTraceDistFrom_succ_nonterminal
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) σ n h hterm]
        rw [PMF.map_bind]
        congr
        funext action
        rw [PMF.map_bind]
        conv_lhs =>
          arg 2
          intro dst
          rw [boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
            G iface hsound horizon σ n (h.extendByOutcome action dst)]
        exact
          boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
            G iface hsound horizon h action
            (fun dst =>
              boundedFOSGBlockTraceDistFrom
                G iface hsound horizon σ n
                (h.extendByOutcome action dst))

/-- Outcome projection of bounded graph-FOSG execution equals outcome
projection of the corresponding history-dependent blocked machine trace
distribution. -/
theorem boundedFOSG_runDistFrom_map_outcome_eq_blockTraceDistFrom_map_outcome
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    PMF.map
        (fun h' => (G.toMachine iface).outcome h'.lastState.state)
        (GameTheory.FOSG.History.runDistFrom
          ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h) =
      PMF.map
        (fun trace => (G.toMachine iface).outcome trace.2)
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon σ n h) := by
  let project :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History) →
        List (List (G.toMachine iface).Event) × (G.toMachine iface).State :=
    fun h' =>
      (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
        h'.lastState.state)
  let observe :
      List (List (G.toMachine iface).Event) × (G.toMachine iface).State →
        (G.toMachine iface).Outcome :=
    fun trace => (G.toMachine iface).outcome trace.2
  calc
    PMF.map
        (fun h' => (G.toMachine iface).outcome h'.lastState.state)
        (GameTheory.FOSG.History.runDistFrom
          ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h)
        =
      PMF.map observe
        (PMF.map project
          (GameTheory.FOSG.History.runDistFrom
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h)) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map observe
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon σ n h) := by
          rw [boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
            (G := G) (iface := iface) (hsound := hsound)
            (horizon := horizon) σ n h]

/-- Public bounded behavioral outcome kernel of a graph-FOSG view, computed as
the machine outcome map of the induced blocked primitive trace distribution. -/
theorem boundedFOSG_outcomeFromBehavioral_eq_blockTraceDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (β :
      ((G.toFOSGView iface hsound).BoundedBehavioralProfile horizon))
    (steps : Nat) :
    ((G.toFOSGView iface hsound).boundedOutcomeFromBehavioral
        horizon β steps) =
      PMF.map
        (fun trace => (G.toMachine iface).outcome trace.2)
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon β.extend steps
          (GameTheory.FOSG.History.nil
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon))) := by
  simpa [Machine.FOSGView.boundedOutcomeFromBehavioral,
    Machine.FOSGView.boundedHistoryOutcome, GameTheory.FOSG.runDist] using
    (boundedFOSG_runDistFrom_map_outcome_eq_blockTraceDistFrom_map_outcome
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon) β.extend steps
      (GameTheory.FOSG.History.nil
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)))

/-- Public bounded pure outcome kernel of a graph-FOSG view, computed as the
machine outcome map of the blocked primitive trace distribution induced by the
pure profile's behavioral embedding. -/
theorem boundedFOSG_outcomeFromPure_eq_blockTraceDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (π :
      ((G.toFOSGView iface hsound).BoundedPureProfile horizon))
    (steps : Nat) :
    ((G.toFOSGView iface hsound).boundedOutcomeFromPure
        horizon π steps) =
      PMF.map
        (fun trace => (G.toMachine iface).outcome trace.2)
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon
          (GameTheory.FOSG.legalPureToBehavioral
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) π.extend)
          steps
          (GameTheory.FOSG.History.nil
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon))) := by
  simpa [Machine.FOSGView.boundedOutcomeFromPure,
    Machine.FOSGView.boundedHistoryOutcome, GameTheory.FOSG.runDist] using
    (boundedFOSG_runDistFrom_map_outcome_eq_blockTraceDistFrom_map_outcome
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon)
      (GameTheory.FOSG.legalPureToBehavioral
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon) π.extend)
      steps
      (GameTheory.FOSG.History.nil
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)))

/-- One-step form matching `FOSG.History.runDistFrom`: if the sampled bounded
destination extends the FOSG history, then the extracted block prefix and
checkpoint state have the same distribution as the primitive machine blocked
run for the selected frontier round. -/
theorem boundedFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          let h' := h.extendByOutcome action dst
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
            h'.lastState.state))
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            next))
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state) := by
  let transition :=
    (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
      h.lastState action)
  have hproject :
      PMF.map
          (fun dst =>
            let h' := h.extendByOutcome action dst
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
              h'.lastState.state))
          transition =
        PMF.map
          (fun dst =>
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
                [roundPrimitiveEvents G iface h.lastState.state action.1],
              dst.state))
          transition := by
    change
      transition.bind
          (fun dst =>
            PMF.pure
              (let h' := h.extendByOutcome action dst
              (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
                h'.lastState.state))) =
        transition.bind
          (fun dst =>
            PMF.pure
              (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
                  [roundPrimitiveEvents G iface h.lastState.state action.1],
                dst.state))
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      transition _ _ ?_
    intro dst hdst
    have hsuppLocal : transition dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdst
    have hsupp :
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) dst ≠ 0 := by
      simpa [transition] using hsuppLocal
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := h) (a := action) (dst := dst) hsupp]
    simp [boundedFOSGHistoryEventBlocks, boundedFOSGStepEventBlocks]
  rw [hproject]
  exact
    boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
      G iface hsound horizon h action

end EventGraph

end Vegas
