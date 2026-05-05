import Vegas.Protocol.FOSG
import Vegas.Protocol.Trace

/-!
# Protocol graph machines

This module interprets an extensional `ProtocolGraph.Configuration` as the
generic asynchronous `Machine` carrier.

The primitive machine step executes one ready graph node.  The FOSG
presentation below exposes whole frontier rounds: it batches the current
frontier into one player-facing transition while the primitive machine remains
the executable carrier.
-/

namespace Vegas

namespace ProtocolGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] ProtocolGraph.nodeDecEq
attribute [local instance] ProtocolGraph.fieldDecEq

/-- Player-owned frontier nodes have at least one legal concrete action. -/
def HasAvailablePlayerActions (G : Vegas.ProtocolGraph Player L) : Prop :=
  ∀ (cfg : G.Configuration) {node : G.Node} {who : Player},
    node ∈ cfg.frontier →
    (G.sem node).actor = some who →
      ∃ slice, G.sliceLegal node slice ∧
        G.actionLegal cfg.result node slice

/-- Static player action alphabet for a protocol graph: choose a graph node
and a result slice for that node. State-local availability restricts this to
ready nodes owned by the player and legal slices for the current result
assignment. -/
structure PlayerAction (G : Vegas.ProtocolGraph Player L) (_who : Player) where
  node : G.Node
  slice : G.WriteSlice

namespace PlayerAction

/-- Player actions are finite when graph nodes, fields, and field values are
finite. -/
@[reducible] noncomputable instance instFintype
    (G : Vegas.ProtocolGraph Player L) (who : Player)
    [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype (PlayerAction G who) := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (StoredValue (L.Val (G.fieldTy field)))) :=
    fun _ => inferInstance
  letI : Fintype G.WriteSlice := by
    dsimp [ProtocolGraph.WriteSlice]
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
write slice for each graph node; state-local availability uses only the slices
for frontier nodes owned by the player. -/
structure PlayerRoundAction (G : Vegas.ProtocolGraph Player L) (_who : Player) where
  slice : G.Node → G.WriteSlice

namespace PlayerRoundAction

@[reducible] noncomputable instance instFintype
    (G : Vegas.ProtocolGraph Player L) (who : Player)
    [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype (PlayerRoundAction G who) := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (StoredValue (L.Val (G.fieldTy field)))) :=
    fun _ => inferInstance
  letI : Fintype G.WriteSlice := by
    dsimp [ProtocolGraph.WriteSlice]
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

/-- Internal graph events execute ready non-player nodes. `idle` is never
available; it only gives terminal FOSG presentations a total internal turn
without inventing an executable graph node. -/
inductive InternalEvent (G : Vegas.ProtocolGraph Player L) where
  | node (node : G.Node)
  | idle

namespace InternalEvent

/-- Internal graph events are finite when graph nodes are finite. -/
@[reducible] noncomputable instance instFintype
    (G : Vegas.ProtocolGraph Player L) [Fintype G.Node] :
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

Execution is graph-native; this structure only says how completed graph state
is observed and scored. -/
structure MachineInterface (G : Vegas.ProtocolGraph Player L) where
  Public : Type
  Obs : Player → Type
  Outcome : Type
  publicView : G.Configuration → Public
  observe : (who : Player) → G.Configuration → Obs who
  outcome : G.Configuration → Outcome
  utility : Outcome → Payoff Player

/-- Player actions available at a graph configuration. -/
def available
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (PlayerAction G who) :=
  { action |
      action.node ∈ cfg.frontier ∧
        (G.sem action.node).actor = some who ∧
          G.sliceLegal action.node action.slice ∧
            G.actionLegal cfg.result action.node action.slice }

/-- Internal events available at a graph configuration. -/
def availableInternal
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration) :
    Set (InternalEvent G) :=
  { event |
      match event with
      | .node node =>
          node ∈ cfg.frontier ∧
            (G.sem node).actor = none
      | .idle => False }

/-- Execute one available player node. Unavailable events stutter, matching the
total-step convention of `Machine`. -/
noncomputable def stepPlay
    (G : Vegas.ProtocolGraph Player L) (who : Player)
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
    (G : Vegas.ProtocolGraph Player L) (event : InternalEvent G)
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

/-- Canonical asynchronous machine for a protocol graph. -/
noncomputable def toMachine
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G) :
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G) :
    (G.toMachine iface).init = Configuration.initial G := rfl

@[simp] theorem toMachine_terminal
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (cfg : (G.toMachine iface).State) :
    (G.toMachine iface).terminal cfg = cfg.terminal := rfl

/-- Players who own at least one node in the current frontier. -/
noncomputable def roundActive
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration) :
    Finset Player := by
  classical
  exact cfg.frontier.biUnion fun node =>
    match (G.sem node).actor with
    | some who => {who}
    | none => ∅

theorem mem_roundActive_iff
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration)
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
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (PlayerRoundAction G who) :=
  { action |
      ∀ {node},
        node ∈ cfg.frontier →
        (G.sem node).actor = some who →
          G.sliceLegal node (action.slice node) ∧
            G.actionLegal cfg.result node (action.slice node) }

/-- Execute one node from a frontier round using the joint round action.
Unavailable primitive events stutter through the underlying total machine step;
frontier soundness lemmas show the intended round nodes remain available across
linearizations. -/
noncomputable def roundStepNode
    (G : Vegas.ProtocolGraph Player L)
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

/-- Primitive machine event selected for one graph node by a frontier-round
joint action. Missing player coordinates are represented by the graph machine's
unavailable `idle` internal event, whose total step stutters. Legal round
actions never need this fallback for current frontier nodes. -/
noncomputable def roundPrimitiveEvent
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
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

/-- The primitive machine event list represented by one frontier round. The
order is the canonical `Finset.toList` order used by `roundTransition`; order
invariance is a separate theorem about independent frontier nodes. -/
noncomputable def roundPrimitiveEvents
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    List (G.toMachine iface).Event :=
  cfg.frontier.toList.map (roundPrimitiveEvent G iface joint)

/-- Every primitive event listed for a legal frontier round is available at the
round's source configuration. Availability after earlier events in a
linearization is the separate frontier-stability theorem. -/
theorem mem_roundPrimitiveEvents_available_of_legal
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
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
definition device only; the frontier commutation theorems are the semantic
justification that this hides no scheduler-relevant order. -/
noncomputable def roundTransition
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF G.Configuration :=
  cfg.frontier.toList.foldl
    (fun acc node => acc.bind fun state => roundStepNode G joint node state)
    (PMF.pure cfg)

/-- A graph frontier round is exactly the primitive machine run obtained by
executing the round's canonical frontier event list. -/
theorem roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
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

/-- FOSG presentation of a protocol-graph machine by frontier rounds, assuming
player-owned frontier nodes are never action-deadlocked. -/
noncomputable def toFOSGView
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) :
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
        Classical.choose (hplayer cfg h.1 h.2)
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
        exact Classical.choose_spec (hplayer cfg h.1 h.2)
      · rename_i h
        exact False.elim (h hnode)
    · have hjoint : joint who = none := by
        simp [joint, hactive]
      rw [hjoint]
      exact hactive

/-- One bounded graph-FOSG transition, projected back to graph configurations,
is the primitive machine run of the round's canonical frontier event list. -/
theorem toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventsFrom
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    (steps :
      List (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).Step)) :
    List (List (G.toMachine iface).Event) :=
  steps.map fun step =>
    roundPrimitiveEvents G iface step.src.state step.act.1

/-- Primitive event blocks extracted from a bounded graph-FOSG history. -/
noncomputable def boundedFOSGHistoryEventBlocks
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History)) :
    List (List (G.toMachine iface).Event) :=
  boundedFOSGStepEventBlocks G iface hplayer horizon h.steps

/-- Every realized bounded graph-FOSG step chain is backed by a primitive
machine blocked run whose support contains the same checkpoint endpoint. -/
theorem boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps :
        List (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).Step)},
      ((G.toFOSGView iface hplayer).toBoundedFOSG horizon).StepChainFrom
          start steps →
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).lastStateFrom
            start steps).state ∈
          ((G.toMachine iface).runEventBlocksFrom
            (boundedFOSGStepEventBlocks G iface hplayer horizon steps)
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
                (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
                  step.src step.act)).support := by
          exact (PMF.mem_support_map_iff _ _ _).2
            ⟨step.dst, (PMF.mem_support_iff _ _).2 step.support, rfl⟩
        rw [toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
          (G := G) (iface := iface) (hplayer := hplayer)
          (horizon := horizon) (state := step.src) (action := step.act)] at hmap
        simpa [block] using hmap
      have htailSupport :
          (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).lastStateFrom
              step.dst steps).state ∈
            ((G.toMachine iface).runEventBlocksFrom
              (boundedFOSGStepEventBlocks G iface hplayer horizon steps)
              step.dst.state).support :=
        boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
          G iface hplayer horizon htail
      change
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).lastStateFrom
            step.dst steps).state ∈
          ((G.toMachine iface).runEventBlocksFrom
            ([block] ++
              boundedFOSGStepEventBlocks G iface hplayer horizon steps)
            step.src.state).support
      rw [Machine.runEventBlocksFrom_append]
      rw [PMF.mem_support_bind_iff]
      exact ⟨step.dst.state, hblock, htailSupport⟩

/-- Every realized bounded graph-FOSG history extracts a primitive machine
blocked trace whose endpoint support contains the history's checkpoint state. -/
theorem boundedFOSGHistory_state_mem_runEventBlocksFrom_support
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((G.toMachine iface).runEventBlocksFrom
        (boundedFOSGHistoryEventBlocks G iface hplayer horizon h)
        (G.toMachine iface).init).support := by
  simpa [boundedFOSGHistoryEventBlocks,
    boundedFOSGStepEventBlocks, GameTheory.FOSG.History.lastState,
    ProtocolGraph.toMachine_init] using
    (boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
      G iface hplayer horizon h.chain)

/-- One bounded graph-FOSG transition, projected to the history's extracted
event-block prefix and the successor checkpoint state, is exactly the
corresponding primitive machine blocked run. -/
theorem boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          (boundedFOSGHistoryEventBlocks G iface hplayer horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            dst.state))
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (boundedFOSGHistoryEventBlocks G iface hplayer horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            next))
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state) := by
  let attach : (G.toMachine iface).State →
      List (List (G.toMachine iface).Event) × (G.toMachine iface).State :=
    fun next =>
      (boundedFOSGHistoryEventBlocks G iface hplayer horizon h ++
          [roundPrimitiveEvents G iface h.lastState.state action.1],
        next)
  have hstate :=
    toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
      (G := G) (iface := iface) (hplayer := hplayer)
      (horizon := horizon) (state := h.lastState) (action := action)
  change
    PMF.map (fun dst => attach dst.state)
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).LegalAction
        h.lastState))
    {α : Type}
    (K : (G.toMachine iface).BoundedState horizon → PMF α) :
    ((((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
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
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hplayer).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hplayer).toBoundedFOSG horizon)) :
    Nat →
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History) →
        PMF (List (List (G.toMachine iface).Event) × (G.toMachine iface).State)
  | 0, h =>
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hplayer horizon h,
          h.lastState.state)
  | n + 1, h => by
      classical
      exact
        if hterm :
            ((G.toFOSGView iface hplayer).toBoundedFOSG horizon).terminal
              h.lastState then
          PMF.pure
            (boundedFOSGHistoryEventBlocks G iface hplayer horizon h,
              h.lastState.state)
        else
          (GameTheory.FOSG.legalActionLaw
            ((G.toFOSGView iface hplayer).toBoundedFOSG horizon)
            σ h hterm).bind fun action =>
            ((G.toMachine iface).runEventBlocksFrom
              [roundPrimitiveEvents G iface h.lastState.state action.1]
              h.lastState.state).bind fun next =>
                boundedFOSGBlockTraceDistFrom
                  G iface hplayer horizon σ n
                  (h.extendByOutcome action
                    (h.lastState.succ
                      (Nat.lt_of_not_ge
                        (fun hle => action.2.1 (Or.inr hle)))
                      next))

@[simp] theorem boundedFOSGBlockTraceDistFrom_zero
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hplayer).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hplayer).toBoundedFOSG horizon))
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History)) :
    boundedFOSGBlockTraceDistFrom G iface hplayer horizon σ 0 h =
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hplayer horizon h,
          h.lastState.state) := rfl

theorem boundedFOSGBlockTraceDistFrom_succ_terminal
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hplayer).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hplayer).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History))
    (hterm :
      ((G.toFOSGView iface hplayer).toBoundedFOSG horizon).terminal
        h.lastState) :
    boundedFOSGBlockTraceDistFrom G iface hplayer horizon σ (n + 1) h =
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hplayer horizon h,
          h.lastState.state) := by
  have hterm' :
      (G.toFOSGView iface hplayer).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGBlockTraceDistFrom, hterm']

theorem boundedFOSGBlockTraceDistFrom_succ_nonterminal
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hplayer).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hplayer).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History))
    (hterm :
      ¬ ((G.toFOSGView iface hplayer).toBoundedFOSG horizon).terminal
        h.lastState) :
    boundedFOSGBlockTraceDistFrom G iface hplayer horizon σ (n + 1) h =
      (GameTheory.FOSG.legalActionLaw
        ((G.toFOSGView iface hplayer).toBoundedFOSG horizon)
        σ h hterm).bind fun action =>
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind fun next =>
            boundedFOSGBlockTraceDistFrom
              G iface hplayer horizon σ n
              (h.extendByOutcome action
                (h.lastState.succ
                  (Nat.lt_of_not_ge
                    (fun hle => action.2.1 (Or.inr hle)))
                  next)) := by
  have hterm' :
      ¬ (G.toFOSGView iface hplayer).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGBlockTraceDistFrom, hterm']

/-- Bounded graph-FOSG execution, projected to extracted primitive event blocks
and checkpoint state, equals the history-dependent blocked machine trace
distribution induced by the same behavioral profile. -/
theorem boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hplayer).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).terminal)]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hplayer).toBoundedFOSG horizon)) :
    ∀ (n : Nat)
      (h :
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History)),
      PMF.map
          (fun h' =>
            (boundedFOSGHistoryEventBlocks G iface hplayer horizon h',
              h'.lastState.state))
          (GameTheory.FOSG.History.runDistFrom
            ((G.toFOSGView iface hplayer).toBoundedFOSG horizon) σ n h) =
        boundedFOSGBlockTraceDistFrom G iface hplayer horizon σ n h
  | 0, h => by
      rw [GameTheory.FOSG.History.runDistFrom_zero]
      rw [boundedFOSGBlockTraceDistFrom_zero]
      rw [PMF.pure_map]
  | n + 1, h => by
      let BFOSG := (G.toFOSGView iface hplayer).toBoundedFOSG horizon
      by_cases hterm : BFOSG.terminal h.lastState
      · rw [GameTheory.FOSG.History.runDistFrom_succ_terminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGBlockTraceDistFrom_succ_terminal
          (G := G) (iface := iface) (hplayer := hplayer)
          (horizon := horizon) σ n h hterm]
        rw [PMF.pure_map]
      · rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGBlockTraceDistFrom_succ_nonterminal
          (G := G) (iface := iface) (hplayer := hplayer)
          (horizon := horizon) σ n h hterm]
        rw [PMF.map_bind]
        congr
        funext action
        rw [PMF.map_bind]
        conv_lhs =>
          arg 2
          intro dst
          rw [boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
            G iface hplayer horizon σ n (h.extendByOutcome action dst)]
        exact
          boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
            G iface hplayer horizon h action
            (fun dst =>
              boundedFOSGBlockTraceDistFrom
                G iface hplayer horizon σ n
                (h.extendByOutcome action dst))

/-- One-step form matching `FOSG.History.runDistFrom`: if the sampled bounded
destination extends the FOSG history, then the extracted block prefix and
checkpoint state have the same distribution as the primitive machine blocked
run for the selected frontier round. -/
theorem boundedFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          let h' := h.extendByOutcome action dst
          (boundedFOSGHistoryEventBlocks G iface hplayer horizon h',
            h'.lastState.state))
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (boundedFOSGHistoryEventBlocks G iface hplayer horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            next))
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state) := by
  let transition :=
    (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
      h.lastState action)
  have hproject :
      PMF.map
          (fun dst =>
            let h' := h.extendByOutcome action dst
            (boundedFOSGHistoryEventBlocks G iface hplayer horizon h',
              h'.lastState.state))
          transition =
        PMF.map
          (fun dst =>
            (boundedFOSGHistoryEventBlocks G iface hplayer horizon h ++
                [roundPrimitiveEvents G iface h.lastState.state action.1],
              dst.state))
          transition := by
    change
      transition.bind
          (fun dst =>
            PMF.pure
              (let h' := h.extendByOutcome action dst
              (boundedFOSGHistoryEventBlocks G iface hplayer horizon h',
                h'.lastState.state))) =
        transition.bind
          (fun dst =>
            PMF.pure
              (boundedFOSGHistoryEventBlocks G iface hplayer horizon h ++
                  [roundPrimitiveEvents G iface h.lastState.state action.1],
                dst.state))
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      transition _ _ ?_
    intro dst hdst
    have hsuppLocal : transition dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdst
    have hsupp :
        (((G.toFOSGView iface hplayer).toBoundedFOSG horizon).transition
          h.lastState action) dst ≠ 0 := by
      simpa [transition] using hsuppLocal
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := h) (a := action) (dst := dst) hsupp]
    simp [boundedFOSGHistoryEventBlocks, boundedFOSGStepEventBlocks]
  rw [hproject]
  exact
    boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
      G iface hplayer horizon h action

end ProtocolGraph

end Vegas
