import Vegas.Protocol.FOSG

/-!
# Protocol graph machines

This module interprets an extensional `ProtocolGraph.Configuration` as the
generic asynchronous `Machine` carrier.

The primitive machine step executes one ready graph node.  A frontier is the
set of schedulable nodes; it is not resolved as a batch and it is not stored in
the state.
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

/-- Internal graph events execute ready non-player nodes. `idle` is never
available; it only gives terminal FOSG presentations a total internal turn
without inventing an executable graph node. -/
inductive InternalEvent (G : Vegas.ProtocolGraph Player L) where
  | node (node : G.Node)
  | idle

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

/-- Pick one frontier node when the frontier is nonempty. -/
noncomputable def selectedFrontierNode?
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration) :
    Option G.Node := by
  classical
  exact
    if h : cfg.frontier.Nonempty then
      some h.choose
    else
      none

theorem selectedFrontierNode?_eq_some_mem
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration)
    {node : G.Node}
    (hselect : selectedFrontierNode? G cfg = some node) :
    node ∈ cfg.frontier := by
  classical
  unfold selectedFrontierNode? at hselect
  split at hselect
  · rename_i hnonempty
    cases hselect
    exact hnonempty.choose_spec
  · simp at hselect

theorem selectedFrontierNode?_some_of_not_terminal
    (G : Vegas.ProtocolGraph Player L) (cfg : G.Configuration)
    (hterminal : ¬ cfg.terminal) :
    ∃ node, selectedFrontierNode? G cfg = some node ∧
      node ∈ cfg.frontier := by
  classical
  have hnonempty : cfg.frontier.Nonempty :=
    cfg.frontier_nonempty_of_not_terminal hterminal
  refine ⟨hnonempty.choose, ?_, hnonempty.choose_spec⟩
  unfold selectedFrontierNode?
  simp [hnonempty]

/-- Canonical selected turn for a protocol-graph configuration. -/
noncomputable def turn
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration) :
    (G.toMachine iface).Turn :=
  match selectedFrontierNode? G cfg with
  | some node =>
      match (G.sem node).actor with
      | some who => .play who
      | none => .internal (.node node)
  | none => .internal .idle

/-- FOSG presentation of a protocol-graph machine, assuming player-owned
frontier nodes are never action-deadlocked. -/
noncomputable def toFOSGView
    (G : Vegas.ProtocolGraph Player L) (iface : MachineInterface G)
    (hplayer : G.HasAvailablePlayerActions) :
    (G.toMachine iface).FOSGView where
  turn := fun pref => turn G iface pref.lastState
  terminal_not_play := by
    intro pref player hterminal hplay
    unfold turn at hplay
    cases hselect : selectedFrontierNode? G pref.lastState with
    | none =>
        simp [hselect] at hplay
    | some node =>
        have hfrontier :=
          selectedFrontierNode?_eq_some_mem G pref.lastState hselect
        cases hactor : (G.sem node).actor with
        | none =>
            rw [hselect] at hplay
            simp [hactor] at hplay
        | some who =>
            rw [hselect] at hplay
            simp [hactor] at hplay
            exact (pref.lastState.not_terminal_of_mem_frontier hfrontier)
              hterminal
  turn_available := by
    intro pref hterminal
    rcases selectedFrontierNode?_some_of_not_terminal G pref.lastState
        hterminal with ⟨node, hselect, hfrontier⟩
    unfold turn
    rw [hselect]
    cases hactor : (G.sem node).actor with
    | none =>
        simpa [hactor, Machine.Turn.AvailableAt, toMachine] using
          (show (InternalEvent.node node : InternalEvent G) ∈
            availableInternal G pref.lastState from ⟨hfrontier, hactor⟩)
    | some who =>
        rcases hplayer pref.lastState hfrontier hactor with
          ⟨slice, hslice, haction⟩
        simpa [hactor, Machine.Turn.AvailableAt, toMachine] using
          (show ∃ action : PlayerAction G who,
              action ∈ available G pref.lastState who from
            ⟨⟨node, slice⟩, hfrontier, hactor, hslice, haction⟩)
  reward := fun _ _ dst who =>
    iface.utility (iface.outcome dst.lastState) who

end ProtocolGraph

end Vegas
