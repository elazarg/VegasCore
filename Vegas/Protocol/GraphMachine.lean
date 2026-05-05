import Vegas.Protocol.Machine

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

/-- Static player action alphabet for a protocol graph: choose a graph node
and a result slice for that node. State-local availability restricts this to
ready nodes owned by the player and legal slices for the current result
assignment. -/
structure PlayerAction (G : Vegas.ProtocolGraph Player L) (_who : Player) where
  node : G.Node
  slice : G.WriteSlice

/-- Internal graph events execute ready non-player nodes. The result slice is
sampled by `G.internalKernel`. -/
structure InternalEvent (G : Vegas.ProtocolGraph Player L) where
  node : G.Node

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
      event.node ∈ cfg.frontier ∧
        (G.sem event.node).actor = none }

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
    if h : event ∈ availableInternal G cfg then
      (G.internalKernel event.node cfg.result).bind fun slice =>
        if hlegal : G.sliceLegal event.node slice then
          PMF.pure (cfg.withResult slice h.1 hlegal)
        else
          PMF.pure cfg
    else
      PMF.pure cfg

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

end ProtocolGraph

end Vegas
