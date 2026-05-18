import Vegas.EventGraph.Basic
import Vegas.Machine.Basic
import Vegas.Machine.Trace

/-!
# Event graph machine interpretation

This module interprets an extensional `EventGraph.Configuration` as the generic
asynchronous `Machine` carrier. Frontier-round game-form views live in
`Vegas.GameBridge.FOSG.FromEventGraph`.
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
      ∃ patch, G.patchLegal node patch ∧
        G.actionLegal cfg.result node patch

/-- Static player action alphabet for an event graph: choose an event node
and a field patch for that node. State-local availability restricts this to
enabled nodes owned by the player and legal patches for the current result
assignment. -/
structure PlayerAction (G : Vegas.EventGraph Player L) (_who : Player) where
  node : G.Node
  patch : G.FieldPatch

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
      Fintype (Option (L.Val (G.fieldTy field))) :=
    fun _ => inferInstance
  letI : Fintype G.FieldPatch := by
    dsimp [EventGraph.FieldPatch]
    infer_instance
  let e : PlayerAction G who ≃ G.Node × G.FieldPatch :=
    { toFun := fun action => (action.node, action.patch)
      invFun := fun pair => { node := pair.1, patch := pair.2 }
      left_inv := by
        intro action
        cases action
        rfl
      right_inv := by
        intro pair
        cases pair
        rfl }
  exact Fintype.ofEquiv (G.Node × G.FieldPatch) e.symm

end PlayerAction

/-- Internal events execute enabled non-player nodes. `idle` is never
available; it only gives terminal FOSG presentations a total internal turn
without inventing an executable event node. -/
inductive InternalEvent (G : Vegas.EventGraph Player L) where
  | node (node : G.Node) (patch : G.FieldPatch)
  | idle

namespace InternalEvent

/-- Internal events are finite when event nodes and field patches are finite. -/
@[reducible] noncomputable instance instFintype
    (G : Vegas.EventGraph Player L) [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype (InternalEvent G) := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (L.Val (G.fieldTy field))) :=
    fun _ => inferInstance
  letI : Fintype G.FieldPatch := by
    dsimp [EventGraph.FieldPatch]
    infer_instance
  letI : DecidableEq (InternalEvent G) := Classical.decEq _
  refine Fintype.mk
    (((Finset.univ : Finset (G.Node × G.FieldPatch)).image
        (fun pair => InternalEvent.node pair.1 pair.2)) ∪
      {InternalEvent.idle}) ?_
  intro event
  cases event with
  | node node patch =>
      exact Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_image.mpr
            ⟨(node, patch), Finset.mem_univ _, rfl⟩))
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
          G.patchLegal action.node action.patch ∧
            G.actionLegal cfg.result action.node action.patch }

/-- Internal events available at a graph configuration. -/
def availableInternal
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration) :
    Set (InternalEvent G) :=
  { event |
      match event with
      | .node node patch =>
          node ∈ cfg.frontier ∧
            (G.sem node).actor = none ∧
              patch ∈ (G.internalKernel node cfg.result).support
      | .idle => False }

/-- Locality condition for exposing graph frontiers as strategic steps.

The progress field prevents player-owned frontier nodes from deadlocking. The
stability fields are the proof-facing form of graph locality: one source-frontier
node cannot change player legality or internal chance for a distinct
source-frontier node. -/
structure HasLocalFrontierSteps (G : Vegas.EventGraph Player L) : Prop where
  availablePlayerActions : G.HasAvailablePlayerActions
  actionStable :
    ∀ (cfg : G.Configuration)
      {first : G.Node} {firstPatch : G.FieldPatch}
      (hfirst : first ∈ cfg.frontier)
      {who : Player} {action : PlayerAction G who}
      (_ : action.node ∈ cfg.frontier)
      (_ : action.node ≠ first)
      (hfirstLegal : G.patchLegal first firstPatch),
      action ∈ available G cfg who →
        action ∈ available G
          (cfg.withPatch firstPatch hfirst hfirstLegal) who
  internalKernelStable :
    ∀ (cfg : G.Configuration)
      {first second : G.Node} {firstPatch : G.FieldPatch}
      (hfirst : first ∈ cfg.frontier)
      (_ : second ∈ cfg.frontier)
      (_ : second ≠ first)
      (hfirstLegal : G.patchLegal first firstPatch),
      G.internalKernel second
          ((cfg.withPatch firstPatch hfirst hfirstLegal).result) =
        G.internalKernel second cfg.result

/-- Execute one available player node. Unavailable events stutter, matching the
total-step convention of `Machine`. -/
noncomputable def stepPlay
    (G : Vegas.EventGraph Player L) (who : Player)
    (action : PlayerAction G who) (cfg : G.Configuration) :
    PMF G.Configuration := by
  classical
  exact
    if h : action ∈ available G cfg who then
      PMF.pure (cfg.withPatch action.patch h.1 h.2.2.1)
    else
      PMF.pure cfg

/-- Execute one available internal node. The event carries the kernel-realized
field patch, so this primitive step is deterministic. -/
noncomputable def stepInternal
    (G : Vegas.EventGraph Player L) (event : InternalEvent G)
    (cfg : G.Configuration) : PMF G.Configuration := by
  classical
  exact
    match event with
    | .node node patch =>
        if h : (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G cfg then
          have hnode :
              node ∈ cfg.frontier ∧
                (G.sem node).actor = none ∧
                  patch ∈ (G.internalKernel node cfg.result).support := by
            simpa [availableInternal] using h
          have hlegal : G.patchLegal node patch :=
            G.internalKernel_support_legal
              (cfg.mem_nodes_of_mem_frontier hnode.1)
              (cfg.not_done_of_mem_frontier hnode.1)
              (fun prereq hpre =>
                cfg.result_some_of_prereq_of_mem_frontier hnode.1 hpre)
              (fun hresult => cfg.legal hresult)
              hnode.2.1 hnode.2.2
          PMF.pure (cfg.withPatch patch hnode.1 hlegal)
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


end EventGraph

end Vegas
