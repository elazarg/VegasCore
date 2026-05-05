import Vegas.Protocol.FOSG

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

end ProtocolGraph

end Vegas
