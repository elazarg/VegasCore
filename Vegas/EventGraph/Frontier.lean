import GameTheory.Core.JointAction
import Math.PMFProduct
import Vegas.EventGraph.ToMachine
import Vegas.Machine.Trace

/-!
# Event-graph frontier strategic bridge

Event graphs execute asynchronously: a primitive machine step fires one
frontier node. This module defines the strategic bridge that presents the
current frontier as one simultaneous player step, plus the primitive event-batch
witnesses that relate that presentation back to machine execution.

The current `RoundView` adapter uses a fixed player action type, so
`PlayerFrontierAction` is represented as a total node-to-patch function even
though only the active player-owned frontier slice is semantically used at a
state. The longer-term EventGraph strategic layer should replace this
coordinate-heavy carrier with policies over declared predecessor projections;
this file keeps the existing adapter honest by making availability and realized
event extraction depend only on the effective frontier slice.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Player-facing action for a frontier step.

This is a coordinate representation for the current `RoundView` adapter: the
action supplies a candidate field patch for every event node, but state-local
availability and realized primitive events use only patches for current
frontier nodes owned by the player. -/
structure PlayerFrontierAction (G : Vegas.EventGraph Player L) (_who : Player) where
  patch : G.Node → G.FieldPatch

namespace PlayerFrontierAction

@[reducible] noncomputable instance instFintype
    (G : Vegas.EventGraph Player L) (who : Player)
    [Fintype G.Node] [Fintype G.Field]
    [∀ field : G.Field, Fintype (L.Val (G.fieldTy field))] :
    Fintype (PlayerFrontierAction G who) := by
  classical
  letI : ∀ field : G.Field,
      Fintype (Option (L.Val (G.fieldTy field))) :=
    fun _ => inferInstance
  letI : Fintype G.FieldPatch := by
    dsimp [EventGraph.FieldPatch]
    infer_instance
  let e : PlayerFrontierAction G who ≃ (G.Node → G.FieldPatch) :=
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

end PlayerFrontierAction

/-- Players who own at least one node in the current frontier. -/
noncomputable def frontierActive
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration) :
    Finset Player := by
  classical
  exact cfg.frontier.biUnion fun node =>
    match (G.sem node).actor with
    | some who => {who}
    | none => ∅

theorem mem_frontierActive_iff
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) :
    who ∈ frontierActive G cfg ↔
      ∃ node, node ∈ cfg.frontier ∧ (G.sem node).actor = some who := by
  classical
  unfold frontierActive
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

/-- Frontier actions available to a player at a graph configuration. -/
def frontierAvailable
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (PlayerFrontierAction G who) :=
  { action |
      ∀ {node},
        node ∈ cfg.frontier →
        (G.sem node).actor = some who →
          G.patchLegal node (action.patch node) ∧
            G.actionLegal cfg.result node (action.patch node) }

/-- Player-facing optional menu for a frontier step.

The `none` move means the player is not called in this frontier step. A
`some action` move means the player is active and the frontier action is legal for
every current frontier node owned by that player. -/
def frontierMenu
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) : Set (Option (PlayerFrontierAction G who)) :=
  { move |
    match move with
    | none => who ∉ frontierActive G cfg
    | some action =>
        who ∈ frontierActive G cfg ∧ action ∈ frontierAvailable G cfg who }

@[simp] theorem mem_frontierMenu_none
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) :
    (none : Option (PlayerFrontierAction G who)) ∈ frontierMenu G cfg who ↔
      who ∉ frontierActive G cfg := by
  rfl

@[simp] theorem mem_frontierMenu_some
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (who : Player) (action : PlayerFrontierAction G who) :
    some action ∈ frontierMenu G cfg who ↔
      who ∈ frontierActive G cfg ∧ action ∈ frontierAvailable G cfg who := by
  rfl

/-- Execute one node from a frontier step using the joint frontier action.
Unavailable primitive events stutter through the underlying total machine step;
frontier soundness lemmas show the intended nodes remain available across
linearizations. -/
noncomputable def frontierStepNode
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node) (cfg : G.Configuration) :
    PMF G.Configuration :=
  match (G.sem node).actor with
  | some who =>
      match joint who with
      | some action =>
          stepPlay G who { node := node, patch := action.patch node } cfg
      | none => PMF.pure cfg
  | none =>
      (G.internalKernel node cfg.result).bind fun patch =>
        stepInternal G (.node node patch) cfg

/-- Player primitive event for a concrete frontier node patch. -/
private noncomputable def playerPrimitiveEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (who : Player) (node : G.Node) (patch : G.FieldPatch) :
    (G.toMachine iface).Event :=
  .play who { node := node, patch := patch }

/-- Internal primitive event for a realized internal-node patch. -/
private noncomputable def internalPrimitiveEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (node : G.Node) (patch : G.FieldPatch) :
    (G.toMachine iface).Event :=
  .internal (.node node patch)

/-- Primitive event associated with one source frontier node after the destination
state is known. Internal nodes read back the realized patch from the destination
result; player nodes are determined by the joint frontier action. -/
noncomputable def realizedNodeEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node) (dst : G.Configuration) :
    (G.toMachine iface).Event :=
  match (G.sem node).actor with
  | some who =>
      match joint who with
      | some action =>
          playerPrimitiveEvent G iface who node (action.patch node)
      | none => .internal .idle
  | none =>
      match dst.result node with
      | some patch => internalPrimitiveEvent G iface node patch
      | none => .internal .idle

@[simp] private theorem toMachine_step_playerPrimitiveEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (who : Player) (node : G.Node) (patch : G.FieldPatch)
    (cfg : G.Configuration) :
    (G.toMachine iface).step
        (playerPrimitiveEvent G iface who node patch) cfg =
      stepPlay G who { node := node, patch := patch } cfg := by
  rfl

@[simp] private theorem toMachine_step_internalPrimitiveEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (node : G.Node) (patch : G.FieldPatch)
    (cfg : G.Configuration) :
    (G.toMachine iface).step
        (internalPrimitiveEvent G iface node patch) cfg =
      stepInternal G (.node node patch) cfg := by
  rfl

private noncomputable def explicitFrontierBatchStep
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node)
    (acc : List (G.toMachine iface).Event × G.Configuration) :
    PMF (List (G.toMachine iface).Event × G.Configuration) := by
  classical
  let events := acc.1
  let current := acc.2
  exact
    match hactor : (G.sem node).actor with
    | some who =>
        match joint who with
        | some action =>
            let event :=
              playerPrimitiveEvent G iface who node (action.patch node)
            (stepPlay G who
              { node := node, patch := action.patch node } current).map
              fun next => (events ++ [event], next)
        | none =>
            PMF.pure (events ++ [(.internal .idle)], current)
    | none =>
        if hfrontier : node ∈ current.frontier then
          (G.internalKernel node current.result).bind fun patch =>
            let event := internalPrimitiveEvent G iface node patch
            (stepInternal G (.node node patch) current).map
              fun next => (events ++ [event], next)
        else
          PMF.pure (events ++ [(.internal .idle)], current)

private theorem explicitFrontierBatchStep_eq_map_frontierStepNode_of_frontier
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration)
    (hfrontier : node ∈ current.frontier) :
    explicitFrontierBatchStep G iface joint node (events, current) =
      PMF.map
        (fun next =>
          (events ++ [realizedNodeEvent G iface joint node next], next))
        (frontierStepNode G joint node current) := by
  classical
  unfold explicitFrontierBatchStep frontierStepNode
  cases hactor : (G.sem node).actor with
  | some who =>
      cases hmove : joint who
      · simp [hactor, hmove, realizedNodeEvent, PMF.pure_map]
      · simp [hactor, hmove, realizedNodeEvent, playerPrimitiveEvent]
  | none =>
      simp only [hfrontier, dite_true, PMF.map_bind]
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (G.internalKernel node current.result)
        (fun patch =>
          PMF.map
            (fun next => (events ++ [internalPrimitiveEvent G iface node patch], next))
            (stepInternal G (InternalEvent.node node patch) current))
        (fun patch =>
          PMF.map
            (fun next =>
              (events ++ [realizedNodeEvent G iface joint node next], next))
            (stepInternal G (InternalEvent.node node patch) current))
        ?_
      intro patch hpatch
      have havailable :
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current := by
        exact ⟨hfrontier, hactor, hpatch⟩
      have hnode :
          node ∈ current.frontier ∧
            (G.sem node).actor = none ∧
              patch ∈ (G.internalKernel node current.result).support :=
        ⟨hfrontier, hactor, hpatch⟩
      have hlegal : G.patchLegal node patch :=
        G.internalKernel_support_legal
          (current.mem_nodes_of_mem_frontier hfrontier)
          (current.not_done_of_mem_frontier hfrontier)
          (fun prereq hpre =>
            current.result_some_of_prereq_of_mem_frontier hfrontier hpre)
          (fun hresult => current.legal hresult)
          hactor hpatch
      have hstep :
          stepInternal G (InternalEvent.node node patch) current =
            PMF.pure (current.withPatch patch hfrontier hlegal) := by
        simp [stepInternal, havailable]
      change
        PMF.map
            (fun next =>
              (events ++ [internalPrimitiveEvent G iface node patch], next))
            (stepInternal G (InternalEvent.node node patch) current) =
          PMF.map
            (fun next =>
              (events ++ [realizedNodeEvent G iface joint node next], next))
            (stepInternal G (InternalEvent.node node patch) current)
      rw [hstep, PMF.pure_map, PMF.pure_map]
      simp [realizedNodeEvent, internalPrimitiveEvent, hactor,
        EventGraph.Configuration.withPatch]

private noncomputable def explicitFrontierBatchGo
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (nodes : List G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration) :
    PMF (List (G.toMachine iface).Event × G.Configuration) :=
  match nodes with
  | [] => PMF.pure (events, current)
  | node :: rest =>
      (explicitFrontierBatchStep G iface joint node (events, current)).bind
        fun next =>
          explicitFrontierBatchGo G iface joint rest next.1 next.2

noncomputable def scheduledFrontierTransitionGo
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerFrontierAction G))
    (nodes : List G.Node)
    (current : G.Configuration) :
    PMF G.Configuration :=
  match nodes with
  | [] => PMF.pure current
  | node :: rest =>
      (frontierStepNode G joint node current).bind fun next =>
        scheduledFrontierTransitionGo G joint rest next

private theorem stepPlay_eq_pure_of_available
    (G : Vegas.EventGraph Player L)
    {who : Player} {action : PlayerAction G who}
    {cfg : G.Configuration}
    (havailable : action ∈ available G cfg who) :
    stepPlay G who action cfg =
      PMF.pure
        (cfg.withPatch action.patch havailable.1 havailable.2.2.1) := by
  simp [stepPlay, havailable]

private theorem stepInternal_eq_pure_of_available
    (G : Vegas.EventGraph Player L)
    {node : G.Node} {patch : G.FieldPatch}
    {cfg : G.Configuration}
    (havailable :
      (InternalEvent.node node patch : InternalEvent G) ∈
        availableInternal G cfg)
    (hfrontier : node ∈ cfg.frontier)
    (hlegal : G.patchLegal node patch) :
    stepInternal G (InternalEvent.node node patch) cfg =
      PMF.pure (cfg.withPatch patch hfrontier hlegal) := by
  simp [stepInternal.eq_def, havailable]

private theorem frontierStepNode_result_eq_of_ne
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerFrontierAction G))
    {node candidate : G.Node}
    (hne : candidate ≠ node)
    {current dst : G.Configuration}
    (hsupp : dst ∈ (frontierStepNode G joint node current).support) :
    dst.result candidate = current.result candidate := by
  classical
  unfold frontierStepNode at hsupp
  cases hactor : (G.sem node).actor with
  | some who =>
      cases hmove : joint who with
      | none =>
          have hdst : dst = current := by
            simpa [hactor, hmove] using hsupp
          subst dst
          rfl
      | some action =>
          by_cases havailable :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G current who
          · have hdst :
                dst =
                  current.withPatch (action.patch node)
                    havailable.1 havailable.2.2.1 := by
              simpa [stepPlay, hactor, hmove, havailable] using hsupp
            subst dst
            simp [Configuration.withPatch, Configuration.updatePatch, hne]
          · have hdst : dst = current := by
              simpa [stepPlay, hactor, hmove, havailable] using hsupp
            subst dst
            rfl
  | none =>
      simp only [hactor, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨patch, _hpatch, hstepMass⟩
      have hstep :
          dst ∈
            (stepInternal G (InternalEvent.node node patch) current).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      by_cases havailable :
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current
      · have hnode :
            node ∈ current.frontier ∧
              (G.sem node).actor = none ∧
                patch ∈ (G.internalKernel node current.result).support := by
          simpa [availableInternal] using havailable
        have hlegal : G.patchLegal node patch :=
          G.internalKernel_support_legal
            (current.mem_nodes_of_mem_frontier hnode.1)
            (current.not_done_of_mem_frontier hnode.1)
            (fun prereq hpre =>
              current.result_some_of_prereq_of_mem_frontier hnode.1 hpre)
            (fun hresult => current.legal hresult)
            hnode.2.1 hnode.2.2
        have hdst :
            dst = current.withPatch patch hnode.1 hlegal := by
          simpa [stepInternal, havailable, hnode, hlegal] using hstep
        subst dst
        simp [Configuration.withPatch, Configuration.updatePatch, hne]
      · have hdst : dst = current := by
          simpa [stepInternal, havailable] using hstep
        subst dst
        rfl

private theorem frontierStepNode_frontier_of_ne
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerFrontierAction G))
    {node candidate : G.Node}
    {current dst : G.Configuration}
    (hcandidate : candidate ∈ current.frontier)
    (hne : candidate ≠ node)
    (hsupp : dst ∈ (frontierStepNode G joint node current).support) :
    candidate ∈ dst.frontier := by
  classical
  unfold frontierStepNode at hsupp
  cases hactor : (G.sem node).actor with
  | some who =>
      cases hmove : joint who with
      | none =>
          have hdst : dst = current := by
            simpa [hactor, hmove] using hsupp
          subst dst
          exact hcandidate
      | some action =>
          by_cases havailable :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G current who
          · have hdst :
                dst =
                  current.withPatch (action.patch node)
                    havailable.1 havailable.2.2.1 := by
              simpa [stepPlay, hactor, hmove, havailable] using hsupp
            subst dst
            exact current.withPatch_mem_frontier_of_ne
              havailable.1 hcandidate hne havailable.2.2.1
          · have hdst : dst = current := by
              simpa [stepPlay, hactor, hmove, havailable] using hsupp
            subst dst
            exact hcandidate
  | none =>
      simp only [hactor, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨patch, _hpatch, hstepMass⟩
      have hstep :
          dst ∈
            (stepInternal G (InternalEvent.node node patch) current).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      by_cases havailable :
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current
      · have hnode :
            node ∈ current.frontier ∧
              (G.sem node).actor = none ∧
                patch ∈ (G.internalKernel node current.result).support := by
          simpa [availableInternal] using havailable
        have hlegal : G.patchLegal node patch :=
          G.internalKernel_support_legal
            (current.mem_nodes_of_mem_frontier hnode.1)
            (current.not_done_of_mem_frontier hnode.1)
            (fun prereq hpre =>
              current.result_some_of_prereq_of_mem_frontier hnode.1 hpre)
            (fun hresult => current.legal hresult)
            hnode.2.1 hnode.2.2
        have hdst :
            dst = current.withPatch patch hnode.1 hlegal := by
          simpa [stepInternal, havailable, hnode, hlegal] using hstep
        subst dst
        exact current.withPatch_mem_frontier_of_ne
          hnode.1 hcandidate hne hlegal
      · have hdst : dst = current := by
          simpa [stepInternal, havailable] using hstep
        subst dst
        exact hcandidate

private theorem frontierStepNode_preserves_available_of_ne
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (PlayerFrontierAction G))
    {node : G.Node}
    {current mid : G.Configuration}
    (hmid : mid ∈ (frontierStepNode G joint node current).support)
    {who : Player} {action : PlayerAction G who}
    (hne : action.node ≠ node)
    (haction : action ∈ available G current who) :
    action ∈ available G mid who := by
  classical
  unfold frontierStepNode at hmid
  cases hactor : (G.sem node).actor with
  | some owner =>
      cases hmove : joint owner with
      | none =>
          have hdst : mid = current := by
            simpa [hactor, hmove] using hmid
          subst mid
          exact haction
      | some frontierAction =>
          by_cases havailable :
              ({ node := node, patch := frontierAction.patch node } :
                PlayerAction G owner) ∈ available G current owner
          · have hdst :
                mid =
                  current.withPatch (frontierAction.patch node)
                    havailable.1 havailable.2.2.1 := by
              simpa [stepPlay, hactor, hmove, havailable] using hmid
            subst mid
            exact hsound.actionStable current
              havailable.1 haction.1 hne havailable.2.2.1 haction
          · have hdst : mid = current := by
              simpa [stepPlay, hactor, hmove, havailable] using hmid
            subst mid
            exact haction
  | none =>
      simp only [hactor, PMF.mem_support_bind_iff] at hmid
      rcases hmid with ⟨patch, _hpatch, hstepMass⟩
      have hstep :
          mid ∈
            (stepInternal G (InternalEvent.node node patch) current).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      by_cases havailable :
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current
      · have hnode :
            node ∈ current.frontier ∧
              (G.sem node).actor = none ∧
                patch ∈ (G.internalKernel node current.result).support := by
          simpa [availableInternal] using havailable
        have hlegal : G.patchLegal node patch :=
          G.internalKernel_support_legal
            (current.mem_nodes_of_mem_frontier hnode.1)
            (current.not_done_of_mem_frontier hnode.1)
            (fun prereq hpre =>
              current.result_some_of_prereq_of_mem_frontier hnode.1 hpre)
            (fun hresult => current.legal hresult)
            hnode.2.1 hnode.2.2
        have hdst :
            mid = current.withPatch patch hnode.1 hlegal := by
          simpa [stepInternal, havailable, hnode, hlegal] using hstep
        subst mid
        exact hsound.actionStable current
          hnode.1 haction.1 hne hlegal haction
      · have hdst : mid = current := by
          simpa [stepInternal, havailable] using hstep
        subst mid
        exact haction

private def frontierNodeReady
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerFrontierAction G))
    (cfg : G.Configuration) (node : G.Node) : Prop :=
  node ∈ cfg.frontier ∧
    match (G.sem node).actor with
    | some who =>
        ∃ action : PlayerFrontierAction G who,
          joint who = some action ∧
            ({ node := node, patch := action.patch node } :
              PlayerAction G who) ∈ available G cfg who
    | none => True

private theorem frontierNodeReady_of_legal
    (G : Vegas.EventGraph Player L)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {node : G.Node}
    (hfrontier : node ∈ cfg.frontier) :
    frontierNodeReady G joint cfg node := by
  classical
  refine ⟨hfrontier, ?_⟩
  cases hactor : (G.sem node).actor with
  | none =>
      trivial
  | some who =>
      have hactive : who ∈ frontierActive G cfg :=
        (mem_frontierActive_iff G cfg who).mpr ⟨node, hfrontier, hactor⟩
      have hcoord := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ frontierActive G cfg ∧
                (∀ {node},
                  node ∈ cfg.frontier →
                  (G.sem node).actor = some who →
                    G.patchLegal node (action.patch node) ∧
                      G.actionLegal cfg.result node (action.patch node)) := by
            simpa [hmove, frontierAvailable] using hcoord
          have hnodeLegal := hpair.2 hfrontier hactor
          exact ⟨action, hmove,
            ⟨hfrontier, hactor, hnodeLegal.1, hnodeLegal.2⟩⟩

private theorem frontierStepNode_preserves_ready_of_ne
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (PlayerFrontierAction G))
    {node candidate : G.Node}
    {current mid : G.Configuration}
    (hmid : mid ∈ (frontierStepNode G joint node current).support)
    (hne : candidate ≠ node)
    (hready : frontierNodeReady G joint current candidate) :
    frontierNodeReady G joint mid candidate := by
  classical
  rcases hready with ⟨hcandidate, hdata⟩
  refine ⟨frontierStepNode_frontier_of_ne G joint hcandidate hne hmid, ?_⟩
  cases hactor : (G.sem candidate).actor with
  | none =>
      simp [hactor] at hdata ⊢
  | some who =>
      rcases (by simpa [hactor] using hdata) with
        ⟨action, hmove, havailable⟩
      exact ⟨action, hmove,
        frontierStepNode_preserves_available_of_ne
          G hsound joint hmid hne havailable⟩

private theorem frontierStepNode_comm_of_ready
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (PlayerFrontierAction G))
    (cfg : G.Configuration)
    {left right : G.Node}
    (hne : left ≠ right)
    (hleftReady : frontierNodeReady G joint cfg left)
    (hrightReady : frontierNodeReady G joint cfg right) :
    (frontierStepNode G joint left cfg).bind
        (fun mid => frontierStepNode G joint right mid) =
      (frontierStepNode G joint right cfg).bind
        (fun mid => frontierStepNode G joint left mid) := by
  classical
  rcases hleftReady with ⟨hleftFrontier, hleftData⟩
  rcases hrightReady with ⟨hrightFrontier, hrightData⟩
  cases hleftActor : (G.sem left).actor with
  | some leftWho =>
      rcases (by simpa [hleftActor] using hleftData) with
        ⟨leftAction, hleftMove, hleftAvail⟩
      have hleftLegal : G.patchLegal left (leftAction.patch left) :=
        hleftAvail.2.2.1
      have hleftStep :
          frontierStepNode G joint left cfg =
            PMF.pure
              (cfg.withPatch (leftAction.patch left)
                hleftFrontier hleftLegal) := by
        simp [frontierStepNode, hleftActor, hleftMove, stepPlay, hleftAvail]
      cases hrightActor : (G.sem right).actor with
      | some rightWho =>
          rcases (by simpa [hrightActor] using hrightData) with
            ⟨rightAction, hrightMove, hrightAvail⟩
          have hrightLegal : G.patchLegal right (rightAction.patch right) :=
            hrightAvail.2.2.1
          have hrightStep :
              frontierStepNode G joint right cfg =
                PMF.pure
                  (cfg.withPatch (rightAction.patch right)
                    hrightFrontier hrightLegal) := by
            simp [frontierStepNode, hrightActor, hrightMove, stepPlay, hrightAvail]
          let cfgLeft :=
            cfg.withPatch (leftAction.patch left) hleftFrontier hleftLegal
          let cfgRight :=
            cfg.withPatch (rightAction.patch right) hrightFrontier hrightLegal
          have hrightAvailAfterLeft :
              ({ node := right, patch := rightAction.patch right } :
                PlayerAction G rightWho) ∈ available G cfgLeft rightWho := by
            dsimp [cfgLeft]
            exact hsound.actionStable cfg hleftFrontier hrightFrontier
              (Ne.symm hne) hleftLegal hrightAvail
          have hleftAvailAfterRight :
              ({ node := left, patch := leftAction.patch left } :
                PlayerAction G leftWho) ∈ available G cfgRight leftWho := by
            dsimp [cfgRight]
            exact hsound.actionStable cfg hrightFrontier hleftFrontier
              hne hrightLegal hleftAvail
          have hrightStepAfterLeft :
              frontierStepNode G joint right cfgLeft =
                PMF.pure
                  (cfgLeft.withPatch (rightAction.patch right)
                    hrightAvailAfterLeft.1 hrightLegal) := by
            simp [frontierStepNode, hrightActor, hrightMove, stepPlay,
              hrightAvailAfterLeft]
          have hleftStepAfterRight :
              frontierStepNode G joint left cfgRight =
                PMF.pure
                  (cfgRight.withPatch (leftAction.patch left)
                    hleftAvailAfterRight.1 hleftLegal) := by
            simp [frontierStepNode, hleftActor, hleftMove, stepPlay,
              hleftAvailAfterRight]
          have hcomm :
              cfgLeft.withPatch (rightAction.patch right)
                  hrightAvailAfterLeft.1 hrightLegal =
                cfgRight.withPatch (leftAction.patch left)
                  hleftAvailAfterRight.1 hleftLegal := by
            dsimp [cfgLeft, cfgRight]
            exact cfg.withPatch_comm hleftFrontier hrightFrontier hne
              hleftLegal hrightLegal
          rw [hleftStep, PMF.pure_bind, hrightStepAfterLeft,
            hrightStep, PMF.pure_bind, hleftStepAfterRight, hcomm]
      | none =>
          have hrightKernelStable :
              G.internalKernel right
                  (cfg.withPatch (leftAction.patch left)
                    hleftFrontier hleftLegal).result =
                G.internalKernel right cfg.result :=
            hsound.internalKernelStable cfg hleftFrontier hrightFrontier
              (Ne.symm hne) hleftLegal
          rw [hleftStep, PMF.pure_bind]
          unfold frontierStepNode
          simp only [hrightActor, hleftActor, hleftMove]
          rw [hrightKernelStable]
          rw [PMF.bind_bind]
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (G.internalKernel right cfg.result)
            (fun patch =>
              (stepInternal G (InternalEvent.node right patch)
                (cfg.withPatch (leftAction.patch left)
                  hleftFrontier hleftLegal)))
            (fun patch =>
              (stepInternal G (InternalEvent.node right patch) cfg).bind
                fun cfgRight =>
                  stepPlay G leftWho
                    { node := left, patch := leftAction.patch left }
                    cfgRight)
            ?_
          intro rightPatch hrightPatch
          have hrightAvailable :
              (InternalEvent.node right rightPatch : InternalEvent G) ∈
                availableInternal G cfg := by
            exact ⟨hrightFrontier, hrightActor, hrightPatch⟩
          have hrightLegal : G.patchLegal right rightPatch :=
            G.internalKernel_support_legal
              (cfg.mem_nodes_of_mem_frontier hrightFrontier)
              (cfg.not_done_of_mem_frontier hrightFrontier)
              (fun prereq hpre =>
                cfg.result_some_of_prereq_of_mem_frontier hrightFrontier hpre)
              (fun hresult => cfg.legal hresult)
              hrightActor hrightPatch
          let cfgLeft :=
            cfg.withPatch (leftAction.patch left) hleftFrontier hleftLegal
          let cfgRight :=
            cfg.withPatch rightPatch hrightFrontier hrightLegal
          have hrightFrontierAfterLeft :
              right ∈ cfgLeft.frontier := by
            dsimp [cfgLeft]
            exact cfg.withPatch_mem_frontier_of_ne hleftFrontier
              hrightFrontier (Ne.symm hne) hleftLegal
          have hrightAvailableAfterLeft :
              (InternalEvent.node right rightPatch : InternalEvent G) ∈
                availableInternal G cfgLeft := by
            dsimp [cfgLeft]
            refine ⟨hrightFrontierAfterLeft, hrightActor, ?_⟩
            rw [hrightKernelStable]
            exact hrightPatch
          have hleftAvailAfterRight :
              ({ node := left, patch := leftAction.patch left } :
                PlayerAction G leftWho) ∈ available G cfgRight leftWho := by
            dsimp [cfgRight]
            exact hsound.actionStable cfg hrightFrontier hleftFrontier
              hne hrightLegal hleftAvail
          have hcomm :
              cfgLeft.withPatch rightPatch
                  hrightFrontierAfterLeft hrightLegal =
                cfgRight.withPatch (leftAction.patch left)
                  hleftAvailAfterRight.1 hleftLegal := by
            dsimp [cfgLeft, cfgRight]
            exact cfg.withPatch_comm hleftFrontier hrightFrontier hne
              hleftLegal hrightLegal
          change
            stepInternal G (InternalEvent.node right rightPatch) cfgLeft =
              (stepInternal G (InternalEvent.node right rightPatch) cfg).bind
                fun cfgRight =>
                  stepPlay G leftWho
                    { node := left, patch := leftAction.patch left }
                    cfgRight
          rw [stepInternal_eq_pure_of_available
            G hrightAvailableAfterLeft hrightFrontierAfterLeft hrightLegal]
          rw [stepInternal_eq_pure_of_available
            G hrightAvailable hrightFrontier hrightLegal]
          rw [PMF.pure_bind]
          rw [stepPlay_eq_pure_of_available G hleftAvailAfterRight]
          exact congrArg PMF.pure hcomm
  | none =>
      cases hrightActor : (G.sem right).actor with
      | some rightWho =>
          rcases (by simpa [hrightActor] using hrightData) with
            ⟨rightAction, hrightMove, hrightAvail⟩
          have hrightLegal : G.patchLegal right (rightAction.patch right) :=
            hrightAvail.2.2.1
          have hrightStep :
              frontierStepNode G joint right cfg =
                PMF.pure
                  (cfg.withPatch (rightAction.patch right)
                    hrightFrontier hrightLegal) := by
            simp [frontierStepNode, hrightActor, hrightMove, stepPlay, hrightAvail]
          have hleftKernelStable :
              G.internalKernel left
                  (cfg.withPatch (rightAction.patch right)
                    hrightFrontier hrightLegal).result =
                G.internalKernel left cfg.result :=
            hsound.internalKernelStable cfg hrightFrontier hleftFrontier
              hne hrightLegal
          rw [hrightStep, PMF.pure_bind]
          unfold frontierStepNode
          simp only [hleftActor, hrightActor, hrightMove]
          rw [hleftKernelStable]
          rw [PMF.bind_bind]
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (G.internalKernel left cfg.result)
            (fun leftPatch =>
              (stepInternal G (InternalEvent.node left leftPatch) cfg).bind
                fun cfgLeft =>
                  stepPlay G rightWho
                    { node := right, patch := rightAction.patch right }
                    cfgLeft)
            (fun leftPatch =>
              (stepInternal G (InternalEvent.node left leftPatch)
                (cfg.withPatch (rightAction.patch right)
                  hrightFrontier hrightLegal)))
            ?_
          intro leftPatch hleftPatch
          have hleftAvailable :
              (InternalEvent.node left leftPatch : InternalEvent G) ∈
                availableInternal G cfg := by
            exact ⟨hleftFrontier, hleftActor, hleftPatch⟩
          have hleftLegal : G.patchLegal left leftPatch :=
            G.internalKernel_support_legal
              (cfg.mem_nodes_of_mem_frontier hleftFrontier)
              (cfg.not_done_of_mem_frontier hleftFrontier)
              (fun prereq hpre =>
                cfg.result_some_of_prereq_of_mem_frontier hleftFrontier hpre)
              (fun hresult => cfg.legal hresult)
              hleftActor hleftPatch
          let cfgLeft :=
            cfg.withPatch leftPatch hleftFrontier hleftLegal
          let cfgRight :=
            cfg.withPatch (rightAction.patch right)
              hrightFrontier hrightLegal
          have hleftFrontierAfterRight :
              left ∈ cfgRight.frontier := by
            dsimp [cfgRight]
            exact cfg.withPatch_mem_frontier_of_ne hrightFrontier
              hleftFrontier hne hrightLegal
          have hleftAvailableAfterRight :
              (InternalEvent.node left leftPatch : InternalEvent G) ∈
                availableInternal G cfgRight := by
            dsimp [cfgRight]
            refine ⟨hleftFrontierAfterRight, hleftActor, ?_⟩
            rw [hleftKernelStable]
            exact hleftPatch
          have hrightAvailAfterLeft :
              ({ node := right, patch := rightAction.patch right } :
                PlayerAction G rightWho) ∈ available G cfgLeft rightWho := by
            dsimp [cfgLeft]
            exact hsound.actionStable cfg hleftFrontier hrightFrontier
              (Ne.symm hne) hleftLegal hrightAvail
          have hcomm :
              cfgLeft.withPatch (rightAction.patch right)
                  hrightAvailAfterLeft.1 hrightLegal =
                cfgRight.withPatch leftPatch
                  hleftFrontierAfterRight hleftLegal := by
            dsimp [cfgLeft, cfgRight]
            exact cfg.withPatch_comm hleftFrontier hrightFrontier hne
              hleftLegal hrightLegal
          change
            ((stepInternal G (InternalEvent.node left leftPatch) cfg).bind
                fun cfgLeft =>
                  stepPlay G rightWho
                    { node := right, patch := rightAction.patch right }
                    cfgLeft) =
              stepInternal G (InternalEvent.node left leftPatch) cfgRight
          rw [stepInternal_eq_pure_of_available
            G hleftAvailable hleftFrontier hleftLegal]
          rw [PMF.pure_bind]
          rw [stepPlay_eq_pure_of_available G hrightAvailAfterLeft]
          rw [stepInternal_eq_pure_of_available
            G hleftAvailableAfterRight hleftFrontierAfterRight hleftLegal]
          exact congrArg PMF.pure hcomm
      | none =>
          unfold frontierStepNode
          simp only [hleftActor, hrightActor]
          rw [PMF.bind_bind, PMF.bind_bind]
          have hleftNormalize :
              ((G.internalKernel left cfg.result).bind fun leftPatch =>
                (stepInternal G (InternalEvent.node left leftPatch) cfg).bind
                  fun mid =>
                    (G.internalKernel right mid.result).bind fun rightPatch =>
                      stepInternal G (InternalEvent.node right rightPatch)
                        mid) =
                (G.internalKernel left cfg.result).bind fun leftPatch =>
                  (G.internalKernel right cfg.result).bind fun rightPatch =>
                    (stepInternal G (InternalEvent.node left leftPatch)
                      cfg).bind fun mid =>
                        stepInternal G
                          (InternalEvent.node right rightPatch) mid := by
            refine Math.ProbabilityMassFunction.bind_congr_on_support
              (G.internalKernel left cfg.result) _ _ ?_
            intro leftPatch hleftPatch
            have hleftAvailable :
                (InternalEvent.node left leftPatch : InternalEvent G) ∈
                  availableInternal G cfg := by
              exact ⟨hleftFrontier, hleftActor, hleftPatch⟩
            have hleftLegal : G.patchLegal left leftPatch :=
              G.internalKernel_support_legal
                (cfg.mem_nodes_of_mem_frontier hleftFrontier)
                (cfg.not_done_of_mem_frontier hleftFrontier)
                (fun prereq hpre =>
                  cfg.result_some_of_prereq_of_mem_frontier
                    hleftFrontier hpre)
                (fun hresult => cfg.legal hresult)
                hleftActor hleftPatch
            let cfgLeft :=
              cfg.withPatch leftPatch hleftFrontier hleftLegal
            have hrightKernelStable :
                G.internalKernel right cfgLeft.result =
                  G.internalKernel right cfg.result := by
              dsimp [cfgLeft]
              exact hsound.internalKernelStable cfg hleftFrontier
                hrightFrontier (Ne.symm hne) hleftLegal
            rw [stepInternal_eq_pure_of_available
              G hleftAvailable hleftFrontier hleftLegal]
            rw [PMF.pure_bind]
            rw [show
              G.internalKernel right
                  (cfg.withPatch leftPatch hleftFrontier hleftLegal).result =
                G.internalKernel right cfg.result by
              simpa [cfgLeft] using hrightKernelStable]
            simp [PMF.pure_bind]
          have hrightNormalize :
              ((G.internalKernel right cfg.result).bind fun rightPatch =>
                (stepInternal G (InternalEvent.node right rightPatch) cfg).bind
                  fun mid =>
                    (G.internalKernel left mid.result).bind fun leftPatch =>
                      stepInternal G (InternalEvent.node left leftPatch)
                        mid) =
                (G.internalKernel right cfg.result).bind fun rightPatch =>
                  (G.internalKernel left cfg.result).bind fun leftPatch =>
                    (stepInternal G (InternalEvent.node right rightPatch)
                      cfg).bind fun mid =>
                        stepInternal G
                          (InternalEvent.node left leftPatch) mid := by
            refine Math.ProbabilityMassFunction.bind_congr_on_support
              (G.internalKernel right cfg.result) _ _ ?_
            intro rightPatch hrightPatch
            have hrightAvailable :
                (InternalEvent.node right rightPatch : InternalEvent G) ∈
                  availableInternal G cfg := by
              exact ⟨hrightFrontier, hrightActor, hrightPatch⟩
            have hrightLegal : G.patchLegal right rightPatch :=
              G.internalKernel_support_legal
                (cfg.mem_nodes_of_mem_frontier hrightFrontier)
                (cfg.not_done_of_mem_frontier hrightFrontier)
                (fun prereq hpre =>
                  cfg.result_some_of_prereq_of_mem_frontier
                    hrightFrontier hpre)
                (fun hresult => cfg.legal hresult)
                hrightActor hrightPatch
            let cfgRight :=
              cfg.withPatch rightPatch hrightFrontier hrightLegal
            have hleftKernelStable :
                G.internalKernel left cfgRight.result =
                  G.internalKernel left cfg.result := by
              dsimp [cfgRight]
              exact hsound.internalKernelStable cfg hrightFrontier
                hleftFrontier hne hrightLegal
            rw [stepInternal_eq_pure_of_available
              G hrightAvailable hrightFrontier hrightLegal]
            rw [PMF.pure_bind]
            rw [show
              G.internalKernel left
                  (cfg.withPatch rightPatch hrightFrontier hrightLegal).result =
                G.internalKernel left cfg.result by
              simpa [cfgRight] using hleftKernelStable]
            simp [PMF.pure_bind]
          rw [hleftNormalize, hrightNormalize]
          rw [PMF.bind_comm (G.internalKernel left cfg.result)
            (G.internalKernel right cfg.result)]
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (G.internalKernel right cfg.result)
            (fun rightPatch =>
              (G.internalKernel left cfg.result).bind fun leftPatch =>
                stepInternal G (InternalEvent.node left leftPatch) cfg >>= fun cfgLeft =>
                  stepInternal G (InternalEvent.node right rightPatch) cfgLeft)
            (fun rightPatch =>
              (G.internalKernel left cfg.result).bind fun leftPatch =>
                stepInternal G (InternalEvent.node right rightPatch) cfg >>= fun cfgRight =>
                  stepInternal G (InternalEvent.node left leftPatch) cfgRight)
            ?_
          intro rightPatch hrightPatch
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (G.internalKernel left cfg.result)
            (fun leftPatch =>
              stepInternal G (InternalEvent.node left leftPatch) cfg >>= fun cfgLeft =>
                stepInternal G (InternalEvent.node right rightPatch) cfgLeft)
            (fun leftPatch =>
              stepInternal G (InternalEvent.node right rightPatch) cfg >>= fun cfgRight =>
                stepInternal G (InternalEvent.node left leftPatch) cfgRight)
            ?_
          intro leftPatch hleftPatch
          have hleftAvailable :
              (InternalEvent.node left leftPatch : InternalEvent G) ∈
                availableInternal G cfg := by
            exact ⟨hleftFrontier, hleftActor, hleftPatch⟩
          have hrightAvailable :
              (InternalEvent.node right rightPatch : InternalEvent G) ∈
                availableInternal G cfg := by
            exact ⟨hrightFrontier, hrightActor, hrightPatch⟩
          have hleftLegal : G.patchLegal left leftPatch :=
            G.internalKernel_support_legal
              (cfg.mem_nodes_of_mem_frontier hleftFrontier)
              (cfg.not_done_of_mem_frontier hleftFrontier)
              (fun prereq hpre =>
                cfg.result_some_of_prereq_of_mem_frontier hleftFrontier hpre)
              (fun hresult => cfg.legal hresult)
              hleftActor hleftPatch
          have hrightLegal : G.patchLegal right rightPatch :=
            G.internalKernel_support_legal
              (cfg.mem_nodes_of_mem_frontier hrightFrontier)
              (cfg.not_done_of_mem_frontier hrightFrontier)
              (fun prereq hpre =>
                cfg.result_some_of_prereq_of_mem_frontier hrightFrontier hpre)
              (fun hresult => cfg.legal hresult)
              hrightActor hrightPatch
          let cfgLeft := cfg.withPatch leftPatch hleftFrontier hleftLegal
          let cfgRight := cfg.withPatch rightPatch hrightFrontier hrightLegal
          have hrightKernelStable :
              G.internalKernel right cfgLeft.result =
                G.internalKernel right cfg.result := by
            dsimp [cfgLeft]
            exact hsound.internalKernelStable cfg hleftFrontier
              hrightFrontier (Ne.symm hne) hleftLegal
          have hleftKernelStable :
              G.internalKernel left cfgRight.result =
                G.internalKernel left cfg.result := by
            dsimp [cfgRight]
            exact hsound.internalKernelStable cfg hrightFrontier
              hleftFrontier hne hrightLegal
          have hrightFrontierAfterLeft :
              right ∈ cfgLeft.frontier := by
            dsimp [cfgLeft]
            exact cfg.withPatch_mem_frontier_of_ne hleftFrontier
              hrightFrontier (Ne.symm hne) hleftLegal
          have hleftFrontierAfterRight :
              left ∈ cfgRight.frontier := by
            dsimp [cfgRight]
            exact cfg.withPatch_mem_frontier_of_ne hrightFrontier
              hleftFrontier hne hrightLegal
          have hrightAvailableAfterLeft :
              (InternalEvent.node right rightPatch : InternalEvent G) ∈
                availableInternal G cfgLeft := by
            dsimp [cfgLeft]
            refine ⟨hrightFrontierAfterLeft, hrightActor, ?_⟩
            rw [hrightKernelStable]
            exact hrightPatch
          have hleftAvailableAfterRight :
              (InternalEvent.node left leftPatch : InternalEvent G) ∈
                availableInternal G cfgRight := by
            dsimp [cfgRight]
            refine ⟨hleftFrontierAfterRight, hleftActor, ?_⟩
            rw [hleftKernelStable]
            exact hleftPatch
          have hcomm :
              cfgLeft.withPatch rightPatch
                  hrightFrontierAfterLeft hrightLegal =
                cfgRight.withPatch leftPatch
                  hleftFrontierAfterRight hleftLegal := by
            dsimp [cfgLeft, cfgRight]
            exact cfg.withPatch_comm hleftFrontier hrightFrontier hne
              hleftLegal hrightLegal
          change
            ((stepInternal G (InternalEvent.node left leftPatch) cfg).bind
                fun cfgLeft =>
                  stepInternal G (InternalEvent.node right rightPatch)
                    cfgLeft) =
              ((stepInternal G (InternalEvent.node right rightPatch) cfg).bind
                fun cfgRight =>
                  stepInternal G (InternalEvent.node left leftPatch)
                    cfgRight)
          rw [stepInternal_eq_pure_of_available
            G hleftAvailable hleftFrontier hleftLegal]
          rw [PMF.pure_bind]
          rw [stepInternal_eq_pure_of_available
            G hrightAvailableAfterLeft hrightFrontierAfterLeft hrightLegal]
          rw [stepInternal_eq_pure_of_available
            G hrightAvailable hrightFrontier hrightLegal]
          rw [PMF.pure_bind]
          rw [stepInternal_eq_pure_of_available
            G hleftAvailableAfterRight hleftFrontierAfterRight hleftLegal]
          exact congrArg PMF.pure hcomm

private theorem scheduledFrontierTransitionGo_eq_of_perm_ready
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (PlayerFrontierAction G)) :
    ∀ {nodes₁ nodes₂ : List G.Node} {current : G.Configuration},
      nodes₁.Perm nodes₂ →
      nodes₁.Nodup →
      (∀ node, node ∈ nodes₁ → frontierNodeReady G joint current node) →
        scheduledFrontierTransitionGo G joint nodes₁ current =
          scheduledFrontierTransitionGo G joint nodes₂ current := by
  intro nodes₁ nodes₂ current hperm
  induction hperm generalizing current with
  | nil =>
      intro _hnodup _hready
      rfl
  | cons node hperm ih =>
      intro hnodup hready
      have hnodupTail := (List.nodup_cons.mp hnodup).2
      have hnodeNotTail := (List.nodup_cons.mp hnodup).1
      simp only [scheduledFrontierTransitionGo]
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (frontierStepNode G joint node current) _ _ ?_
      intro mid hmid
      exact ih hnodupTail (fun candidate hcandidate =>
        frontierStepNode_preserves_ready_of_ne G hsound joint hmid
          (by
            intro heq
            subst candidate
            exact hnodeNotTail hcandidate)
          (hready candidate (List.mem_cons_of_mem _ hcandidate)))
  | swap left right rest =>
      intro hnodup hready
      have hleftNeRight : left ≠ right := by
        intro heq
        subst left
        exact (List.nodup_cons.mp hnodup).1 (by simp)
      have hleftReady :
          frontierNodeReady G joint current left := hready left (by simp)
      have hrightReady :
          frontierNodeReady G joint current right := hready right (by simp)
      simp only [scheduledFrontierTransitionGo]
      rw [← PMF.bind_bind, ← PMF.bind_bind]
      rw [frontierStepNode_comm_of_ready
        G hsound joint current hleftNeRight hleftReady hrightReady]
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hnodup hready
      have hnodupMid := h₁.nodup hnodup
      have hreadyMid := fun node hnode =>
        hready node ((h₁.mem_iff).2 hnode)
      exact (ih₁ hnodup hready).trans (ih₂ hnodupMid hreadyMid)

/-- Executing one frontier node does not change the internal kernel of a
different frontier node under local frontier-step soundness. -/
theorem frontierStepNode_preserves_internalKernel_of_ne
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (PlayerFrontierAction G))
    {node candidate : G.Node}
    {current mid : G.Configuration}
    (hmid : mid ∈ (frontierStepNode G joint node current).support)
    (hcandidate : candidate ∈ current.frontier)
    (hne : candidate ≠ node) :
    G.internalKernel candidate mid.result =
      G.internalKernel candidate current.result := by
  classical
  unfold frontierStepNode at hmid
  cases hactor : (G.sem node).actor with
  | some owner =>
      cases hmove : joint owner with
      | none =>
          have hdst : mid = current := by
            simpa [hactor, hmove] using hmid
          subst mid
          rfl
      | some frontierAction =>
          by_cases havailable :
              ({ node := node, patch := frontierAction.patch node } :
                PlayerAction G owner) ∈ available G current owner
          · have hdst :
                mid =
                  current.withPatch (frontierAction.patch node)
                    havailable.1 havailable.2.2.1 := by
              simpa [stepPlay, hactor, hmove, havailable] using hmid
            subst mid
            exact hsound.internalKernelStable current
              havailable.1 hcandidate hne havailable.2.2.1
          · have hdst : mid = current := by
              simpa [stepPlay, hactor, hmove, havailable] using hmid
            subst mid
            rfl
  | none =>
      simp only [hactor, PMF.mem_support_bind_iff] at hmid
      rcases hmid with ⟨patch, _hpatch, hstepMass⟩
      have hstep :
          mid ∈
            (stepInternal G (InternalEvent.node node patch) current).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      by_cases havailable :
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current
      · have hnode :
            node ∈ current.frontier ∧
              (G.sem node).actor = none ∧
                patch ∈ (G.internalKernel node current.result).support := by
          simpa [availableInternal] using havailable
        have hlegal : G.patchLegal node patch :=
          G.internalKernel_support_legal
            (current.mem_nodes_of_mem_frontier hnode.1)
            (current.not_done_of_mem_frontier hnode.1)
            (fun prereq hpre =>
              current.result_some_of_prereq_of_mem_frontier hnode.1 hpre)
            (fun hresult => current.legal hresult)
            hnode.2.1 hnode.2.2
        have hdst :
            mid = current.withPatch patch hnode.1 hlegal := by
          simpa [stepInternal, havailable, hnode, hlegal] using hstep
        subst mid
        exact hsound.internalKernelStable current
          hnode.1 hcandidate hne hlegal
      · have hdst : mid = current := by
          simpa [stepInternal, havailable] using hstep
        subst mid
        rfl

/-- A prefix of distinct frontier executions does not change the internal
kernel of a source-frontier node that the prefix does not execute. This is the
kernel-stability form used to treat the canonical frontier order as a proof
linearization. -/
theorem scheduledFrontierTransitionGo_preserves_internalKernel_of_not_mem
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (PlayerFrontierAction G))
    (nodes : List G.Node)
    {candidate : G.Node}
    {current dst : G.Configuration}
    (hcandidate : candidate ∈ current.frontier)
    (hnotmem : candidate ∉ nodes)
    (hsupp : dst ∈ (scheduledFrontierTransitionGo G joint nodes current).support) :
    G.internalKernel candidate dst.result =
      G.internalKernel candidate current.result := by
  classical
  induction nodes generalizing current with
  | nil =>
      have hdst : dst = current := by
        simpa [scheduledFrontierTransitionGo] using hsupp
      subst dst
      rfl
  | cons node rest ih =>
      simp only [scheduledFrontierTransitionGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨mid, hmid, hdstRest⟩
      have hnotData : candidate ≠ node ∧ candidate ∉ rest := by
        simpa using hnotmem
      have hne : candidate ≠ node := by
        intro h
        exact hnotData.1 h
      have hcandidateMid : candidate ∈ mid.frontier :=
        frontierStepNode_frontier_of_ne G joint hcandidate hne hmid
      have hkernelMid :
          G.internalKernel candidate mid.result =
            G.internalKernel candidate current.result :=
        frontierStepNode_preserves_internalKernel_of_ne
          G hsound joint hmid hcandidate hne
      exact (ih hcandidateMid hnotData.2 hdstRest).trans hkernelMid

/-- A legal player action for a source-frontier node remains available after
recording any disjoint subset of the same source frontier. -/
theorem available_after_withNodePatches_of_not_mem
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (cfg : G.Configuration)
    {nodes : Finset G.Node}
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → G.FieldPatch)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode))
    {who : Player} {action : PlayerAction G who}
    (hnotmem : action.node ∉ nodes)
    (haction : action ∈ available G cfg who) :
    action ∈ available G
      (cfg.withNodePatches nodes hsubset patch hlegal) who := by
  classical
  induction nodes using Finset.induction with
  | empty =>
      simpa [Configuration.withNodePatches] using haction
  | @insert first rest hfirstNotRest ih =>
      have hrestSubset : rest ⊆ cfg.frontier := by
        intro candidate hcandidate
        exact hsubset (Finset.mem_insert_of_mem hcandidate)
      let restPatch : ∀ node, node ∈ rest → G.FieldPatch :=
        fun node hnode => patch node (Finset.mem_insert_of_mem hnode)
      have hrestLegal :
          ∀ node hnode, G.patchLegal node (restPatch node hnode) := by
        intro node hnode
        exact hlegal node (Finset.mem_insert_of_mem hnode)
      have hactionRest :
          action ∈ available G
            (cfg.withNodePatches rest hrestSubset restPatch hrestLegal) who :=
        ih hrestSubset restPatch hrestLegal
          (by
            intro hmem
            exact hnotmem (Finset.mem_insert_of_mem hmem))
      have hfirstFrontier : first ∈ cfg.frontier :=
        hsubset (Finset.mem_insert_self first rest)
      have hfirstCurrent :
          first ∈
            (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).frontier :=
        cfg.withNodePatches_mem_frontier_of_not_mem
          hrestSubset restPatch hrestLegal hfirstFrontier hfirstNotRest
      let firstPatch : G.FieldPatch :=
        patch first (Finset.mem_insert_self first rest)
      have hfirstLegal : G.patchLegal first firstPatch := by
        exact hlegal first (Finset.mem_insert_self first rest)
      have hne : action.node ≠ first := by
        intro heq
        apply hnotmem
        simp [heq]
      have hafter :
          action ∈ available G
            ((cfg.withNodePatches rest hrestSubset restPatch hrestLegal).withPatch
              firstPatch hfirstCurrent hfirstLegal) who :=
        hsound.actionStable
          (cfg.withNodePatches rest hrestSubset restPatch hrestLegal)
          hfirstCurrent hactionRest.1 hne hfirstLegal hactionRest
      let insertedPatch :
          ∀ candidate, candidate ∈ insert first rest → G.FieldPatch :=
        fun candidate hcandidate =>
          if h : candidate = first then
            firstPatch
          else
            restPatch candidate (by
              rcases Finset.mem_insert.mp hcandidate with hmem | hmem
              · exact False.elim (h hmem)
              · exact hmem)
      have insertedLegal :
          ∀ candidate hcandidate,
            G.patchLegal candidate (insertedPatch candidate hcandidate) := by
        intro candidate hcandidate
        dsimp [insertedPatch]
        split
        · subst candidate
          exact hfirstLegal
        · rename_i hneCandidate
          exact hrestLegal candidate (by
            rcases Finset.mem_insert.mp hcandidate with hmem | hmem
            · exact False.elim (hneCandidate hmem)
            · exact hmem)
      have hinsertEq :
          (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).withPatch
              firstPatch hfirstCurrent hfirstLegal =
            cfg.withNodePatches (insert first rest) hsubset
              insertedPatch insertedLegal := by
        simpa [firstPatch, restPatch, insertedPatch, insertedLegal] using
          (cfg.withNodePatches_insert_eq_withPatch
            hrestSubset restPatch hrestLegal hfirstFrontier
            hfirstNotRest firstPatch hfirstLegal)
      have hpatchCongr :
          cfg.withNodePatches (insert first rest) hsubset
              insertedPatch insertedLegal =
            cfg.withNodePatches (insert first rest) hsubset
              patch hlegal := by
        apply Configuration.withNodePatches_congr
        intro candidate hc₁ hc₂
        dsimp [insertedPatch, restPatch, firstPatch]
        by_cases hcandidate : candidate = first
        · subst candidate
          simp
        · simp [hcandidate]
      simpa [hinsertEq, hpatchCongr] using hafter

/-- Internal kernels for a source-frontier node are unchanged after recording
any disjoint subset of the same source frontier. -/
theorem internalKernel_after_withNodePatches_of_not_mem
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    (cfg : G.Configuration)
    {nodes : Finset G.Node}
    (hsubset : nodes ⊆ cfg.frontier)
    (patch : ∀ node, node ∈ nodes → G.FieldPatch)
    (hlegal : ∀ node hnode, G.patchLegal node (patch node hnode))
    {candidate : G.Node}
    (hcandidate : candidate ∈ cfg.frontier)
    (hnotmem : candidate ∉ nodes) :
    G.internalKernel candidate
        (cfg.withNodePatches nodes hsubset patch hlegal).result =
      G.internalKernel candidate cfg.result := by
  classical
  induction nodes using Finset.induction with
  | empty =>
      simp [Configuration.withNodePatches]
  | @insert first rest hfirstNotRest ih =>
      have hrestSubset : rest ⊆ cfg.frontier := by
        intro node hnode
        exact hsubset (Finset.mem_insert_of_mem hnode)
      let restPatch : ∀ node, node ∈ rest → G.FieldPatch :=
        fun node hnode => patch node (Finset.mem_insert_of_mem hnode)
      have hrestLegal :
          ∀ node hnode, G.patchLegal node (restPatch node hnode) := by
        intro node hnode
        exact hlegal node (Finset.mem_insert_of_mem hnode)
      have hkernelRest :
          G.internalKernel candidate
              (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).result =
            G.internalKernel candidate cfg.result :=
        ih hrestSubset restPatch hrestLegal
          (by
            intro hmem
            exact hnotmem (Finset.mem_insert_of_mem hmem))
      have hfirstFrontier : first ∈ cfg.frontier :=
        hsubset (Finset.mem_insert_self first rest)
      have hfirstCurrent :
          first ∈
            (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).frontier :=
        cfg.withNodePatches_mem_frontier_of_not_mem
          hrestSubset restPatch hrestLegal hfirstFrontier hfirstNotRest
      have hcandidateCurrent :
          candidate ∈
            (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).frontier :=
        cfg.withNodePatches_mem_frontier_of_not_mem
          hrestSubset restPatch hrestLegal hcandidate
          (by
            intro hmem
            exact hnotmem (Finset.mem_insert_of_mem hmem))
      let firstPatch : G.FieldPatch :=
        patch first (Finset.mem_insert_self first rest)
      have hfirstLegal : G.patchLegal first firstPatch :=
        hlegal first (Finset.mem_insert_self first rest)
      have hne : candidate ≠ first := by
        intro heq
        apply hnotmem
        simp [heq]
      have hkernelStep :
          G.internalKernel candidate
              (((cfg.withNodePatches rest hrestSubset restPatch hrestLegal).withPatch
                firstPatch hfirstCurrent hfirstLegal).result) =
            G.internalKernel candidate
              (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).result :=
        hsound.internalKernelStable
          (cfg.withNodePatches rest hrestSubset restPatch hrestLegal)
          hfirstCurrent hcandidateCurrent hne hfirstLegal
      let insertedPatch :
          ∀ candidate, candidate ∈ insert first rest → G.FieldPatch :=
        fun candidate hcandidate =>
          if h : candidate = first then
            firstPatch
          else
            restPatch candidate (by
              rcases Finset.mem_insert.mp hcandidate with hmem | hmem
              · exact False.elim (h hmem)
              · exact hmem)
      have insertedLegal :
          ∀ candidate hcandidate,
            G.patchLegal candidate (insertedPatch candidate hcandidate) := by
        intro node hnode
        dsimp [insertedPatch]
        split
        · subst node
          exact hfirstLegal
        · rename_i hneNode
          exact hrestLegal node (by
            rcases Finset.mem_insert.mp hnode with hmem | hmem
            · exact False.elim (hneNode hmem)
            · exact hmem)
      have hinsertEq :
          (cfg.withNodePatches rest hrestSubset restPatch hrestLegal).withPatch
              firstPatch hfirstCurrent hfirstLegal =
            cfg.withNodePatches (insert first rest) hsubset
              insertedPatch insertedLegal := by
        simpa [firstPatch, restPatch, insertedPatch, insertedLegal] using
          (cfg.withNodePatches_insert_eq_withPatch
            hrestSubset restPatch hrestLegal hfirstFrontier
            hfirstNotRest firstPatch hfirstLegal)
      have hpatchCongr :
          cfg.withNodePatches (insert first rest) hsubset
              insertedPatch insertedLegal =
            cfg.withNodePatches (insert first rest) hsubset
              patch hlegal := by
        apply Configuration.withNodePatches_congr
        intro node h₁ h₂
        dsimp [insertedPatch, restPatch, firstPatch]
        by_cases hnode : node = first
        · subst node
          simp
        · simp [hnode]
      rw [← hpatchCongr, ← hinsertEq]
      exact hkernelStep.trans hkernelRest

private theorem scheduledFrontierTransitionGo_result_eq_of_not_mem
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerFrontierAction G))
    {candidate : G.Node}
    (nodes : List G.Node)
    {current dst : G.Configuration}
    (hnotmem : candidate ∉ nodes)
    (hsupp : dst ∈ (scheduledFrontierTransitionGo G joint nodes current).support) :
    dst.result candidate = current.result candidate := by
  classical
  induction nodes generalizing current with
  | nil =>
      have hdst : dst = current := by
        simpa [scheduledFrontierTransitionGo] using hsupp
      subst dst
      rfl
  | cons node rest ih =>
      simp only [scheduledFrontierTransitionGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨mid, hmid, hdst⟩
      have hne : candidate ≠ node := by
        intro h
        subst candidate
        exact hnotmem (by simp)
      have hnotmemRest : candidate ∉ rest := by
        intro hmem
        exact hnotmem (List.mem_cons_of_mem _ hmem)
      calc
        dst.result candidate = mid.result candidate :=
          ih hnotmemRest hdst
        _ = current.result candidate :=
          frontierStepNode_result_eq_of_ne G joint hne hmid

private theorem realizedNodeEvent_eq_of_result_eq
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node) {left right : G.Configuration}
    (hresult : left.result node = right.result node) :
    realizedNodeEvent G iface joint node left =
      realizedNodeEvent G iface joint node right := by
  classical
  cases hactor : (G.sem node).actor with
  | none =>
      simp [realizedNodeEvent, hactor, hresult]
  | some who =>
      cases hmove : joint who <;>
        simp [realizedNodeEvent, hactor, hmove]

private theorem explicitFrontierBatchStep_support_of_frontierStepNode
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    {node : G.Node}
    {events : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hfrontier : node ∈ current.frontier)
    (hnext : next ∈ (frontierStepNode G joint node current).support) :
    (events ++ [realizedNodeEvent G iface joint node next], next) ∈
      (explicitFrontierBatchStep G iface joint node
        (events, current)).support := by
  classical
  rw [explicitFrontierBatchStep_eq_map_frontierStepNode_of_frontier
    G iface joint node events current hfrontier]
  exact (PMF.mem_support_map_iff _ _ _).2 ⟨next, hnext, rfl⟩

private theorem explicitFrontierBatchStep_support_runEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node)
    {events events' : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hsupp :
      (events', next) ∈
        (explicitFrontierBatchStep G iface joint node
          (events, current)).support) :
    ∃ event : (G.toMachine iface).Event,
      events' = events ++ [event] ∧
        next ∈ ((G.toMachine iface).step event current).support := by
  classical
  cases hactor : (G.sem node).actor with
  | some who =>
      cases hmove : joint who with
      | none =>
          have hdist :
              explicitFrontierBatchStep G iface joint node (events, current) =
                PMF.pure
                  (events ++ [Machine.Event.internal InternalEvent.idle],
                    current) := by
            unfold explicitFrontierBatchStep
            rw [hactor]
            simp [hmove]
          rw [hdist] at hsupp
          have hpair : (events', next) =
              (events ++ [Machine.Event.internal InternalEvent.idle], current) := by
            exact (PMF.mem_support_pure_iff
              (events ++ [Machine.Event.internal InternalEvent.idle], current)
              (events', next)).mp hsupp
          have hevents :
              events' = events ++ [Machine.Event.internal InternalEvent.idle] :=
            congrArg Prod.fst hpair
          have hnext : next = current := congrArg Prod.snd hpair
          subst events'
          subst next
          refine ⟨Machine.Event.internal InternalEvent.idle, rfl, ?_⟩
          simp only [Machine.step, toMachine, stepInternal, PMF.support_pure]
          exact Set.mem_singleton current
      | some action =>
          let event :=
            playerPrimitiveEvent G iface who node (action.patch node)
          have hdist :
              explicitFrontierBatchStep G iface joint node (events, current) =
                PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current) := by
            unfold explicitFrontierBatchStep
            rw [hactor]
            simp [hmove, event, playerPrimitiveEvent]
          rw [hdist] at hsupp
          have hsuppMap :
              (events', next) ∈
                (PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current)).support := hsupp
          rcases (PMF.mem_support_map_iff _ _ _).mp hsuppMap with
            ⟨next', hnext', hpair⟩
          have hevents : events' = events ++ [event] :=
            (congrArg Prod.fst hpair).symm
          have hnext : next = next' := (congrArg Prod.snd hpair).symm
          subst events'
          subst next
          refine ⟨event, rfl, ?_⟩
          simpa [event, playerPrimitiveEvent, Machine.step, toMachine] using hnext'
  | none =>
      by_cases hfrontier : node ∈ current.frontier
      · have hsuppBind :
            (events', next) ∈
              ((G.internalKernel node current.result).bind fun patch =>
                PMF.map
                  (fun next =>
                    (events ++ [internalPrimitiveEvent G iface node patch],
                      next))
                  (stepInternal G (InternalEvent.node node patch)
                    current)).support := by
          have hdist :
              explicitFrontierBatchStep G iface joint node (events, current) =
                (G.internalKernel node current.result).bind fun patch =>
                  PMF.map
                    (fun next =>
                      (events ++ [internalPrimitiveEvent G iface node patch],
                        next))
                    (stepInternal G (InternalEvent.node node patch)
                      current) := by
            unfold explicitFrontierBatchStep
            rw [hactor]
            simp [hfrontier]
          simpa [hdist] using hsupp
        rw [PMF.mem_support_bind_iff] at hsuppBind
        rcases hsuppBind with ⟨patch, _hpatch, hstepMap⟩
        rcases (PMF.mem_support_map_iff _ _ _).mp hstepMap with
          ⟨next', hnext', hpair⟩
        have hevents :
            events' = events ++ [internalPrimitiveEvent G iface node patch] :=
          (congrArg Prod.fst hpair).symm
        have hnext : next = next' := (congrArg Prod.snd hpair).symm
        subst events'
        subst next
        refine ⟨internalPrimitiveEvent G iface node patch, rfl, ?_⟩
        simpa [internalPrimitiveEvent, Machine.step, toMachine] using hnext'
      · have hpair : (events', next) =
            (events ++ [Machine.Event.internal InternalEvent.idle], current) := by
          have hdist :
              explicitFrontierBatchStep G iface joint node (events, current) =
                PMF.pure
                  (events ++ [Machine.Event.internal InternalEvent.idle],
                    current) := by
            unfold explicitFrontierBatchStep
            rw [hactor]
            simp [hfrontier]
          rw [hdist] at hsupp
          exact (PMF.mem_support_pure_iff
            (events ++ [Machine.Event.internal InternalEvent.idle], current)
            (events', next)).mp hsupp
        have hevents :
            events' = events ++ [Machine.Event.internal InternalEvent.idle] :=
          congrArg Prod.fst hpair
        have hnext : next = current := congrArg Prod.snd hpair
        subst events'
        subst next
        refine ⟨Machine.Event.internal InternalEvent.idle, rfl, ?_⟩
        simp only [Machine.step, toMachine, stepInternal, PMF.support_pure]
        exact Set.mem_singleton current

private theorem explicitFrontierBatchStep_support_availableRunEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) source joint)
    (node : G.Node)
    {events events' : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hcurrentAvailable :
      ∀ {who : Player} {action : PlayerAction G who},
        action.node = node →
        action ∈ available G source who →
          action ∈ available G current who)
    (hcurrent : node ∈ current.frontier)
    (hsource : node ∈ source.frontier)
    (hsupp :
      (events', next) ∈
        (explicitFrontierBatchStep G iface joint node
          (events, current)).support) :
    ∃ event : (G.toMachine iface).Event,
      events' = events ++ [event] ∧
        (G.toMachine iface).EventAvailable current event ∧
          next ∈ ((G.toMachine iface).step event current).support := by
  classical
  cases hactor : (G.sem node).actor with
  | some who =>
      have hactive : who ∈ frontierActive G source := by
        rw [mem_frontierActive_iff]
        exact ⟨node, hsource, hactor⟩
      have hlocal := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G source := by
            simpa [hmove] using hlocal
          exact False.elim (hnot hactive)
      | some action =>
          let event :=
            playerPrimitiveEvent G iface who node (action.patch node)
          have hdist :
              explicitFrontierBatchStep G iface joint node (events, current) =
                PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current) := by
            unfold explicitFrontierBatchStep
            rw [hactor]
            simp [hmove, event, playerPrimitiveEvent]
          rw [hdist] at hsupp
          rcases (PMF.mem_support_map_iff _ _ _).mp hsupp with
            ⟨next', hnext', hpair⟩
          have hevents : events' = events ++ [event] :=
            (congrArg Prod.fst hpair).symm
          have hnext : next = next' := (congrArg Prod.snd hpair).symm
          subst events'
          subst next
          have hsourceAction :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G source who := by
            have hpair :
                who ∈ frontierActive G source ∧
                  action ∈ frontierAvailable G source who := by
              simpa [hmove] using hlocal
            have hnodeLegal := hpair.2 hsource hactor
            exact ⟨hsource, hactor, hnodeLegal.1, hnodeLegal.2⟩
          have hcurrentAction :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G current who :=
            hcurrentAvailable rfl hsourceAction
          refine ⟨event, rfl, ?_, ?_⟩
          · simpa [event, playerPrimitiveEvent, toMachine]
          · simpa [event, playerPrimitiveEvent, Machine.step, toMachine] using hnext'
  | none =>
      have hdist :
          explicitFrontierBatchStep G iface joint node (events, current) =
            (G.internalKernel node current.result).bind fun patch =>
              PMF.map
                (fun next =>
                  (events ++ [internalPrimitiveEvent G iface node patch],
                    next))
                (stepInternal G (InternalEvent.node node patch)
                  current) := by
        unfold explicitFrontierBatchStep
        rw [hactor]
        simp [hcurrent]
      rw [hdist] at hsupp
      rw [PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨patch, hpatch, hstepMap⟩
      rcases (PMF.mem_support_map_iff _ _ _).mp hstepMap with
        ⟨next', hnext', hpair⟩
      have hevents :
          events' = events ++ [internalPrimitiveEvent G iface node patch] :=
        (congrArg Prod.fst hpair).symm
      have hnext : next = next' := (congrArg Prod.snd hpair).symm
      subst events'
      subst next
      let event := internalPrimitiveEvent G iface node patch
      have havailable :
          (G.toMachine iface).EventAvailable current event := by
        change
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current
        exact ⟨hcurrent, hactor, hpatch⟩
      refine ⟨event, rfl, havailable, ?_⟩
      simpa [event, internalPrimitiveEvent, Machine.step, toMachine] using hnext'

private theorem explicitFrontierBatchStep_support_no_idle
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node)
    {events events' : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hcurrent : node ∈ current.frontier)
    (hsource : node ∈ source.frontier)
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) source joint)
    (hnoEvents :
      (Machine.Event.internal InternalEvent.idle :
        (G.toMachine iface).Event) ∉ events)
    (hsupp :
      (events', next) ∈
        (explicitFrontierBatchStep G iface joint node
          (events, current)).support) :
    (Machine.Event.internal InternalEvent.idle :
      (G.toMachine iface).Event) ∉ events' := by
  classical
  cases hactor : (G.sem node).actor with
  | some who =>
      have hactive : who ∈ frontierActive G source := by
        rw [mem_frontierActive_iff]
        exact ⟨node, hsource, hactor⟩
      have hlocal := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G source := by
            simpa [hmove] using hlocal
          exact False.elim (hnot hactive)
      | some action =>
          let event :=
            playerPrimitiveEvent G iface who node (action.patch node)
          have hdist :
              explicitFrontierBatchStep G iface joint node (events, current) =
                PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current) := by
            unfold explicitFrontierBatchStep
            rw [hactor]
            simp [hmove, event, playerPrimitiveEvent]
          rw [hdist] at hsupp
          rcases (PMF.mem_support_map_iff _ _ _).mp hsupp with
            ⟨next', _hnext', hpair⟩
          have hevents : events' = events ++ [event] :=
            (congrArg Prod.fst hpair).symm
          subst events'
          intro hidle
          rw [List.mem_append] at hidle
          rcases hidle with hidle | hidle
          · exact hnoEvents hidle
          · simp [event, playerPrimitiveEvent] at hidle
  | none =>
      by_cases hfrontier : node ∈ current.frontier
      · have hdist :
            explicitFrontierBatchStep G iface joint node (events, current) =
              (G.internalKernel node current.result).bind fun patch =>
                PMF.map
                  (fun next =>
                    (events ++ [internalPrimitiveEvent G iface node patch],
                      next))
                  (stepInternal G (InternalEvent.node node patch)
                    current) := by
          unfold explicitFrontierBatchStep
          rw [hactor]
          simp [hfrontier]
        rw [hdist] at hsupp
        rw [PMF.mem_support_bind_iff] at hsupp
        rcases hsupp with ⟨patch, _hpatch, hstepMap⟩
        rcases (PMF.mem_support_map_iff _ _ _).mp hstepMap with
          ⟨next', _hnext', hpair⟩
        have hevents :
            events' = events ++ [internalPrimitiveEvent G iface node patch] :=
          (congrArg Prod.fst hpair).symm
        subst events'
        intro hidle
        rw [List.mem_append] at hidle
        rcases hidle with hidle | hidle
        · exact hnoEvents hidle
        · simp [internalPrimitiveEvent] at hidle
      · exact False.elim (hfrontier hcurrent)

private theorem explicitFrontierBatchGo_support_runEventsFrom_suffix
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G)) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      (current : G.Configuration)
      {batch : List (G.toMachine iface).Event}
      {dst : G.Configuration},
      (batch, dst) ∈
        (explicitFrontierBatchGo G iface joint nodes events current).support →
        ∃ suffix : List (G.toMachine iface).Event,
          batch = events ++ suffix ∧
            dst ∈
              ((G.toMachine iface).runEventsFrom suffix current).support
  | [], events, current, batch, dst, hsupp => by
      have hpure :
          (batch, dst) ∈ (PMF.pure (events, current)).support := by
        simpa [explicitFrontierBatchGo] using hsupp
      have hpair : (batch, dst) = (events, current) :=
        (PMF.mem_support_pure_iff (events, current) (batch, dst)).mp hpure
      have hbatch : batch = events := congrArg Prod.fst hpair
      have hdst : dst = current := congrArg Prod.snd hpair
      subst batch
      subst dst
      refine ⟨[], by simp, ?_⟩
      simp only [Machine.runEventsFrom_nil, PMF.support_pure]
      exact Set.mem_singleton current
  | node :: rest, events, current, batch, dst, hsupp => by
      classical
      simp only [explicitFrontierBatchGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨next, hstepMass, hrestMass⟩
      rcases next with ⟨events₁, mid⟩
      have hstepSupport :
          (events₁, mid) ∈
            (explicitFrontierBatchStep G iface joint node
              (events, current)).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      have hrestSupport :
          (batch, dst) ∈
            (explicitFrontierBatchGo G iface joint rest events₁ mid).support :=
        (PMF.mem_support_iff _ _).2 hrestMass
      rcases explicitFrontierBatchStep_support_runEvent
          G iface joint node hstepSupport with
        ⟨event, hevents₁, hstep⟩
      rcases explicitFrontierBatchGo_support_runEventsFrom_suffix
          G iface joint rest events₁ mid hrestSupport with
        ⟨suffix, hbatch, hrunRest⟩
      subst events₁
      refine ⟨[event] ++ suffix, ?_, ?_⟩
      · simpa [List.append_assoc] using hbatch
      · rw [Machine.runEventsFrom_append]
        have hfirst :
            mid ∈
              ((G.toMachine iface).runEventsFrom [event] current).support := by
          simpa [Machine.runEventsFrom] using hstep
        exact (PMF.mem_support_bind_iff
          (p := (G.toMachine iface).runEventsFrom [event] current)
          (f := fun current =>
            (G.toMachine iface).runEventsFrom suffix current)
          dst).2 ⟨mid, hfirst, hrunRest⟩

private theorem explicitFrontierBatchGo_support_availableRunFrom_suffix
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hsound : G.HasLocalFrontierSteps)
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) source joint) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      (current : G.Configuration)
      {batch : List (G.toMachine iface).Event}
      {dst : G.Configuration},
      nodes.Nodup →
      (∀ node, node ∈ nodes → node ∈ source.frontier) →
      (∀ node, node ∈ nodes → node ∈ current.frontier) →
      (∀ {who : Player} {action : PlayerAction G who},
        action.node ∈ nodes →
        action ∈ available G source who →
          action ∈ available G current who) →
      (batch, dst) ∈
        (explicitFrontierBatchGo G iface joint nodes events current).support →
        ∃ suffix : List (G.toMachine iface).Event,
          batch = events ++ suffix ∧
            (G.toMachine iface).AvailableRunFrom current suffix dst
  | [], events, current, batch, dst, _hnodup, _hsource, _hcurrent,
      _havailable, hsupp => by
      have hpure :
          (batch, dst) ∈ (PMF.pure (events, current)).support := by
        simpa [explicitFrontierBatchGo] using hsupp
      have hpair : (batch, dst) = (events, current) :=
        (PMF.mem_support_pure_iff (events, current) (batch, dst)).mp hpure
      have hbatch : batch = events := congrArg Prod.fst hpair
      have hdst : dst = current := congrArg Prod.snd hpair
      subst batch
      subst dst
      exact ⟨[], by simp, Machine.AvailableRunFrom.nil _⟩
  | node :: rest, events, current, batch, dst, hnodup, hsource,
      hcurrent, havailable, hsupp => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      simp only [explicitFrontierBatchGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨next, hstepMass, hrestMass⟩
      rcases next with ⟨events₁, mid⟩
      have hstepSupport :
          (events₁, mid) ∈
            (explicitFrontierBatchStep G iface joint node
              (events, current)).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      have hrestSupport :
          (batch, dst) ∈
            (explicitFrontierBatchGo G iface joint rest events₁ mid).support :=
        (PMF.mem_support_iff _ _).2 hrestMass
      have hnodeCurrent : node ∈ current.frontier :=
        hcurrent node (by simp)
      have hnodeSource : node ∈ source.frontier :=
        hsource node (by simp)
      rcases explicitFrontierBatchStep_support_availableRunEvent
          G iface source joint hlegal node
          (fun hnode haction => havailable (by simp [hnode]) haction)
          hnodeCurrent hnodeSource hstepSupport with
        ⟨event, hevents₁, heventAvailable, hstep⟩
      have hmidFrontierStep :
          mid ∈ (frontierStepNode G joint node current).support := by
        have hstepSupport' := hstepSupport
        rw [explicitFrontierBatchStep_eq_map_frontierStepNode_of_frontier
          G iface joint node events current hnodeCurrent] at hstepSupport'
        rcases (PMF.mem_support_map_iff _ _ _).mp hstepSupport' with
          ⟨mid', hmid', hpair⟩
        have hmidEq : mid = mid' := (congrArg Prod.snd hpair).symm
        subst mid
        exact hmid'
      have hrestSource :
          ∀ candidate, candidate ∈ rest → candidate ∈ source.frontier := by
        intro candidate hcandidate
        exact hsource candidate (List.mem_cons_of_mem _ hcandidate)
      have hrestCurrent :
          ∀ candidate, candidate ∈ rest → candidate ∈ mid.frontier := by
        intro candidate hcandidate
        have hcandidateCurrent :
            candidate ∈ current.frontier :=
          hcurrent candidate (List.mem_cons_of_mem _ hcandidate)
        have hne : candidate ≠ node := by
          intro h
          subst candidate
          exact hnodeNotRest hcandidate
        exact frontierStepNode_frontier_of_ne
          G joint hcandidateCurrent hne hmidFrontierStep
      have havailableMid :
          ∀ {who : Player} {action : PlayerAction G who},
            action.node ∈ rest →
            action ∈ available G source who →
              action ∈ available G mid who := by
        intro who action hmemRest hactionSource
        have hactionCurrent : action ∈ available G current who :=
          havailable (List.mem_cons_of_mem _ hmemRest) hactionSource
        have hne : action.node ≠ node := by
          intro h
          subst node
          exact hnodeNotRest hmemRest
        exact frontierStepNode_preserves_available_of_ne
          G hsound joint hmidFrontierStep hne hactionCurrent
      subst events₁
      rcases explicitFrontierBatchGo_support_availableRunFrom_suffix
          G iface source joint hsound hlegal rest
          (events ++ [event]) mid
          hrestNodup hrestSource hrestCurrent havailableMid
          hrestSupport with
        ⟨suffix, hbatch, hrun⟩
      refine ⟨[event] ++ suffix, ?_, ?_⟩
      · simpa [List.append_assoc] using hbatch
      · exact Machine.AvailableRunFrom.cons heventAvailable hstep hrun

private theorem explicitFrontierBatchGo_support_of_scheduledFrontierTransitionGo_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G)) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      {current dst : G.Configuration},
      nodes.Nodup →
      (∀ node, node ∈ nodes → node ∈ current.frontier) →
      dst ∈ (scheduledFrontierTransitionGo G joint nodes current).support →
        (events ++ nodes.map (fun node =>
          realizedNodeEvent G iface joint node dst), dst) ∈
          (explicitFrontierBatchGo G iface joint nodes events current).support
  | [], events, current, dst, _hnodup, _hfrontier, hdst => by
      have hdstEq : dst = current := by
        simpa [scheduledFrontierTransitionGo] using hdst
      subst dst
      simp [explicitFrontierBatchGo]
  | node :: rest, events, current, dst, hnodup, hfrontier, hdst => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      simp only [scheduledFrontierTransitionGo, PMF.mem_support_bind_iff] at hdst
      rcases hdst with ⟨mid, hmid, hdstRest⟩
      have hnodeFrontier : node ∈ current.frontier :=
        hfrontier node (by simp)
      have hstepSupport :
          (events ++ [realizedNodeEvent G iface joint node mid], mid) ∈
            (explicitFrontierBatchStep G iface joint node
              (events, current)).support :=
        explicitFrontierBatchStep_support_of_frontierStepNode
          G iface joint hnodeFrontier hmid
      have hrestFrontier :
          ∀ candidate, candidate ∈ rest → candidate ∈ mid.frontier := by
        intro candidate hcandidate
        have hcandidateFrontier :
            candidate ∈ current.frontier :=
          hfrontier candidate (List.mem_cons_of_mem _ hcandidate)
        have hne : candidate ≠ node := by
          intro h
          subst candidate
          exact hnodeNotRest hcandidate
        exact frontierStepNode_frontier_of_ne
          G joint hcandidateFrontier hne hmid
      have hrestSupport :
          ((events ++ [realizedNodeEvent G iface joint node mid]) ++
              rest.map (fun node =>
                realizedNodeEvent G iface joint node dst), dst) ∈
            (explicitFrontierBatchGo G iface joint rest
              (events ++ [realizedNodeEvent G iface joint node mid])
              mid).support :=
        explicitFrontierBatchGo_support_of_scheduledFrontierTransitionGo_support
          G iface joint rest
          (events ++ [realizedNodeEvent G iface joint node mid])
          hrestNodup hrestFrontier hdstRest
      have hresult :
          dst.result node = mid.result node :=
        scheduledFrontierTransitionGo_result_eq_of_not_mem
          G joint rest hnodeNotRest hdstRest
      have hevent :
          realizedNodeEvent G iface joint node mid =
            realizedNodeEvent G iface joint node dst :=
        realizedNodeEvent_eq_of_result_eq
          G iface joint node hresult.symm
      change
        (events ++
            (node :: rest).map
              (fun node => realizedNodeEvent G iface joint node dst),
          dst) ∈
          ((explicitFrontierBatchStep G iface joint node (events, current)).bind
            fun next =>
              explicitFrontierBatchGo G iface joint rest next.1 next.2).support
      rw [PMF.mem_support_bind_iff]
      refine ⟨(events ++ [realizedNodeEvent G iface joint node mid], mid),
        hstepSupport, ?_⟩
      simpa [List.map, List.append_assoc, hevent] using hrestSupport

private theorem explicitFrontierBatchGo_eq_map_scheduledFrontierTransitionGo
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G)) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      {current : G.Configuration},
      nodes.Nodup →
      (∀ node, node ∈ nodes → node ∈ current.frontier) →
        PMF.map
            (fun dst =>
              (events ++ nodes.map (fun node =>
                realizedNodeEvent G iface joint node dst), dst))
            (scheduledFrontierTransitionGo G joint nodes current) =
          explicitFrontierBatchGo G iface joint nodes events current
  | [], events, current, _hnodup, _hfrontier => by
      simp [scheduledFrontierTransitionGo, explicitFrontierBatchGo, PMF.pure_map]
  | node :: rest, events, current, hnodup, hfrontier => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      have hnodeFrontier : node ∈ current.frontier :=
        hfrontier node (by simp)
      rw [scheduledFrontierTransitionGo, explicitFrontierBatchGo]
      rw [explicitFrontierBatchStep_eq_map_frontierStepNode_of_frontier
        G iface joint node events current hnodeFrontier]
      rw [PMF.map_bind]
      rw [PMF.bind_map]
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (frontierStepNode G joint node current) _ _ ?_
      intro mid hmid
      have hrestFrontier :
          ∀ candidate, candidate ∈ rest → candidate ∈ mid.frontier := by
        intro candidate hcandidate
        have hcandidateFrontier :
            candidate ∈ current.frontier :=
          hfrontier candidate (List.mem_cons_of_mem _ hcandidate)
        have hne : candidate ≠ node := by
          intro h
          subst candidate
          exact hnodeNotRest hcandidate
        exact frontierStepNode_frontier_of_ne
          G joint hcandidateFrontier hne hmid
      have hmap :
          PMF.map
              (fun dst =>
                (events ++ (node :: rest).map (fun node =>
                  realizedNodeEvent G iface joint node dst), dst))
              (scheduledFrontierTransitionGo G joint rest mid) =
            PMF.map
              (fun dst =>
                ((events ++ [realizedNodeEvent G iface joint node mid]) ++
                  rest.map (fun node =>
                    realizedNodeEvent G iface joint node dst), dst))
              (scheduledFrontierTransitionGo G joint rest mid) := by
        rw [← PMF.bind_pure_comp
          (fun dst =>
            (events ++ (node :: rest).map (fun node =>
              realizedNodeEvent G iface joint node dst), dst))]
        rw [← PMF.bind_pure_comp
          (fun dst =>
            ((events ++ [realizedNodeEvent G iface joint node mid]) ++
              rest.map (fun node =>
                realizedNodeEvent G iface joint node dst), dst))]
        refine Math.ProbabilityMassFunction.bind_congr_on_support
          (scheduledFrontierTransitionGo G joint rest mid) _ _ ?_
        intro dst hdst
        have hresult :
            dst.result node = mid.result node :=
          scheduledFrontierTransitionGo_result_eq_of_not_mem
            G joint rest hnodeNotRest hdst
        have hevent :
            realizedNodeEvent G iface joint node dst =
              realizedNodeEvent G iface joint node mid :=
          realizedNodeEvent_eq_of_result_eq
            G iface joint node hresult
        simp [List.map, List.append_assoc, hevent]
      rw [hmap]
      exact explicitFrontierBatchGo_eq_map_scheduledFrontierTransitionGo
        G iface joint rest
        (events ++ [realizedNodeEvent G iface joint node mid])
        hrestNodup hrestFrontier

/-- Stepwise distribution over a realized primitive event batch and destination
of one frontier step. Internal stochastic choices are sampled before their
deterministic primitive event is executed. This is the operational sampler used
to justify the exported decorated event-batch distribution. -/
private noncomputable def explicitFrontierBatchWalk
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G)) :
    PMF (List (G.toMachine iface).Event × G.Configuration) :=
  explicitFrontierBatchGo G iface joint cfg.frontier.toList [] cfg

/-- Extract the realized primitive event batch from a completed round source,
joint action, and destination. For internal nodes, the destination result
determines which patch was realized. -/
noncomputable def realizedEventBatch
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (dst : G.Configuration) :
    List (G.toMachine iface).Event :=
  cfg.frontier.toList.map fun node =>
    realizedNodeEvent G iface joint node dst

private theorem explicitFrontierBatchStep_map_state
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (node : G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration) :
    PMF.map Prod.snd
        (explicitFrontierBatchStep G iface joint node (events, current)) =
      frontierStepNode G joint node current := by
  classical
  unfold explicitFrontierBatchStep frontierStepNode
  cases hactor : (G.sem node).actor with
  | none =>
      by_cases hfrontier : node ∈ current.frontier
      · simp [hfrontier, PMF.map_bind, PMF.map_comp, PMF.map_id]
      · have hnotEnabled : ¬ current.Enabled node := by
          intro henabled
          exact hfrontier ((current.mem_frontier_iff node).mpr henabled)
        simp [hfrontier, hnotEnabled, stepInternal, availableInternal,
          hactor, PMF.pure_map]
  | some who =>
      cases hmove : joint who with
      | none =>
          simp [hmove, PMF.pure_map]
      | some action =>
          simp [hmove, PMF.map_comp, PMF.map_id]

private theorem explicitFrontierBatchGo_support_no_idle
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) source joint) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      {current : G.Configuration}
      {batch : List (G.toMachine iface).Event}
      {dst : G.Configuration},
      nodes.Nodup →
      (∀ node, node ∈ nodes → node ∈ source.frontier) →
      (∀ node, node ∈ nodes → node ∈ current.frontier) →
      (Machine.Event.internal InternalEvent.idle :
        (G.toMachine iface).Event) ∉ events →
      (batch, dst) ∈
        (explicitFrontierBatchGo G iface joint nodes events current).support →
        (Machine.Event.internal InternalEvent.idle :
          (G.toMachine iface).Event) ∉ batch
  | [], events, current, batch, dst, _hnodup, _hsource, _hcurrent,
      hnoEvents, hsupp => by
      have hpure :
          (batch, dst) ∈ (PMF.pure (events, current)).support := by
        simpa [explicitFrontierBatchGo] using hsupp
      have hpair : (batch, dst) = (events, current) :=
        (PMF.mem_support_pure_iff (events, current) (batch, dst)).mp hpure
      have hbatch : batch = events := congrArg Prod.fst hpair
      subst batch
      exact hnoEvents
  | node :: rest, events, current, batch, dst, hnodup, hsource,
      hcurrent, hnoEvents, hsupp => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      simp only [explicitFrontierBatchGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨next, hstepMass, hrestMass⟩
      rcases next with ⟨events₁, mid⟩
      have hstepSupport :
          (events₁, mid) ∈
            (explicitFrontierBatchStep G iface joint node
              (events, current)).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      have hrestSupport :
          (batch, dst) ∈
            (explicitFrontierBatchGo G iface joint rest events₁ mid).support :=
        (PMF.mem_support_iff _ _).2 hrestMass
      have hnodeCurrent : node ∈ current.frontier :=
        hcurrent node (by simp)
      have hnodeSource : node ∈ source.frontier :=
        hsource node (by simp)
      have hnoEvents₁ :
          (Machine.Event.internal InternalEvent.idle :
            (G.toMachine iface).Event) ∉ events₁ :=
        explicitFrontierBatchStep_support_no_idle
          G iface source joint node hnodeCurrent hnodeSource hlegal
          hnoEvents hstepSupport
      have hmidFrontierStep :
          mid ∈ (frontierStepNode G joint node current).support := by
        have hmap :
            mid ∈
              (PMF.map Prod.snd
                (explicitFrontierBatchStep G iface joint node
                  (events, current))).support :=
          (PMF.mem_support_map_iff _ _ _).2
            ⟨(events₁, mid), hstepSupport, rfl⟩
        rw [explicitFrontierBatchStep_map_state] at hmap
        exact hmap
      have hrestSource :
          ∀ candidate, candidate ∈ rest → candidate ∈ source.frontier := by
        intro candidate hcandidate
        exact hsource candidate (List.mem_cons_of_mem _ hcandidate)
      have hrestCurrent :
          ∀ candidate, candidate ∈ rest → candidate ∈ mid.frontier := by
        intro candidate hcandidate
        have hcandidateCurrent :
            candidate ∈ current.frontier :=
          hcurrent candidate (List.mem_cons_of_mem _ hcandidate)
        have hne : candidate ≠ node := by
          intro h
          subst candidate
          exact hnodeNotRest hcandidate
        exact frontierStepNode_frontier_of_ne
          G joint hcandidateCurrent hne hmidFrontierStep
      exact explicitFrontierBatchGo_support_no_idle
        G iface source joint hlegal rest events₁ hrestNodup
        hrestSource hrestCurrent hnoEvents₁ hrestSupport

private theorem explicitFrontierBatchGo_map_state
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerFrontierAction G))
    (nodes : List G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration) :
    PMF.map Prod.snd
        (explicitFrontierBatchGo G iface joint nodes events current) =
      scheduledFrontierTransitionGo G joint nodes current := by
  induction nodes generalizing events current with
  | nil =>
      simp [explicitFrontierBatchGo, scheduledFrontierTransitionGo, PMF.pure_map]
  | cons node nodes ih =>
      classical
      rw [explicitFrontierBatchGo, scheduledFrontierTransitionGo]
      rw [PMF.map_bind]
      simp_rw [ih]
      rw [← explicitFrontierBatchStep_map_state G iface joint node events current]
      rw [PMF.bind_map]
      rfl

/-- A concrete linearization of exactly the current source frontier.

The list order is an implementation schedule. Its membership proof says that
the schedule has no semantic content beyond choosing an order in which to
execute the same local frontier. -/
structure FrontierSchedule
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration) where
  nodes : List G.Node
  nodup : nodes.Nodup
  mem_iff : ∀ node, node ∈ nodes ↔ node ∈ cfg.frontier

namespace FrontierSchedule

theorem perm_toCanonical
    {G : Vegas.EventGraph Player L} {cfg : G.Configuration}
    (schedule : FrontierSchedule G cfg) :
    schedule.nodes.Perm cfg.frontier.toList := by
  classical
  refine (List.perm_ext_iff_of_nodup schedule.nodup
    (by simpa using cfg.frontier.nodup_toList)).2 ?_
  intro node
  simp [schedule.mem_iff node]

end FrontierSchedule

/-- Execute a frontier step using an explicit schedule. -/
noncomputable def frontierTransitionWithSchedule
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (schedule : FrontierSchedule G cfg) :
    PMF G.Configuration :=
  scheduledFrontierTransitionGo G joint schedule.nodes cfg

/-- Execute the current frontier in the canonical list order.

This is the scheduled operational representative used for primitive
event-batch witnesses. The native round-view transition is the order-free
`frontierRealizationTransition`; for graph views exposed through
`HasLocalFrontierSteps`, frontier independence justifies treating this
canonical list as proof/execution presentation rather than strategic content. -/
noncomputable def scheduledFrontierTransition
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G)) :
    PMF G.Configuration :=
  scheduledFrontierTransitionGo G joint cfg.frontier.toList cfg

/-- Patch distribution for one order-free frontier coordinate. Player-owned
coordinates are fixed by the legal joint action; internal coordinates use the
graph's internal kernel at the source configuration. -/
noncomputable def frontierPatchDist
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (_hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    (idx : FrontierIndex G cfg) :
    PMF G.FieldPatch :=
  match (G.sem idx.1).actor with
  | some who =>
      match joint who with
      | some action => PMF.pure (action.patch idx.1)
      | none => PMF.pure (FieldPatch.empty G)
  | none => G.internalKernel idx.1 cfg.result

/-- Order-free distribution of one frontier realization. This is the semantic
round payload; list schedules are execution witnesses for samples of this
distribution. -/
noncomputable def frontierRealizationDist
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint) :
    PMF (FrontierRealization G cfg) :=
  PMF.map
    (fun patch : (idx : FrontierIndex G cfg) → G.FieldPatch =>
      { patch := patch })
    (Math.PMFProduct.pmfPi
      (fun idx => frontierPatchDist G cfg joint hlegal idx))

/-- Coordinate support for a sampled order-free frontier realization. -/
theorem frontierRealizationDist_support_coord
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {realization : FrontierRealization G cfg}
    (hsupp : realization ∈
      (frontierRealizationDist G cfg joint hlegal).support)
    (idx : FrontierIndex G cfg) :
    realization.patch idx ∈
      (frontierPatchDist G cfg joint hlegal idx).support := by
  classical
  rcases (PMF.mem_support_map_iff _ _ _).mp hsupp with
    ⟨patches, hpatches, hrealization⟩
  subst realization
  have hmass :
      (Math.PMFProduct.pmfPi
        (fun idx => frontierPatchDist G cfg joint hlegal idx)) patches ≠ 0 :=
    (PMF.mem_support_iff _ _).mp hpatches
  have hprod :
      (∏ idx : FrontierIndex G cfg,
        frontierPatchDist G cfg joint hlegal idx (patches idx)) ≠ 0 := by
    simpa [Math.PMFProduct.pmfPi_apply] using hmass
  have hcoord_ne :
      frontierPatchDist G cfg joint hlegal idx (patches idx) ≠ 0 :=
    (Finset.prod_ne_zero_iff).mp hprod idx (Finset.mem_univ idx)
  exact (PMF.mem_support_iff _ _).mpr hcoord_ne

/-- Every realization sampled by the order-free frontier law carries legal
patches. Player coordinates are legal by the joint-action legality proof;
internal coordinates are legal by `internalKernel_support_legal`. -/
theorem frontierRealizationDist_support_legal
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {realization : FrontierRealization G cfg}
    (hsupp : realization ∈
      (frontierRealizationDist G cfg joint hlegal).support) :
    realization.Legal := by
  classical
  intro idx
  have hcoord :=
    frontierRealizationDist_support_coord G cfg joint hlegal hsupp idx
  cases hactor : (G.sem idx.1).actor with
  | none =>
      have hcoord :
          realization.patch idx ∈
            (G.internalKernel idx.1 cfg.result).support :=
        by simpa [frontierPatchDist, hactor] using hcoord
      exact
        G.internalKernel_support_legal
          (cfg.mem_nodes_of_mem_frontier idx.2)
          (cfg.not_done_of_mem_frontier idx.2)
          (fun prereq hpre =>
            cfg.result_some_of_prereq_of_mem_frontier idx.2 hpre)
          (fun hresult => cfg.legal hresult)
          hactor hcoord
  | some who =>
      have hactive : who ∈ frontierActive G cfg :=
        (mem_frontierActive_iff G cfg who).mpr ⟨idx.1, idx.2, hactor⟩
      have hcoordLegal := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G cfg := by
            simpa [hmove] using hcoordLegal
          exact False.elim (hnot hactive)
      | some action =>
          have hround :
              who ∈ frontierActive G cfg ∧
                action ∈ frontierAvailable G cfg who := by
            simpa [hmove] using hcoordLegal
          have hpatch :
              realization.patch idx = action.patch idx.1 := by
            have hmem :
                realization.patch idx ∈
                  (PMF.pure (action.patch idx.1) : PMF G.FieldPatch).support :=
              by simpa [frontierPatchDist, hactor, hmove] using hcoord
            simpa using
              (PMF.mem_support_pure_iff (action.patch idx.1)
                (realization.patch idx)).mp hmem
          change G.patchLegal idx.1 (realization.patch idx)
          rw [hpatch]
          exact (hround.2 idx.2 hactor).1

/-- A patch sampled by one source-frontier coordinate distribution is legal for
that coordinate. -/
private theorem frontierPatchDist_support_legal
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    (idx : FrontierIndex G cfg)
    {patch : G.FieldPatch}
    (hpatch : patch ∈ (frontierPatchDist G cfg joint hlegal idx).support) :
    G.patchLegal idx.1 patch := by
  classical
  cases hactor : (G.sem idx.1).actor with
  | none =>
      have hkernel : patch ∈ (G.internalKernel idx.1 cfg.result).support := by
        simpa [frontierPatchDist, hactor] using hpatch
      exact
        G.internalKernel_support_legal
          (cfg.mem_nodes_of_mem_frontier idx.2)
          (cfg.not_done_of_mem_frontier idx.2)
          (fun prereq hpre =>
            cfg.result_some_of_prereq_of_mem_frontier idx.2 hpre)
          (fun hresult => cfg.legal hresult)
          hactor hkernel
  | some who =>
      have hactive : who ∈ frontierActive G cfg :=
        (mem_frontierActive_iff G cfg who).mpr ⟨idx.1, idx.2, hactor⟩
      have hcoord := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hround :
              who ∈ frontierActive G cfg ∧
                action ∈ frontierAvailable G cfg who := by
            simpa [hmove] using hcoord
          have hpatchEq : patch = action.patch idx.1 := by
            have hpure :
                patch ∈
                  (PMF.pure (action.patch idx.1) :
                    PMF G.FieldPatch).support := by
              simpa [frontierPatchDist, hactor, hmove] using hpatch
            exact
              (PMF.mem_support_pure_iff
                (action.patch idx.1) patch).mp hpure
          rw [hpatchEq]
          exact (hround.2 idx.2 hactor).1

/-- Combine already-fixed prefix patches with sampled patches for the remaining
source frontier. Coordinates in `done` are read from `donePatch`; every other
source-frontier coordinate is read from `realization`. -/
private noncomputable def combinedFrontierConfig
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    {done : Finset G.Node}
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode))
    (realization : FrontierRealization G cfg)
    (hrealLegal : realization.Legal) :
    G.Configuration :=
  cfg.withFrontierPatches
    (fun node hfrontier =>
      if hdone : node ∈ done then
        donePatch node hdone
      else
        realization.patchAt node hfrontier)
    (fun node hfrontier => by
      by_cases hdone : node ∈ done
      · simpa [hdone] using doneLegal node hdone
      · simpa [hdone] using hrealLegal ⟨node, hfrontier⟩)

private theorem combinedFrontierConfig_empty
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (realization : FrontierRealization G cfg)
    (hrealLegal : realization.Legal) :
    combinedFrontierConfig G cfg (done := ∅)
      (fun _ hnode => False.elim (by simp at hnode))
      (fun _ hnode => False.elim (by simp at hnode))
      realization hrealLegal =
      cfg.extendFrontier realization hrealLegal := by
  classical
  apply Configuration.ext
  funext node
  by_cases hfrontier : node ∈ cfg.frontier
  · simp [combinedFrontierConfig, hfrontier, Configuration.extendFrontier]
  · simp [combinedFrontierConfig, hfrontier, Configuration.extendFrontier]

private theorem combinedFrontierConfig_of_cover
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    (hcover : ∀ node, node ∈ cfg.frontier → node ∈ done)
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode))
    (realization : FrontierRealization G cfg)
    (hrealLegal : realization.Legal) :
    combinedFrontierConfig G cfg donePatch doneLegal realization hrealLegal =
      cfg.withNodePatches done hdoneSubset donePatch doneLegal := by
  classical
  apply Configuration.ext
  funext node
  by_cases hfrontier : node ∈ cfg.frontier
  · have hdone : node ∈ done := hcover node hfrontier
    simp [combinedFrontierConfig, hfrontier, hdone]
  · have hdone : node ∉ done := by
      intro h
      exact hfrontier (hdoneSubset h)
    simp [combinedFrontierConfig, hfrontier, hdone]

/-- A scheduled source-frontier node step is the source coordinate patch law
followed by the deterministic prefix update. -/
private theorem frontierStepNode_withNodePatches_eq_bind_patchDist
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hjoint :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode))
    {node : G.Node}
    (hnodeFrontier : node ∈ cfg.frontier)
    (hnotDone : node ∉ done) :
    let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
    let hcurrentFrontier : node ∈ current.frontier :=
      cfg.withNodePatches_mem_frontier_of_not_mem
        hdoneSubset donePatch doneLegal hnodeFrontier hnotDone
    frontierStepNode G joint node current =
      (by
        classical
        exact
          (frontierPatchDist G cfg joint hjoint
            ⟨node, hnodeFrontier⟩).bind fun patch =>
            if hpatch :
                patch ∈
                  (frontierPatchDist G cfg joint hjoint
                    ⟨node, hnodeFrontier⟩).support then
              PMF.pure
                (current.withPatch patch hcurrentFrontier
                  (frontierPatchDist_support_legal G cfg joint hjoint
                    ⟨node, hnodeFrontier⟩ hpatch))
            else
              PMF.pure current) := by
  classical
  dsimp
  let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
  have hcurrentFrontier : node ∈ current.frontier :=
    cfg.withNodePatches_mem_frontier_of_not_mem
      hdoneSubset donePatch doneLegal hnodeFrontier hnotDone
  cases hactor : (G.sem node).actor with
  | some who =>
      have hactive : who ∈ frontierActive G cfg :=
        (mem_frontierActive_iff G cfg who).mpr
          ⟨node, hnodeFrontier, hactor⟩
      have hcoord := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hround :
              who ∈ frontierActive G cfg ∧
                action ∈ frontierAvailable G cfg who := by
            simpa [hmove] using hcoord
          have hactionSource :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G cfg who := by
            exact
              ⟨hnodeFrontier, hactor,
                (hround.2 hnodeFrontier hactor).1,
                (hround.2 hnodeFrontier hactor).2⟩
          have hactionCurrent :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G current who := by
            dsimp [current]
            exact available_after_withNodePatches_of_not_mem
              G hsound cfg hdoneSubset donePatch doneLegal hnotDone
              hactionSource
          rw [frontierStepNode]
          simp only [hactor, hmove]
          rw [stepPlay_eq_pure_of_available G hactionCurrent]
          have hpure :
              action.patch node ∈
                (frontierPatchDist G cfg joint hjoint
                  ⟨node, hnodeFrontier⟩).support := by
            simp [frontierPatchDist, hactor, hmove]
          have hcfg :
              current.withPatch (action.patch node) hactionCurrent.1
                  hactionCurrent.2.2.1 =
                (cfg.withNodePatches done hdoneSubset donePatch doneLegal).withPatch
                  (action.patch node) hcurrentFrontier
                  (frontierPatchDist_support_legal G cfg joint hjoint
                    ⟨node, hnodeFrontier⟩ hpure) := by
            apply Configuration.ext
            funext candidate
            by_cases hcandidate : candidate = node
            · subst candidate
              simp [current, Configuration.withPatch,
                Configuration.updatePatch]
            · simp [current, Configuration.withPatch,
                Configuration.updatePatch, hcandidate]
          simpa [frontierPatchDist, hactor, hmove, hpure] using
            congrArg PMF.pure hcfg
  | none =>
      have hkernel :
          G.internalKernel node current.result =
            G.internalKernel node cfg.result := by
        dsimp [current]
        exact internalKernel_after_withNodePatches_of_not_mem
          G hsound cfg hdoneSubset donePatch doneLegal
          hnodeFrontier hnotDone
      rw [frontierStepNode]
      simp only [hactor]
      rw [hkernel]
      simp only [frontierPatchDist, hactor]
      change
        ((G.internalKernel node cfg.result).bind fun patch =>
          stepInternal G (InternalEvent.node node patch)
            (cfg.withNodePatches done hdoneSubset donePatch doneLegal)) =
        ((G.internalKernel node cfg.result).bind fun patch =>
          if hpatch : patch ∈ (G.internalKernel node cfg.result).support then
            PMF.pure
              ((cfg.withNodePatches done hdoneSubset donePatch doneLegal).withPatch
                patch hcurrentFrontier
                (frontierPatchDist_support_legal G cfg joint hjoint
                  ⟨node, hnodeFrontier⟩
                  (by simpa [frontierPatchDist, hactor] using hpatch)))
          else
            PMF.pure current)
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (G.internalKernel node cfg.result) _ _ ?_
      intro patch hpatch
      have hpatchFrontier :
          patch ∈
            (frontierPatchDist G cfg joint hjoint
              ⟨node, hnodeFrontier⟩).support := by
        simpa [frontierPatchDist, hactor] using hpatch
      have hpatchLegal : G.patchLegal node patch :=
        frontierPatchDist_support_legal G cfg joint hjoint
          ⟨node, hnodeFrontier⟩ hpatchFrontier
      have havailable :
          (InternalEvent.node node patch : InternalEvent G) ∈
            availableInternal G current := by
        refine ⟨hcurrentFrontier, hactor, ?_⟩
        rw [hkernel]
        exact hpatch
      rw [stepInternal_eq_pure_of_available G havailable
        hcurrentFrontier hpatchLegal]
      have hne : ¬ (G.internalKernel node cfg.result) patch = 0 := by
        simpa [PMF.mem_support_iff] using hpatch
      have hcfg :
          current.withPatch patch hcurrentFrontier hpatchLegal =
            (cfg.withNodePatches done hdoneSubset donePatch doneLegal).withPatch
              patch hcurrentFrontier
              (frontierPatchDist_support_legal G cfg joint hjoint
                ⟨node, hnodeFrontier⟩
                (by simpa [frontierPatchDist, hactor] using hpatch)) := by
        apply Configuration.ext
        funext candidate
        by_cases hcandidate : candidate = node
        · subst candidate
          simp [current, Configuration.withPatch, Configuration.updatePatch]
        · simp [current, Configuration.withPatch, Configuration.updatePatch,
            hcandidate]
      simpa [hne] using congrArg PMF.pure hcfg

/-- Source coordinate patch law with an executed prefix forced to its already
sampled values. -/
private noncomputable def frontierPatchDistWithDone
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (idx : FrontierIndex G cfg) :
    PMF G.FieldPatch :=
  if hdone : idx.1 ∈ done then
    PMF.pure (donePatch idx.1 hdone)
  else
    frontierPatchDist G cfg joint hlegal idx

private theorem frontierPatchDistWithDone_eq_source_of_not_mem
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    {idx : FrontierIndex G cfg}
    (hnot : idx.1 ∉ done) :
    frontierPatchDistWithDone G cfg joint hlegal donePatch idx =
      frontierPatchDist G cfg joint hlegal idx := by
  simp [frontierPatchDistWithDone, hnot]

private theorem pmfPi_support_coord
    {ι : Type} [Fintype ι]
    {A : ι → Type}
    (σ : ∀ i, PMF (A i))
    {patches : ∀ i, A i}
    (hsupp : patches ∈ (Math.PMFProduct.pmfPi σ).support)
    (idx : ι) :
    patches idx ∈ (σ idx).support := by
  classical
  have hmass :
      (Math.PMFProduct.pmfPi σ) patches ≠ 0 :=
    (PMF.mem_support_iff _ _).mp hsupp
  have hprod :
      (∏ idx, σ idx (patches idx)) ≠ 0 := by
    simpa [Math.PMFProduct.pmfPi_apply] using hmass
  have hcoord :
      σ idx (patches idx) ≠ 0 :=
    (Finset.prod_ne_zero_iff).mp hprod idx (Finset.mem_univ idx)
  exact (PMF.mem_support_iff _ _).mpr hcoord

private theorem frontierPatchDistWithDone_support_legal
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode))
    {patches : FrontierIndex G cfg → G.FieldPatch}
    (hsupp :
      patches ∈
        (Math.PMFProduct.pmfPi
          (frontierPatchDistWithDone G cfg joint hlegal
            donePatch)).support) :
    ∀ idx : FrontierIndex G cfg, G.patchLegal idx.1 (patches idx) := by
  classical
  intro idx
  have hcoord :=
    pmfPi_support_coord
      (frontierPatchDistWithDone G cfg joint hlegal donePatch)
      hsupp idx
  by_cases hdone : idx.1 ∈ done
  · have hpure :
        patches idx ∈
          (PMF.pure (donePatch idx.1 hdone) :
            PMF G.FieldPatch).support := by
        simpa [frontierPatchDistWithDone, hdone] using hcoord
    have hpatch : patches idx = donePatch idx.1 hdone :=
      (PMF.mem_support_pure_iff (donePatch idx.1 hdone)
        (patches idx)).mp hpure
    rw [hpatch]
    exact doneLegal idx.1 hdone
  · have hsource :
        patches idx ∈
          (frontierPatchDist G cfg joint hlegal idx).support := by
        simpa [frontierPatchDistWithDone, hdone] using hcoord
    exact frontierPatchDist_support_legal G cfg joint hlegal idx hsource

private theorem frontierPatchDistWithDone_pointwise_legal
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode))
    {patches : FrontierIndex G cfg → G.FieldPatch}
    (hsupp :
      ∀ idx : FrontierIndex G cfg,
        patches idx ∈
          (frontierPatchDistWithDone G cfg joint hlegal
            donePatch idx).support) :
    ∀ idx : FrontierIndex G cfg, G.patchLegal idx.1 (patches idx) := by
  classical
  intro idx
  have hcoord := hsupp idx
  by_cases hdone : idx.1 ∈ done
  · have hpure :
        patches idx ∈
          (PMF.pure (donePatch idx.1 hdone) :
            PMF G.FieldPatch).support := by
        simpa [frontierPatchDistWithDone, hdone] using hcoord
    have hpatch : patches idx = donePatch idx.1 hdone :=
      (PMF.mem_support_pure_iff (donePatch idx.1 hdone)
        (patches idx)).mp hpure
    rw [hpatch]
    exact doneLegal idx.1 hdone
  · have hsource :
        patches idx ∈
          (frontierPatchDist G cfg joint hlegal idx).support := by
        simpa [frontierPatchDistWithDone, hdone] using hcoord
    exact frontierPatchDist_support_legal G cfg joint hlegal idx hsource

private noncomputable def configOfFrontierPatches
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (patches : FrontierIndex G cfg → G.FieldPatch)
    (hlegal :
      ∀ idx : FrontierIndex G cfg, G.patchLegal idx.1 (patches idx)) :
    G.Configuration :=
  cfg.withFrontierPatches
    (fun node hfrontier => patches ⟨node, hfrontier⟩)
    (fun node hfrontier => hlegal ⟨node, hfrontier⟩)

private noncomputable def frontierProductConfigDist
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode)) :
    PMF G.Configuration := by
  classical
  exact
    (Math.PMFProduct.pmfPi
      (frontierPatchDistWithDone G cfg joint hlegal donePatch)).bind
      fun patches =>
        if hsupp :
            ∀ idx : FrontierIndex G cfg,
              patches idx ∈
                (frontierPatchDistWithDone G cfg joint hlegal
                  donePatch idx).support then
          PMF.pure
            (configOfFrontierPatches G cfg patches
              (frontierPatchDistWithDone_pointwise_legal G cfg joint hlegal
                donePatch doneLegal hsupp))
        else
          PMF.pure (cfg.withNodePatches done hdoneSubset donePatch doneLegal)

private theorem frontierPatchDistWithDone_insert_eq_update
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    {node : G.Node} (hnodeFrontier : node ∈ cfg.frontier)
    (nodePatch : G.FieldPatch) :
    let inserted : Finset G.Node := insert node done
    let insertedPatch :
        ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
      fun candidate hcandidate =>
        if h : candidate = node then
          nodePatch
        else
          donePatch candidate (by
            rcases Finset.mem_insert.mp hcandidate with hmem | hmem
            · exact False.elim (h hmem)
            · exact hmem)
    (fun idx =>
      frontierPatchDistWithDone G cfg joint hlegal insertedPatch idx) =
      Function.update
        (fun idx =>
          frontierPatchDistWithDone G cfg joint hlegal donePatch idx)
        ⟨node, hnodeFrontier⟩
        (PMF.pure nodePatch) := by
  classical
  funext idx
  by_cases hidx : idx = ⟨node, hnodeFrontier⟩
  · subst idx
    simp [frontierPatchDistWithDone]
  · have hidxNode : idx.1 ≠ node := by
      intro hnode
      apply hidx
      apply Subtype.ext
      exact hnode
    simp [frontierPatchDistWithDone, Function.update_of_ne hidx,
      hidxNode]

private theorem configOfFrontierPatches_eq_extend
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (realization : FrontierRealization G cfg)
    (hlegal : realization.Legal) :
    configOfFrontierPatches G cfg realization.patch hlegal =
      cfg.extendFrontier realization hlegal := by
  rfl

/-- Order-free state transition induced by a legal frontier realization. The
fallback branch is unreachable on the support of well-formed event graphs; it
keeps the function total over Lean's unconstrained PMF samples. -/
noncomputable def frontierRealizationTransition
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    PMF G.Configuration := by
  classical
  exact
    (frontierRealizationDist G cfg joint.1 joint.2).bind fun realization =>
      if hlegal : realization.Legal then
        PMF.pure (cfg.extendFrontier realization hlegal)
      else
        PMF.pure cfg

/-- On the support of the order-free frontier realization law, the totality
fallback in `frontierRealizationTransition` is unreachable. -/
theorem frontierRealizationTransition_eq_bind_extendFrontier
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    frontierRealizationTransition G cfg joint =
      (by
        classical
        exact
          (frontierRealizationDist G cfg joint.1 joint.2).bind
            fun realization =>
              if hsupp :
                  realization ∈
                    (frontierRealizationDist G cfg joint.1 joint.2).support then
                PMF.pure
                  (cfg.extendFrontier realization
                    (frontierRealizationDist_support_legal
                      G cfg joint.1 joint.2 hsupp))
              else
                PMF.pure cfg) := by
  classical
  unfold frontierRealizationTransition
  refine Math.ProbabilityMassFunction.bind_congr_on_support
    (frontierRealizationDist G cfg joint.1 joint.2)
    (fun realization =>
      if hlegal : realization.Legal then
        PMF.pure (cfg.extendFrontier realization hlegal)
      else
        PMF.pure cfg)
    (fun realization =>
      if hsupp :
          realization ∈
            (frontierRealizationDist G cfg joint.1 joint.2).support then
        PMF.pure
          (cfg.extendFrontier realization
            (frontierRealizationDist_support_legal
              G cfg joint.1 joint.2 hsupp))
      else
        PMF.pure cfg)
    ?_
  · intro realization hsupp
    have hlegal :
        realization.Legal :=
      frontierRealizationDist_support_legal G cfg joint.1 joint.2 hsupp
    simp [hlegal, hsupp]

/-- Raw-product normal form for the order-free frontier transition. -/
private theorem frontierRealizationTransition_eq_bind_configOfPatches
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    frontierRealizationTransition G cfg joint =
      (by
        classical
        let sourceFamily :=
          frontierPatchDist G cfg joint.1 joint.2
        exact
          (Math.PMFProduct.pmfPi sourceFamily).bind fun patches =>
            if hsupp :
                patches ∈ (Math.PMFProduct.pmfPi sourceFamily).support then
              PMF.pure
                (configOfFrontierPatches G cfg patches
                  (frontierPatchDistWithDone_support_legal G cfg
                    joint.1 joint.2
                    (done := ∅)
                    (fun node hnode => False.elim (by simp at hnode))
                    (fun node hnode => False.elim (by simp at hnode))
                    (by
                      simpa [sourceFamily, frontierPatchDistWithDone] using
                        hsupp)))
            else
              PMF.pure cfg) := by
  classical
  unfold frontierRealizationTransition frontierRealizationDist
  rw [← PMF.bind_pure_comp
    (fun patch : FrontierIndex G cfg → G.FieldPatch =>
      ({ patch := patch } : FrontierRealization G cfg))
    (Math.PMFProduct.pmfPi
      (fun idx => frontierPatchDist G cfg joint.1 joint.2 idx))]
  rw [PMF.bind_bind]
  refine Math.ProbabilityMassFunction.bind_congr_on_support
    (Math.PMFProduct.pmfPi
      (fun idx => frontierPatchDist G cfg joint.1 joint.2 idx))
    _ _ ?_
  intro patches hsupp
  have hrealSupp :
      ({ patch := patches } : FrontierRealization G cfg) ∈
        (PMF.map
          (fun patch : FrontierIndex G cfg → G.FieldPatch =>
            ({ patch := patch } : FrontierRealization G cfg))
          (Math.PMFProduct.pmfPi
            (fun idx => frontierPatchDist G cfg joint.1 joint.2 idx))).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨patches, hsupp, rfl⟩
  have hrealLegal :
      ({ patch := patches } : FrontierRealization G cfg).Legal :=
    frontierRealizationDist_support_legal G cfg joint.1 joint.2 hrealSupp
  have hpatchLegal :
      ∀ idx : FrontierIndex G cfg, G.patchLegal idx.1 (patches idx) :=
    frontierPatchDistWithDone_support_legal G cfg joint.1 joint.2
      (done := ∅)
      (fun node hnode => False.elim (by simp at hnode))
      (fun node hnode => False.elim (by simp at hnode))
      (by simpa [frontierPatchDistWithDone] using hsupp)
  have hcfg :
      cfg.extendFrontier
          ({ patch := patches } : FrontierRealization G cfg) hrealLegal =
        configOfFrontierPatches G cfg patches hpatchLegal := by
    rfl
  simp [hrealLegal, hsupp, hcfg, configOfFrontierPatches]

private theorem frontierProductConfigDist_empty_eq_frontierRealizationTransition
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    frontierProductConfigDist G cfg joint.1 joint.2
      (done := ∅)
      (by intro node hnode; simp at hnode)
      (fun _ hnode => False.elim (by simp at hnode))
      (fun _ hnode => False.elim (by simp at hnode)) =
      frontierRealizationTransition G cfg joint := by
  classical
  rw [frontierRealizationTransition_eq_bind_configOfPatches]
  unfold frontierProductConfigDist
  let sourceFamily := frontierPatchDist G cfg joint.1 joint.2
  change
    (Math.PMFProduct.pmfPi sourceFamily).bind
        (fun patches =>
          if hpoint :
              ∀ idx : FrontierIndex G cfg,
                patches idx ∈ (sourceFamily idx).support then
            PMF.pure
              (configOfFrontierPatches G cfg patches
                (frontierPatchDistWithDone_pointwise_legal G cfg
                  joint.1 joint.2
                  (done := ∅)
                  (fun node hnode => False.elim (by simp at hnode))
                  (fun node hnode => False.elim (by simp at hnode))
                  (by simpa [sourceFamily, frontierPatchDistWithDone] using
                    hpoint)))
          else
            PMF.pure
              (cfg.withNodePatches ∅
                (by intro node hnode; simp at hnode)
                (fun _ hnode => False.elim (by simp at hnode))
                (fun _ hnode => False.elim (by simp at hnode)))) =
      (Math.PMFProduct.pmfPi sourceFamily).bind
        (fun patches =>
          if hsupp :
              patches ∈
                (Math.PMFProduct.pmfPi sourceFamily).support then
            PMF.pure
              (configOfFrontierPatches G cfg patches
                (frontierPatchDistWithDone_support_legal G cfg
                  joint.1 joint.2
                  (done := ∅)
                  (fun node hnode => False.elim (by simp at hnode))
                  (fun node hnode => False.elim (by simp at hnode))
                  (by simpa [sourceFamily, frontierPatchDistWithDone] using
                    hsupp)))
          else
            PMF.pure cfg)
  refine Math.ProbabilityMassFunction.bind_congr_on_support
    (Math.PMFProduct.pmfPi sourceFamily) _ _ ?_
  intro patches hsupp
  have hpoint :
      ∀ idx : FrontierIndex G cfg,
        patches idx ∈ (sourceFamily idx).support := by
    intro idx
    exact pmfPi_support_coord sourceFamily hsupp idx
  have hcfg :
      configOfFrontierPatches G cfg patches
          (frontierPatchDistWithDone_pointwise_legal G cfg
            joint.1 joint.2
            (done := ∅)
            (fun node hnode => False.elim (by simp at hnode))
            (fun node hnode => False.elim (by simp at hnode))
            (by simpa [sourceFamily, frontierPatchDistWithDone] using
              hpoint)) =
        configOfFrontierPatches G cfg patches
          (frontierPatchDistWithDone_support_legal G cfg
            joint.1 joint.2
            (done := ∅)
            (fun node hnode => False.elim (by simp at hnode))
            (fun node hnode => False.elim (by simp at hnode))
            (by simpa [sourceFamily, frontierPatchDistWithDone] using
              hsupp)) := by
    apply Configuration.ext
    funext node
    by_cases hfrontier : node ∈ cfg.frontier
    · simp [configOfFrontierPatches, hfrontier]
    · simp [configOfFrontierPatches, hfrontier]
  simp [hpoint, hsupp, hcfg]

private theorem frontierProductConfigDist_of_cover
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    {joint : JointAction (PlayerFrontierAction G)}
    (hjoint :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    (hcover : ∀ node, node ∈ cfg.frontier → node ∈ done)
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode)) :
    frontierProductConfigDist G cfg joint hjoint hdoneSubset
      donePatch doneLegal =
      PMF.pure (cfg.withNodePatches done hdoneSubset donePatch doneLegal) := by
  classical
  unfold frontierProductConfigDist
  refine (Math.ProbabilityMassFunction.bind_congr_on_support
    (Math.PMFProduct.pmfPi
      (frontierPatchDistWithDone G cfg joint hjoint donePatch))
    _ (fun _ => PMF.pure
      (cfg.withNodePatches done hdoneSubset donePatch doneLegal)) ?_).trans ?_
  · intro patches hsupp
    have hpoint :
        ∀ idx : FrontierIndex G cfg,
          patches idx ∈
            (frontierPatchDistWithDone G cfg joint hjoint
              donePatch idx).support := by
      intro idx
      exact pmfPi_support_coord
        (frontierPatchDistWithDone G cfg joint hjoint donePatch)
        hsupp idx
    have hcfg :
        configOfFrontierPatches G cfg patches
            (frontierPatchDistWithDone_pointwise_legal G cfg joint hjoint
              donePatch doneLegal hpoint) =
          cfg.withNodePatches done hdoneSubset donePatch doneLegal := by
      apply Configuration.ext
      funext node
      by_cases hfrontier : node ∈ cfg.frontier
      · have hdone : node ∈ done := hcover node hfrontier
        have hpure :
            patches ⟨node, hfrontier⟩ ∈
              (PMF.pure (donePatch node hdone) :
                PMF G.FieldPatch).support := by
          simpa [frontierPatchDistWithDone, hdone] using
            hpoint ⟨node, hfrontier⟩
        have hpatch :
            patches ⟨node, hfrontier⟩ = donePatch node hdone :=
          (PMF.mem_support_pure_iff (donePatch node hdone)
            (patches ⟨node, hfrontier⟩)).mp hpure
        simp [configOfFrontierPatches, hfrontier, hdone, hpatch]
      · have hdone : node ∉ done := by
          intro h
          exact hfrontier (hdoneSubset h)
        simp [configOfFrontierPatches, hfrontier, hdone]
    simp [hpoint, hcfg]
  · simp [PMF.bind_const]

private theorem frontierProductConfigDist_step
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    {joint : JointAction (PlayerFrontierAction G)}
    (hjoint :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    (donePatch : ∀ node, node ∈ done → G.FieldPatch)
    (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode))
    {node : G.Node}
    (hnodeFrontier : node ∈ cfg.frontier)
    (hnotDone : node ∉ done) :
    let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
    frontierProductConfigDist G cfg joint hjoint hdoneSubset
      donePatch doneLegal =
      (by
        classical
        exact
          (frontierPatchDist G cfg joint hjoint
            ⟨node, hnodeFrontier⟩).bind fun nodePatch =>
            if hpatch :
                nodePatch ∈
                  (frontierPatchDist G cfg joint hjoint
                    ⟨node, hnodeFrontier⟩).support then
              let inserted : Finset G.Node := insert node done
              let insertedSubset : inserted ⊆ cfg.frontier := by
                intro candidate hcandidate
                rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hnodeFrontier
                · exact hdoneSubset hcandidate
              let insertedPatch :
                  ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
                fun candidate hcandidate =>
                  if h : candidate = node then
                    nodePatch
                  else
                    donePatch candidate (by
                      rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                      · exact False.elim (h hmem)
                      · exact hmem)
              let insertedLegal :
                  ∀ candidate hcandidate,
                    G.patchLegal candidate (insertedPatch candidate hcandidate) := by
                intro candidate hcandidate
                dsimp [insertedPatch]
                split
                · subst candidate
                  exact frontierPatchDist_support_legal G cfg joint hjoint
                    ⟨node, hnodeFrontier⟩ hpatch
                · rename_i hne
                  exact doneLegal candidate (by
                    rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                    · exact False.elim (hne hmem)
                    · exact hmem)
              frontierProductConfigDist G cfg joint hjoint insertedSubset
                insertedPatch insertedLegal
            else
              PMF.pure current) := by
  classical
  dsimp
  let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
  let idx : FrontierIndex G cfg := ⟨node, hnodeFrontier⟩
  let familyDone :=
    frontierPatchDistWithDone G cfg joint hjoint donePatch
  let source := frontierPatchDist G cfg joint hjoint idx
  have hfamilySource : Function.update familyDone idx source = familyDone := by
    funext candidate
    by_cases hcandidate : candidate = idx
    · subst candidate
      simp [familyDone, source, idx, frontierPatchDistWithDone, hnotDone]
    · rw [Function.update_of_ne hcandidate]
  unfold frontierProductConfigDist
  change
    (Math.PMFProduct.pmfPi familyDone).bind
        (fun patches =>
          if hpoint :
              ∀ idx : FrontierIndex G cfg,
                patches idx ∈ (familyDone idx).support then
            PMF.pure
              (configOfFrontierPatches G cfg patches
                (frontierPatchDistWithDone_pointwise_legal G cfg joint hjoint
                  donePatch doneLegal (by simpa [familyDone] using hpoint)))
          else
            PMF.pure current) =
      source.bind fun nodePatch =>
        if hpatch : nodePatch ∈ source.support then
          let inserted : Finset G.Node := insert node done
          let insertedSubset : inserted ⊆ cfg.frontier := by
            intro candidate hcandidate
            rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
            · subst candidate
              exact hnodeFrontier
            · exact hdoneSubset hcandidate
          let insertedPatch :
              ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
            fun candidate hcandidate =>
              if h : candidate = node then
                nodePatch
              else
                donePatch candidate (by
                  rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                  · exact False.elim (h hmem)
                  · exact hmem)
          let insertedLegal :
              ∀ candidate hcandidate,
                G.patchLegal candidate (insertedPatch candidate hcandidate) := by
            intro candidate hcandidate
            dsimp [insertedPatch]
            split
            · subst candidate
              exact frontierPatchDist_support_legal G cfg joint hjoint
                ⟨node, hnodeFrontier⟩ hpatch
            · rename_i hne
              exact doneLegal candidate (by
                rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                · exact False.elim (hne hmem)
                · exact hmem)
          (Math.PMFProduct.pmfPi
              (frontierPatchDistWithDone G cfg joint hjoint
                insertedPatch)).bind
            fun patches =>
              if hpoint :
                  ∀ idx : FrontierIndex G cfg,
                    patches idx ∈
                      (frontierPatchDistWithDone G cfg joint hjoint
                        insertedPatch idx).support then
                PMF.pure
                  (configOfFrontierPatches G cfg patches
                    (frontierPatchDistWithDone_pointwise_legal G cfg
                      joint hjoint insertedPatch insertedLegal hpoint))
              else
                PMF.pure
                  (cfg.withNodePatches inserted insertedSubset
                    insertedPatch insertedLegal)
        else
          PMF.pure current
  have hpmf :
      Math.PMFProduct.pmfPi familyDone =
        Math.PMFProduct.pmfPi (Function.update familyDone idx source) := by
    exact congrArg Math.PMFProduct.pmfPi hfamilySource.symm
  rw [hpmf]
  rw [Math.PMFProduct.pmfPi_update_bind]
  rw [PMF.bind_bind]
  refine Math.ProbabilityMassFunction.bind_congr_on_support source _ _ ?_
  intro nodePatch hnodePatch
  have hpatchIff :
      (if hpatch : nodePatch ∈ source.support then
          let inserted : Finset G.Node := insert node done
          let insertedSubset : inserted ⊆ cfg.frontier := by
            intro candidate hcandidate
            rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
            · subst candidate
              exact hnodeFrontier
            · exact hdoneSubset hcandidate
          let insertedPatch :
              ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
            fun candidate hcandidate =>
              if h : candidate = node then
                nodePatch
              else
                donePatch candidate (by
                  rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                  · exact False.elim (h hmem)
                  · exact hmem)
          let insertedLegal :
              ∀ candidate hcandidate,
                G.patchLegal candidate (insertedPatch candidate hcandidate) := by
            intro candidate hcandidate
            dsimp [insertedPatch]
            split
            · subst candidate
              exact frontierPatchDist_support_legal G cfg joint hjoint
                ⟨node, hnodeFrontier⟩ hpatch
            · rename_i hne
              exact doneLegal candidate (by
                rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                · exact False.elim (hne hmem)
                · exact hmem)
          (Math.PMFProduct.pmfPi
              (frontierPatchDistWithDone G cfg joint hjoint
                insertedPatch)).bind
            fun patches =>
              if hpoint :
                  ∀ idx : FrontierIndex G cfg,
                    patches idx ∈
                      (frontierPatchDistWithDone G cfg joint hjoint
                        insertedPatch idx).support then
                PMF.pure
                  (configOfFrontierPatches G cfg patches
                    (frontierPatchDistWithDone_pointwise_legal G cfg
                      joint hjoint insertedPatch insertedLegal hpoint))
              else
                PMF.pure
                  (cfg.withNodePatches inserted insertedSubset
                    insertedPatch insertedLegal)
        else
          PMF.pure current) =
        (let inserted : Finset G.Node := insert node done
         let insertedSubset : inserted ⊆ cfg.frontier := by
            intro candidate hcandidate
            rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
            · subst candidate
              exact hnodeFrontier
            · exact hdoneSubset hcandidate
          let insertedPatch :
              ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
            fun candidate hcandidate =>
              if h : candidate = node then
                nodePatch
              else
                donePatch candidate (by
                  rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                  · exact False.elim (h hmem)
                  · exact hmem)
          let insertedLegal :
              ∀ candidate hcandidate,
                G.patchLegal candidate (insertedPatch candidate hcandidate) := by
            intro candidate hcandidate
            dsimp [insertedPatch]
            split
            · subst candidate
              exact frontierPatchDist_support_legal G cfg joint hjoint
                ⟨node, hnodeFrontier⟩ hnodePatch
            · rename_i hne
              exact doneLegal candidate (by
                rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                · exact False.elim (hne hmem)
                · exact hmem)
          (Math.PMFProduct.pmfPi
              (frontierPatchDistWithDone G cfg joint hjoint
                insertedPatch)).bind
            fun patches =>
              if hpoint :
                  ∀ idx : FrontierIndex G cfg,
                    patches idx ∈
                      (frontierPatchDistWithDone G cfg joint hjoint
                        insertedPatch idx).support then
                PMF.pure
                  (configOfFrontierPatches G cfg patches
                    (frontierPatchDistWithDone_pointwise_legal G cfg
                      joint hjoint insertedPatch insertedLegal hpoint))
              else
                PMF.pure
                  (cfg.withNodePatches inserted insertedSubset
                    insertedPatch insertedLegal)) := by
    simp [hnodePatch]
  rw [hpatchIff]
  let inserted : Finset G.Node := insert node done
  let insertedSubset : inserted ⊆ cfg.frontier := by
    intro candidate hcandidate
    rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
    · subst candidate
      exact hnodeFrontier
    · exact hdoneSubset hcandidate
  let insertedPatch :
      ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
    fun candidate hcandidate =>
      if h : candidate = node then
        nodePatch
      else
        donePatch candidate (by
          rcases Finset.mem_insert.mp hcandidate with hmem | hmem
          · exact False.elim (h hmem)
          · exact hmem)
  let insertedLegal :
      ∀ candidate hcandidate,
        G.patchLegal candidate (insertedPatch candidate hcandidate) := by
    intro candidate hcandidate
    dsimp [insertedPatch]
    split
    · subst candidate
      exact frontierPatchDist_support_legal G cfg joint hjoint
        ⟨node, hnodeFrontier⟩ hnodePatch
    · rename_i hne
      exact doneLegal candidate (by
        rcases Finset.mem_insert.mp hcandidate with hmem | hmem
        · exact False.elim (hne hmem)
        · exact hmem)
  have hfamilyInserted :
      (fun idx =>
        frontierPatchDistWithDone G cfg joint hjoint insertedPatch idx) =
        Function.update familyDone idx (PMF.pure nodePatch) := by
    dsimp [insertedPatch, familyDone, idx]
    exact frontierPatchDistWithDone_insert_eq_update
      G cfg joint hjoint donePatch hnodeFrontier nodePatch
  rw [← hfamilyInserted]
  refine Math.ProbabilityMassFunction.bind_congr_on_support
    (Math.PMFProduct.pmfPi
      (frontierPatchDistWithDone G cfg joint hjoint insertedPatch)) _ _ ?_
  intro patches hsupp
  have hpointInserted :
      ∀ idx : FrontierIndex G cfg,
        patches idx ∈
          (frontierPatchDistWithDone G cfg joint hjoint
            insertedPatch idx).support := by
    intro candidate
    exact pmfPi_support_coord
      (frontierPatchDistWithDone G cfg joint hjoint insertedPatch)
      hsupp candidate
  have hpointDone :
      ∀ candidate : FrontierIndex G cfg,
        patches candidate ∈ (familyDone candidate).support := by
    intro candidate
    by_cases hcandidate : candidate = idx
    · subst candidate
      have hpure :
          patches idx ∈ (PMF.pure nodePatch : PMF G.FieldPatch).support := by
        have hcoord :=
          pmfPi_support_coord
            (frontierPatchDistWithDone G cfg joint hjoint insertedPatch)
            hsupp idx
        have hfamilyAt := congrFun hfamilyInserted idx
        rw [hfamilyAt] at hcoord
        simpa [Function.update] using hcoord
      have hpatchEq : patches idx = nodePatch :=
        (PMF.mem_support_pure_iff nodePatch (patches idx)).mp hpure
      rw [hpatchEq]
      simpa [familyDone, source, idx, frontierPatchDistWithDone, hnotDone]
        using hnodePatch
    · have hcoord :=
        pmfPi_support_coord
          (frontierPatchDistWithDone G cfg joint hjoint insertedPatch)
          hsupp candidate
      have hsame :
          frontierPatchDistWithDone G cfg joint hjoint insertedPatch candidate =
            familyDone candidate := by
        have hupdate :=
          congrFun hfamilyInserted candidate
        rw [Function.update_of_ne hcandidate] at hupdate
        exact hupdate
      simpa [hsame] using hcoord
  have hcfg :
      configOfFrontierPatches G cfg patches
          (frontierPatchDistWithDone_pointwise_legal G cfg joint hjoint
            donePatch doneLegal (by simpa [familyDone] using hpointDone)) =
        configOfFrontierPatches G cfg patches
          (frontierPatchDistWithDone_pointwise_legal G cfg joint hjoint
            insertedPatch insertedLegal hpointInserted) := by
    apply Configuration.ext
    funext candidate
    by_cases hfrontier : candidate ∈ cfg.frontier
    · simp [configOfFrontierPatches, hfrontier]
    · simp [configOfFrontierPatches, hfrontier]
  rw [dif_pos (by simpa [familyDone] using hpointDone)]
  rw [dif_pos hpointInserted]

private theorem scheduledFrontierTransitionGo_eq_frontierProductConfigDist
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hjoint :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint) :
    ∀ (nodes : List G.Node) (done : Finset G.Node)
      (_hnodup : nodes.Nodup)
      (hdoneSubset : done ⊆ cfg.frontier)
      (_hnodesSubset : ∀ node, node ∈ nodes → node ∈ cfg.frontier)
      (_hdisjoint : ∀ node, node ∈ nodes → node ∉ done)
      (_hcover : ∀ node, node ∈ cfg.frontier → node ∈ done ∨ node ∈ nodes)
      (donePatch : ∀ node, node ∈ done → G.FieldPatch)
      (doneLegal : ∀ node hnode, G.patchLegal node (donePatch node hnode)),
        scheduledFrontierTransitionGo G joint nodes
            (cfg.withNodePatches done hdoneSubset donePatch doneLegal) =
          frontierProductConfigDist G cfg joint hjoint hdoneSubset
            donePatch doneLegal
  | [], done, _hnodup, hdoneSubset, _hnodesSubset, _hdisjoint, hcover,
      donePatch, doneLegal => by
      have hcoverDone :
          ∀ node, node ∈ cfg.frontier → node ∈ done := by
        intro node hfrontier
        rcases hcover node hfrontier with hdone | hnodes
        · exact hdone
        · simp at hnodes
      rw [scheduledFrontierTransitionGo]
      rw [frontierProductConfigDist_of_cover
        G cfg hjoint hdoneSubset hcoverDone donePatch doneLegal]
  | node :: rest, done, hnodup, hdoneSubset, hnodesSubset,
      hdisjoint, hcover, donePatch, doneLegal => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      have hnodeFrontier : node ∈ cfg.frontier :=
        hnodesSubset node (by simp)
      have hnodeNotDone : node ∉ done :=
        hdisjoint node (by simp)
      let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
      have hcurrentFrontier : node ∈ current.frontier :=
        cfg.withNodePatches_mem_frontier_of_not_mem
          hdoneSubset donePatch doneLegal hnodeFrontier hnodeNotDone
      rw [scheduledFrontierTransitionGo]
      rw [frontierStepNode_withNodePatches_eq_bind_patchDist
        G hsound hjoint hdoneSubset donePatch doneLegal
        hnodeFrontier hnodeNotDone]
      rw [PMF.bind_bind]
      rw [frontierProductConfigDist_step G cfg hjoint hdoneSubset
        donePatch doneLegal hnodeFrontier hnodeNotDone]
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (frontierPatchDist G cfg joint hjoint ⟨node, hnodeFrontier⟩)
        _ _ ?_
      intro nodePatch hnodePatch
      let inserted : Finset G.Node := insert node done
      have insertedSubset : inserted ⊆ cfg.frontier := by
        intro candidate hcandidate
        rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hnodeFrontier
        · exact hdoneSubset hcandidate
      let insertedPatch :
          ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
        fun candidate hcandidate =>
          if h : candidate = node then
            nodePatch
          else
            donePatch candidate (by
              rcases Finset.mem_insert.mp hcandidate with hmem | hmem
              · exact False.elim (h hmem)
              · exact hmem)
      have insertedLegal :
          ∀ candidate hcandidate,
            G.patchLegal candidate (insertedPatch candidate hcandidate) := by
        intro candidate hcandidate
        dsimp [insertedPatch]
        split
        · subst candidate
          exact frontierPatchDist_support_legal G cfg joint hjoint
            ⟨node, hnodeFrontier⟩ hnodePatch
        · rename_i hne
          exact doneLegal candidate (by
            rcases Finset.mem_insert.mp hcandidate with hmem | hmem
            · exact False.elim (hne hmem)
            · exact hmem)
      have hnextEq :
          (current.withPatch nodePatch hcurrentFrontier
              (frontierPatchDist_support_legal G cfg joint hjoint
                ⟨node, hnodeFrontier⟩ hnodePatch)) =
            cfg.withNodePatches inserted insertedSubset
              insertedPatch insertedLegal := by
        dsimp [current, inserted, insertedPatch, insertedLegal]
        exact cfg.withNodePatches_insert_eq_withPatch
          hdoneSubset donePatch doneLegal hnodeFrontier hnodeNotDone
          nodePatch
          (frontierPatchDist_support_legal G cfg joint hjoint
            ⟨node, hnodeFrontier⟩ hnodePatch)
      have hrestSubset :
          ∀ candidate, candidate ∈ rest → candidate ∈ cfg.frontier := by
        intro candidate hcandidate
        exact hnodesSubset candidate (List.mem_cons_of_mem _ hcandidate)
      have hrestDisjoint :
          ∀ candidate, candidate ∈ rest → candidate ∉ inserted := by
        intro candidate hcandidate hdone'
        rcases Finset.mem_insert.mp hdone' with hcandidateNode | hdoneOld
        · subst candidate
          exact hnodeNotRest hcandidate
        · exact hdisjoint candidate (List.mem_cons_of_mem _ hcandidate)
            hdoneOld
      have hrestCover :
          ∀ candidate, candidate ∈ cfg.frontier →
            candidate ∈ inserted ∨ candidate ∈ rest := by
        intro candidate hcandidateFrontier
        rcases hcover candidate hcandidateFrontier with hdoneOld | hnodes
        · exact Or.inl (Finset.mem_insert_of_mem hdoneOld)
        · rcases List.mem_cons.mp hnodes with hcandidateNode | hrest
          · subst candidate
            exact Or.inl (Finset.mem_insert_self node done)
          · exact Or.inr hrest
      have hih :
          scheduledFrontierTransitionGo G joint rest
              (cfg.withNodePatches inserted insertedSubset
                insertedPatch insertedLegal) =
            frontierProductConfigDist G cfg joint hjoint insertedSubset
              insertedPatch insertedLegal :=
        scheduledFrontierTransitionGo_eq_frontierProductConfigDist
          G hsound hjoint rest inserted hrestNodup insertedSubset
          hrestSubset hrestDisjoint hrestCover insertedPatch insertedLegal
      rw [dif_pos hnodePatch]
      rw [PMF.pure_bind]
      rw [hnextEq]
      simpa [hnodePatch] using hih

/-- Supported order-free frontier destinations come from a supported legal
frontier realization. -/
theorem frontierRealizationTransition_support_extend
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint })
    {dst : G.Configuration}
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    ∃ realization,
      realization ∈
        (frontierRealizationDist G cfg joint.1 joint.2).support ∧
        ∃ hlegal : realization.Legal,
          dst = cfg.extendFrontier realization hlegal := by
  classical
  unfold frontierRealizationTransition at hdst
  rw [PMF.mem_support_bind_iff] at hdst
  rcases hdst with ⟨realization, hrealization, hdst⟩
  have hlegalSupport :
      realization.Legal :=
    frontierRealizationDist_support_legal G cfg joint.1 joint.2 hrealization
  refine ⟨realization, hrealization, hlegalSupport, ?_⟩
  by_cases hlegal : realization.Legal
  · have hdst' :
        dst ∈ (PMF.pure (cfg.extendFrontier realization hlegal)).support := by
      simpa [hlegal] using hdst
    exact (PMF.mem_support_pure_iff
      (cfg.extendFrontier realization hlegal) dst).mp hdst'
  · exact False.elim (hlegal hlegalSupport)

/-- The order-free transition is extensional in the configuration and the
underlying joint action; legality proof terms are irrelevant. -/
theorem frontierRealizationTransition_congr
    (G : Vegas.EventGraph Player L)
    {cfg₁ cfg₂ : G.Configuration}
    (hcfg : cfg₁ = cfg₂)
    {joint₁ :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg₁ joint }}
    {joint₂ :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg₂ joint }}
    (hjoint : joint₁.1 = joint₂.1) :
    frontierRealizationTransition G cfg₁ joint₁ =
      frontierRealizationTransition G cfg₂ joint₂ := by
  subst cfg₂
  apply congrArg (frontierRealizationTransition G cfg₁)
  exact Subtype.ext hjoint

private theorem frontierStepNode_support_withNodePatches_realization
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hjoint :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {realization : FrontierRealization G cfg}
    (hrealSupp : realization ∈
      (frontierRealizationDist G cfg joint hjoint).support)
    (hrealLegal : realization.Legal)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    {node : G.Node}
    (hnodeFrontier : node ∈ cfg.frontier)
    (hnotDone : node ∉ done) :
    let donePatch :
        ∀ candidate, candidate ∈ done → G.FieldPatch :=
      fun candidate hcandidate =>
        realization.patchAt candidate (hdoneSubset hcandidate)
    let doneLegal :
        ∀ candidate hcandidate,
          G.patchLegal candidate (donePatch candidate hcandidate) :=
      fun candidate hcandidate =>
        hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
    let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
    let hcurrentFrontier : node ∈ current.frontier :=
      cfg.withNodePatches_mem_frontier_of_not_mem
        hdoneSubset donePatch doneLegal hnodeFrontier hnotDone
    let nodePatch := realization.patchAt node hnodeFrontier
    (current.withPatch nodePatch hcurrentFrontier
        (hrealLegal ⟨node, hnodeFrontier⟩)) ∈
      (frontierStepNode G joint node current).support := by
  classical
  dsimp
  let donePatch :
      ∀ candidate, candidate ∈ done → G.FieldPatch :=
    fun candidate hcandidate =>
      realization.patchAt candidate (hdoneSubset hcandidate)
  let doneLegal :
      ∀ candidate hcandidate,
        G.patchLegal candidate (donePatch candidate hcandidate) :=
    fun candidate hcandidate =>
      hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
  let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
  have hcurrentFrontier : node ∈ current.frontier :=
    cfg.withNodePatches_mem_frontier_of_not_mem
      hdoneSubset donePatch doneLegal hnodeFrontier hnotDone
  let nodePatch := realization.patchAt node hnodeFrontier
  have hnodeLegal : G.patchLegal node nodePatch :=
    hrealLegal ⟨node, hnodeFrontier⟩
  have hcoord :=
    frontierRealizationDist_support_coord G cfg joint hjoint hrealSupp
      ⟨node, hnodeFrontier⟩
  cases hactor : (G.sem node).actor with
  | some who =>
      have hactive : who ∈ frontierActive G cfg :=
        (mem_frontierActive_iff G cfg who).mpr ⟨node, hnodeFrontier, hactor⟩
      have hcoordLegal := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ frontierActive G cfg := by
            simpa [hmove] using hcoordLegal
          exact False.elim (hnot hactive)
      | some action =>
          have hround :
              who ∈ frontierActive G cfg ∧
                action ∈ frontierAvailable G cfg who := by
            simpa [hmove] using hcoordLegal
          have hactionSource :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G cfg who := by
            have hnode := hround.2 hnodeFrontier hactor
            exact ⟨hnodeFrontier, hactor, hnode.1, hnode.2⟩
          have hactionCurrent :
              ({ node := node, patch := action.patch node } :
                PlayerAction G who) ∈ available G current who := by
            dsimp [current]
            exact available_after_withNodePatches_of_not_mem
              G hsound cfg hdoneSubset donePatch doneLegal hnotDone
              hactionSource
          have hpatch : nodePatch = action.patch node := by
            have hmem :
                nodePatch ∈
                  (PMF.pure (action.patch node) : PMF G.FieldPatch).support := by
              simpa [frontierPatchDist, hactor, hmove, nodePatch,
                FrontierRealization.patchAt] using hcoord
            exact (PMF.mem_support_pure_iff (action.patch node) nodePatch).mp hmem
          rw [show frontierStepNode G joint node current =
              stepPlay G who { node := node, patch := action.patch node }
                current by
            simp [frontierStepNode, hactor, hmove]]
          change current.withPatch nodePatch hcurrentFrontier hnodeLegal ∈
            (stepPlay G who { node := node, patch := action.patch node }
              current).support
          have hdstEq :
              current.withPatch nodePatch hcurrentFrontier hnodeLegal =
                current.withPatch (action.patch node) hcurrentFrontier
                  (by simpa [hpatch] using hnodeLegal) := by
            apply Configuration.ext
            funext candidate
            by_cases hcandidate : candidate = node
            · subst candidate
              simp [Configuration.withPatch, Configuration.updatePatch, hpatch]
            · simp [Configuration.withPatch, Configuration.updatePatch,
                hcandidate]
          rw [hdstEq]
          rw [stepPlay_eq_pure_of_available G hactionCurrent]
          simp
  | none =>
      have hpatchSource :
          nodePatch ∈ (G.internalKernel node cfg.result).support := by
        simpa [frontierPatchDist, hactor, nodePatch,
          FrontierRealization.patchAt] using hcoord
      have hkernel :
          G.internalKernel node current.result =
            G.internalKernel node cfg.result := by
        dsimp [current]
        exact internalKernel_after_withNodePatches_of_not_mem
          G hsound cfg hdoneSubset donePatch doneLegal
          hnodeFrontier hnotDone
      have hpatchCurrent :
          nodePatch ∈ (G.internalKernel node current.result).support := by
        rw [hkernel]
        exact hpatchSource
      have havailable :
          (InternalEvent.node node nodePatch : InternalEvent G) ∈
            availableInternal G current := by
        exact ⟨hcurrentFrontier, hactor, hpatchCurrent⟩
      rw [frontierStepNode, hactor]
      rw [PMF.mem_support_bind_iff]
      refine ⟨nodePatch, hpatchCurrent, ?_⟩
      have hstep :
          (current.withPatch nodePatch hcurrentFrontier hnodeLegal) ∈
            (stepInternal G (InternalEvent.node node nodePatch) current).support := by
        rw [stepInternal_eq_pure_of_available G havailable
          hcurrentFrontier hnodeLegal]
        simp
      exact hstep

private theorem withNodePatches_insert_realization_eq_withPatch
    (G : Vegas.EventGraph Player L)
    {cfg : G.Configuration}
    {realization : FrontierRealization G cfg}
    (hrealLegal : realization.Legal)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    {node : G.Node}
    (hnodeFrontier : node ∈ cfg.frontier)
    (hnotDone : node ∉ done) :
    let donePatch :
        ∀ candidate, candidate ∈ done → G.FieldPatch :=
      fun candidate hcandidate =>
        realization.patchAt candidate (hdoneSubset hcandidate)
    let doneLegal :
        ∀ candidate hcandidate,
          G.patchLegal candidate (donePatch candidate hcandidate) :=
      fun candidate hcandidate =>
        hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
    let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
    let hcurrentFrontier : node ∈ current.frontier :=
      cfg.withNodePatches_mem_frontier_of_not_mem
        hdoneSubset donePatch doneLegal hnodeFrontier hnotDone
    let nodePatch := realization.patchAt node hnodeFrontier
    let inserted := insert node done
    let insertedSubset : inserted ⊆ cfg.frontier := by
      intro candidate hcandidate
      rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
      · subst candidate
        exact hnodeFrontier
      · exact hdoneSubset hcandidate
    let insertedPatch :
        ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
      fun candidate hcandidate =>
        realization.patchAt candidate (insertedSubset hcandidate)
    let insertedLegal :
        ∀ candidate hcandidate,
          G.patchLegal candidate (insertedPatch candidate hcandidate) :=
      fun candidate hcandidate =>
        hrealLegal ⟨candidate, insertedSubset hcandidate⟩
    current.withPatch nodePatch hcurrentFrontier
        (hrealLegal ⟨node, hnodeFrontier⟩) =
      cfg.withNodePatches inserted insertedSubset insertedPatch
        insertedLegal := by
  classical
  dsimp
  let donePatch :
      ∀ candidate, candidate ∈ done → G.FieldPatch :=
    fun candidate hcandidate =>
      realization.patchAt candidate (hdoneSubset hcandidate)
  let doneLegal :
      ∀ candidate hcandidate,
        G.patchLegal candidate (donePatch candidate hcandidate) :=
    fun candidate hcandidate =>
      hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
  let nodePatch := realization.patchAt node hnodeFrontier
  let inserted := insert node done
  let insertedSubset : inserted ⊆ cfg.frontier := by
    intro candidate hcandidate
    rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
    · subst candidate
      exact hnodeFrontier
    · exact hdoneSubset hcandidate
  let insertedPatch :
      ∀ candidate, candidate ∈ inserted → G.FieldPatch :=
    fun candidate hcandidate =>
      realization.patchAt candidate (insertedSubset hcandidate)
  let insertedLegal :
      ∀ candidate hcandidate,
        G.patchLegal candidate (insertedPatch candidate hcandidate) :=
    fun candidate hcandidate =>
      hrealLegal ⟨candidate, insertedSubset hcandidate⟩
  have hbase :=
    cfg.withNodePatches_insert_eq_withPatch
      hdoneSubset donePatch doneLegal hnodeFrontier hnotDone
      nodePatch (hrealLegal ⟨node, hnodeFrontier⟩)
  have hcongr :
      cfg.withNodePatches inserted insertedSubset
          (by
            intro candidate hcandidate
            exact
              if h : candidate = node then
                nodePatch
              else
                donePatch candidate (by
                  rcases Finset.mem_insert.mp hcandidate with hmem | hmem
                  · exact False.elim (h hmem)
                  · exact hmem))
          (by
            intro candidate hcandidate
            by_cases h : candidate = node
            · subst candidate
              simpa [nodePatch] using hrealLegal ⟨node, hnodeFrontier⟩
            · simp [h, doneLegal])
          =
        cfg.withNodePatches inserted insertedSubset insertedPatch
          insertedLegal := by
    apply Configuration.withNodePatches_congr
    intro candidate h₁ h₂
    dsimp [insertedPatch, insertedSubset, nodePatch, donePatch]
    by_cases hcandidate : candidate = node
    · subst candidate
      simp
    · simp [hcandidate]
  exact hbase.trans hcongr

private theorem extendFrontier_eq_withNodePatches_of_cover
    (G : Vegas.EventGraph Player L)
    {cfg : G.Configuration}
    {realization : FrontierRealization G cfg}
    (hrealLegal : realization.Legal)
    {done : Finset G.Node}
    (hdoneSubset : done ⊆ cfg.frontier)
    (hcover : ∀ node, node ∈ cfg.frontier → node ∈ done) :
    let donePatch :
        ∀ candidate, candidate ∈ done → G.FieldPatch :=
      fun candidate hcandidate =>
        realization.patchAt candidate (hdoneSubset hcandidate)
    let doneLegal :
        ∀ candidate hcandidate,
          G.patchLegal candidate (donePatch candidate hcandidate) :=
      fun candidate hcandidate =>
        hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
    cfg.extendFrontier realization hrealLegal =
      cfg.withNodePatches done hdoneSubset donePatch doneLegal := by
  classical
  dsimp
  apply Configuration.ext
  funext node
  by_cases hfrontier : node ∈ cfg.frontier
  · have hdone : node ∈ done := hcover node hfrontier
    rw [Configuration.extendFrontier_result_of_mem cfg realization hrealLegal
      hfrontier]
    rw [Configuration.withNodePatches_result_of_mem cfg done hdoneSubset
      (fun candidate hcandidate =>
        realization.patchAt candidate (hdoneSubset hcandidate))
      (fun candidate hcandidate =>
        hrealLegal ⟨candidate, hdoneSubset hcandidate⟩)
      hdone]
  · have hdone : node ∉ done := by
      intro h
      exact hfrontier (hdoneSubset h)
    rw [Configuration.extendFrontier_result_of_not_mem cfg realization
      hrealLegal hfrontier]
    rw [Configuration.withNodePatches_result_of_not_mem cfg done hdoneSubset
      (fun candidate hcandidate =>
        realization.patchAt candidate (hdoneSubset hcandidate))
      (fun candidate hcandidate =>
        hrealLegal ⟨candidate, hdoneSubset hcandidate⟩)
      hdone]

private theorem scheduledFrontierTransitionGo_support_extendFrontier_from_prefix
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hjoint :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    {realization : FrontierRealization G cfg}
    (hrealSupp : realization ∈
      (frontierRealizationDist G cfg joint hjoint).support)
    (hrealLegal : realization.Legal) :
    ∀ (nodes : List G.Node) (done : Finset G.Node)
      (_hnodup : nodes.Nodup)
      (hdoneSubset : done ⊆ cfg.frontier)
      (_hnodesSubset : ∀ node, node ∈ nodes → node ∈ cfg.frontier)
      (_hdisjoint : ∀ node, node ∈ nodes → node ∉ done)
      (_hcover : ∀ node, node ∈ cfg.frontier → node ∈ done ∨ node ∈ nodes),
        let donePatch :
            ∀ candidate, candidate ∈ done → G.FieldPatch :=
          fun candidate hcandidate =>
            realization.patchAt candidate (hdoneSubset hcandidate)
        let doneLegal :
            ∀ candidate hcandidate,
              G.patchLegal candidate (donePatch candidate hcandidate) :=
          fun candidate hcandidate =>
            hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
        cfg.extendFrontier realization hrealLegal ∈
          (scheduledFrontierTransitionGo G joint nodes
            (cfg.withNodePatches done hdoneSubset
              donePatch doneLegal)).support
  | [], done, _hnodup, hdoneSubset, _hnodesSubset, _hdisjoint, hcover => by
      have hcoverDone :
          ∀ node, node ∈ cfg.frontier → node ∈ done := by
        intro node hfrontier
        rcases hcover node hfrontier with hdone | hnodes
        · exact hdone
        · simp at hnodes
      have heq :=
        extendFrontier_eq_withNodePatches_of_cover
          G hrealLegal hdoneSubset hcoverDone
      simp [scheduledFrontierTransitionGo, heq]
  | node :: rest, done, hnodup, hdoneSubset, hnodesSubset,
      hdisjoint, hcover => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      have hnodeFrontier : node ∈ cfg.frontier :=
        hnodesSubset node (by simp)
      have hnodeNotDone : node ∉ done :=
        hdisjoint node (by simp)
      let donePatch :
          ∀ candidate, candidate ∈ done → G.FieldPatch :=
        fun candidate hcandidate =>
          realization.patchAt candidate (hdoneSubset hcandidate)
      let doneLegal :
          ∀ candidate hcandidate,
            G.patchLegal candidate (donePatch candidate hcandidate) :=
        fun candidate hcandidate =>
          hrealLegal ⟨candidate, hdoneSubset hcandidate⟩
      let current := cfg.withNodePatches done hdoneSubset donePatch doneLegal
      have hcurrentFrontier : node ∈ current.frontier :=
        cfg.withNodePatches_mem_frontier_of_not_mem
          hdoneSubset donePatch doneLegal hnodeFrontier hnodeNotDone
      let nodePatch := realization.patchAt node hnodeFrontier
      let mid :=
        current.withPatch nodePatch hcurrentFrontier
          (hrealLegal ⟨node, hnodeFrontier⟩)
      have hstep :
          mid ∈ (frontierStepNode G joint node current).support := by
        dsimp [mid, current, nodePatch, donePatch, doneLegal]
        exact frontierStepNode_support_withNodePatches_realization
          G hsound hjoint hrealSupp hrealLegal hdoneSubset
          hnodeFrontier hnodeNotDone
      let done' := insert node done
      have hdoneSubset' : done' ⊆ cfg.frontier := by
        intro candidate hcandidate
        rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hnodeFrontier
        · exact hdoneSubset hcandidate
      let donePatch' :
          ∀ candidate, candidate ∈ done' → G.FieldPatch :=
        fun candidate hcandidate =>
          realization.patchAt candidate (hdoneSubset' hcandidate)
      let doneLegal' :
          ∀ candidate hcandidate,
            G.patchLegal candidate (donePatch' candidate hcandidate) :=
        fun candidate hcandidate =>
          hrealLegal ⟨candidate, hdoneSubset' hcandidate⟩
      have hmid :
          mid = cfg.withNodePatches done' hdoneSubset'
            donePatch' doneLegal' := by
        dsimp [mid, current, nodePatch, donePatch, doneLegal, done',
          donePatch', doneLegal']
        exact withNodePatches_insert_realization_eq_withPatch
          G hrealLegal hdoneSubset hnodeFrontier hnodeNotDone
      have hrestSubset :
          ∀ candidate, candidate ∈ rest → candidate ∈ cfg.frontier := by
        intro candidate hcandidate
        exact hnodesSubset candidate (List.mem_cons_of_mem _ hcandidate)
      have hrestDisjoint :
          ∀ candidate, candidate ∈ rest → candidate ∉ done' := by
        intro candidate hcandidate hdone'
        rcases Finset.mem_insert.mp hdone' with hcandidateNode | hdoneOld
        · subst candidate
          exact hnodeNotRest hcandidate
        · exact hdisjoint candidate (List.mem_cons_of_mem _ hcandidate) hdoneOld
      have hrestCover :
          ∀ candidate, candidate ∈ cfg.frontier →
            candidate ∈ done' ∨ candidate ∈ rest := by
        intro candidate hcandidateFrontier
        rcases hcover candidate hcandidateFrontier with hdoneOld | hnodes
        · exact Or.inl (Finset.mem_insert_of_mem hdoneOld)
        · rcases List.mem_cons.mp hnodes with hcandidateNode | hrest
          · subst candidate
            exact Or.inl (Finset.mem_insert_self node done)
          · exact Or.inr hrest
      have hrest :
          cfg.extendFrontier realization hrealLegal ∈
            (scheduledFrontierTransitionGo G joint rest
              (cfg.withNodePatches done' hdoneSubset'
                donePatch' doneLegal')).support :=
        scheduledFrontierTransitionGo_support_extendFrontier_from_prefix
          G hsound hjoint hrealSupp hrealLegal rest done'
          hrestNodup hdoneSubset' hrestSubset hrestDisjoint hrestCover
      change cfg.extendFrontier realization hrealLegal ∈
        (scheduledFrontierTransitionGo G joint (node :: rest) current).support
      rw [scheduledFrontierTransitionGo.eq_def]
      rw [PMF.mem_support_bind_iff]
      refine ⟨mid, hstep, ?_⟩
      simpa [hmid]

/-- Every destination supported by the order-free frontier-realization
transition is also supported by the canonical scheduled representative. -/
theorem frontierRealizationTransition_support_scheduledFrontierTransition
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint })
    {dst : G.Configuration}
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    dst ∈ (scheduledFrontierTransition G cfg joint.1).support := by
  classical
  rcases frontierRealizationTransition_support_extend G cfg joint hdst with
    ⟨realization, hrealSupp, hrealLegal, hdstEq⟩
  subst dst
  unfold scheduledFrontierTransition
  exact scheduledFrontierTransitionGo_support_extendFrontier_from_prefix
    G hsound joint.2 hrealSupp hrealLegal cfg.frontier.toList ∅
    (by simpa using cfg.frontier.nodup_toList)
    (by intro node hnode; simp at hnode)
    (by
      intro node hnode
      exact Finset.mem_toList.mp hnode)
    (by simp)
    (by
      intro node hnode
      exact Or.inr (Finset.mem_toList.mpr hnode))

/-- Any explicit source-frontier schedule induces the same state kernel as the
canonical scheduled representative. Thus `frontier.toList` is a chosen
linearization, not semantic event-graph content. -/
theorem frontierTransitionWithSchedule_eq_scheduledFrontierTransition
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    (schedule : FrontierSchedule G cfg) :
    frontierTransitionWithSchedule G cfg joint schedule =
      scheduledFrontierTransition G cfg joint := by
  classical
  unfold frontierTransitionWithSchedule scheduledFrontierTransition
  exact scheduledFrontierTransitionGo_eq_of_perm_ready G hsound joint
    schedule.perm_toCanonical schedule.nodup
    (fun node hnode =>
      frontierNodeReady_of_legal G hlegal
        ((schedule.mem_iff node).1 hnode))

/-- The order-free frontier transition and the canonical scheduled
representative have the same destination distribution. -/
theorem frontierRealizationTransition_eq_scheduledFrontierTransition
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    frontierRealizationTransition G cfg joint =
      scheduledFrontierTransition G cfg joint.1 := by
  classical
  rw [← frontierProductConfigDist_empty_eq_frontierRealizationTransition
    G cfg joint]
  unfold scheduledFrontierTransition
  exact
    (scheduledFrontierTransitionGo_eq_frontierProductConfigDist
      G hsound joint.2 cfg.frontier.toList ∅
      (by simpa using cfg.frontier.nodup_toList)
      (by intro node hnode; simp at hnode)
      (by intro node hnode; exact Finset.mem_toList.mp hnode)
      (by intro node hnode hdone; simp at hdone)
      (by
        intro node hfrontier
        exact Or.inr (Finset.mem_toList.mpr hfrontier))
      (fun _ hnode => by simp at hnode)
      (fun _ hnode => by simp at hnode)).symm

/-- Distribution over the realized primitive event batch and destination of one
frontier step.

The sampler walks the source frontier in canonical order, sampling internal
kernels from the threaded current result as their nodes are reached and
recording the concrete primitive event that is executed. Under
`HasLocalFrontierSteps`, the kernel-stability lemmas make this canonical
walk a representative linearization of the local frontier step. -/
noncomputable def explicitFrontierBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G)) :
    PMF (List (G.toMachine iface).Event × G.Configuration) :=
  explicitFrontierBatchWalk G iface cfg joint

/-- Forgetting realized primitive events from the explicit batch distribution
recovers the canonical scheduled representative transition. -/
theorem explicitFrontierBatchDist_map_state_eq_scheduledFrontierTransition
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G)) :
    PMF.map Prod.snd (explicitFrontierBatchDist G iface cfg joint) =
      scheduledFrontierTransition G cfg joint := by
  classical
  unfold explicitFrontierBatchDist explicitFrontierBatchWalk
  unfold scheduledFrontierTransition
  exact explicitFrontierBatchGo_map_state G iface joint cfg.frontier.toList [] cfg

/-- Decorating every scheduled round destination with its realized primitive
event batch is exactly the operational explicit-batch distribution. -/
theorem scheduledFrontierTransition_map_realizedEventBatch_eq_explicitFrontierBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerFrontierAction G)) :
    PMF.map (fun dst => (realizedEventBatch G iface cfg joint dst, dst))
        (scheduledFrontierTransition G cfg joint) =
      explicitFrontierBatchDist G iface cfg joint := by
  classical
  unfold realizedEventBatch explicitFrontierBatchDist explicitFrontierBatchWalk
  unfold scheduledFrontierTransition
  simpa using
    (explicitFrontierBatchGo_eq_map_scheduledFrontierTransitionGo
      G iface joint cfg.frontier.toList []
      (by simpa using cfg.frontier.nodup_toList)
      (by
        intro node hnode
        simpa using hnode))

/-- Forgetting realized primitive events from the explicit batch distribution
recovers the order-free frontier transition. -/
theorem explicitFrontierBatchDist_map_state_eq_frontierRealizationTransition
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    PMF.map Prod.snd (explicitFrontierBatchDist G iface cfg joint.1) =
      frontierRealizationTransition G cfg joint := by
  rw [explicitFrontierBatchDist_map_state_eq_scheduledFrontierTransition]
  exact (frontierRealizationTransition_eq_scheduledFrontierTransition
    G hsound joint).symm

/-- Decorating every order-free frontier destination with its realized
primitive event batch is exactly the operational explicit-batch distribution. -/
theorem frontierRealizationTransition_map_realizedEventBatch_eq_explicitFrontierBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint }) :
    PMF.map (fun dst => (realizedEventBatch G iface cfg joint.1 dst, dst))
        (frontierRealizationTransition G cfg joint) =
      explicitFrontierBatchDist G iface cfg joint.1 := by
  rw [frontierRealizationTransition_eq_scheduledFrontierTransition
    G hsound joint]
  exact scheduledFrontierTransition_map_realizedEventBatch_eq_explicitFrontierBatchDist
    G iface cfg joint.1

/-- Every supported explicit realized batch is executable as a primitive
machine event trace from the round source to its recorded destination. -/
theorem explicitFrontierBatchDist_support_runEventsFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    {batch : List (G.toMachine iface).Event}
    (hsupp : (batch, dst) ∈
      (explicitFrontierBatchDist G iface cfg joint).support) :
    dst ∈ ((G.toMachine iface).runEventsFrom batch cfg).support := by
  classical
  unfold explicitFrontierBatchDist explicitFrontierBatchWalk at hsupp
  rcases explicitFrontierBatchGo_support_runEventsFrom_suffix
      G iface joint cfg.frontier.toList [] cfg hsupp with
    ⟨suffix, hbatch, hrun⟩
  rw [hbatch]
  simpa using hrun

/-- Under local frontier-step locality, every supported explicit realized batch
is a primitive machine run whose events are available at the states where they
are executed. -/
theorem explicitFrontierBatchDist_support_availableRunFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    {batch : List (G.toMachine iface).Event}
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    (hsupp : (batch, dst) ∈
      (explicitFrontierBatchDist G iface cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg batch dst := by
  classical
  unfold explicitFrontierBatchDist explicitFrontierBatchWalk at hsupp
  rcases explicitFrontierBatchGo_support_availableRunFrom_suffix
      G iface cfg joint hsound hlegal cfg.frontier.toList [] cfg
      (by simpa using cfg.frontier.nodup_toList)
      (by
        intro node hnode
        simpa using hnode)
      (by
        intro node hnode
        simpa using hnode)
      (by
        intro who action _ haction
        exact haction)
      hsupp with
    ⟨suffix, hbatch, hrun⟩
  simpa [hbatch] using hrun

/-- Nonzero-mass form of `explicitFrontierBatchDist_support_runEventsFrom`, useful
for callers phrased directly in PMF weights. -/
theorem explicitFrontierBatchDist_support_runEventsFrom_ne_zero
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    {batch : List (G.toMachine iface).Event}
    (hsupp : (batch, dst) ∈
      (explicitFrontierBatchDist G iface cfg joint).support) :
    ((G.toMachine iface).runEventsFrom batch cfg) dst ≠ 0 := by
  exact (PMF.mem_support_iff _ _).mp
    (explicitFrontierBatchDist_support_runEventsFrom G iface hsupp)

/-- Legal source rounds never emit the totality-only idle fallback in supported
explicit event batches. -/
theorem explicitFrontierBatchDist_support_no_idle
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    {batch : List (G.toMachine iface).Event}
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    (hsupp : (batch, dst) ∈
      (explicitFrontierBatchDist G iface cfg joint).support) :
    (Machine.Event.internal InternalEvent.idle :
      (G.toMachine iface).Event) ∉ batch := by
  classical
  unfold explicitFrontierBatchDist explicitFrontierBatchWalk at hsupp
  exact explicitFrontierBatchGo_support_no_idle
    G iface cfg joint hlegal cfg.frontier.toList []
    (by simpa using cfg.frontier.nodup_toList)
    (by
      intro node hnode
      simpa using hnode)
    (by
      intro node hnode
      simpa using hnode)
    (by simp)
    hsupp

/-- Support-facing bridge form of the decorated explicit-batch theorem. -/
theorem realizedEventBatch_mem_explicitFrontierBatchDist_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hdst : dst ∈ (scheduledFrontierTransition G cfg joint).support) :
    (realizedEventBatch G iface cfg joint dst, dst) ∈
      (explicitFrontierBatchDist G iface cfg joint).support := by
  classical
  unfold explicitFrontierBatchDist explicitFrontierBatchWalk
  unfold scheduledFrontierTransition at hdst
  simpa [realizedEventBatch] using
    (explicitFrontierBatchGo_support_of_scheduledFrontierTransitionGo_support
      G iface joint cfg.frontier.toList []
      (by simpa using cfg.frontier.nodup_toList)
      (by
        intro node hnode
        simpa using hnode)
      hdst)

/-- Order-free frontier destinations have the same realized primitive batch
witness as the canonical scheduled representative. -/
theorem realizedEventBatch_mem_explicitFrontierBatchDist_support_of_frontier
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg dst : G.Configuration}
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint })
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    (realizedEventBatch G iface cfg joint.1 dst, dst) ∈
      (explicitFrontierBatchDist G iface cfg joint.1).support :=
  realizedEventBatch_mem_explicitFrontierBatchDist_support G iface
    (frontierRealizationTransition_support_scheduledFrontierTransition
      G hsound joint hdst)

/-- Realized primitive batches extracted from the native order-free frontier
transition execute from the source configuration to the realized destination,
with every primitive event available at its execution state. -/
theorem realizedEventBatch_availableRunFrom_of_frontierRealizationTransition_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg dst : G.Configuration}
    (joint :
      { joint : JointAction (PlayerFrontierAction G) //
        JointActionLegal (PlayerFrontierAction G) (frontierActive G)
          Configuration.terminal (frontierAvailable G) cfg joint })
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg
      (realizedEventBatch G iface cfg joint.1 dst) dst :=
  explicitFrontierBatchDist_support_availableRunFrom G iface hsound joint.2
    (realizedEventBatch_mem_explicitFrontierBatchDist_support_of_frontier
      G iface hsound joint hdst)

/-- Legal supported scheduled frontier destinations have no totality-only idle fallback in
their realized primitive event batch. -/
theorem realizedEventBatch_no_idle_of_scheduledFrontierTransition_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerFrontierAction G)}
    (hlegal :
      JointActionLegal (PlayerFrontierAction G) (frontierActive G)
        Configuration.terminal (frontierAvailable G) cfg joint)
    (hdst : dst ∈ (scheduledFrontierTransition G cfg joint).support) :
    (Machine.Event.internal InternalEvent.idle :
      (G.toMachine iface).Event) ∉
      realizedEventBatch G iface cfg joint dst := by
  exact explicitFrontierBatchDist_support_no_idle G iface hlegal
    (realizedEventBatch_mem_explicitFrontierBatchDist_support
      G iface hdst)

end EventGraph

end Vegas
