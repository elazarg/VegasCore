import GameTheory.Core.JointAction
import Math.PMFProduct
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
      Fintype (Option (L.Val (G.fieldTy field))) :=
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

/-- Primitive event associated with one source round node after the destination
state is known. Internal nodes read back the realized patch from the destination
result; player nodes are determined by the joint round action. -/
noncomputable def realizedNodeEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
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

private noncomputable def explicitRoundBatchStep
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
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

private theorem explicitRoundBatchStep_eq_map_roundStepNode_of_frontier
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (node : G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration)
    (hfrontier : node ∈ current.frontier) :
    explicitRoundBatchStep G iface joint node (events, current) =
      PMF.map
        (fun next =>
          (events ++ [realizedNodeEvent G iface joint node next], next))
        (roundStepNode G joint node current) := by
  classical
  unfold explicitRoundBatchStep roundStepNode
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

private noncomputable def explicitRoundBatchGo
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (nodes : List G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration) :
    PMF (List (G.toMachine iface).Event × G.Configuration) :=
  match nodes with
  | [] => PMF.pure (events, current)
  | node :: rest =>
      (explicitRoundBatchStep G iface joint node (events, current)).bind
        fun next =>
          explicitRoundBatchGo G iface joint rest next.1 next.2

noncomputable def roundTransitionGo
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerRoundAction G))
    (nodes : List G.Node)
    (current : G.Configuration) :
    PMF G.Configuration :=
  match nodes with
  | [] => PMF.pure current
  | node :: rest =>
      (roundStepNode G joint node current).bind fun next =>
        roundTransitionGo G joint rest next

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

private theorem roundStepNode_result_eq_of_ne
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerRoundAction G))
    {node candidate : G.Node}
    (hne : candidate ≠ node)
    {current dst : G.Configuration}
    (hsupp : dst ∈ (roundStepNode G joint node current).support) :
    dst.result candidate = current.result candidate := by
  classical
  unfold roundStepNode at hsupp
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

private theorem roundStepNode_frontier_of_ne
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerRoundAction G))
    {node candidate : G.Node}
    {current dst : G.Configuration}
    (hcandidate : candidate ∈ current.frontier)
    (hne : candidate ≠ node)
    (hsupp : dst ∈ (roundStepNode G joint node current).support) :
    candidate ∈ dst.frontier := by
  classical
  unfold roundStepNode at hsupp
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

private theorem roundStepNode_preserves_available_of_ne
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (PlayerRoundAction G))
    {node : G.Node}
    {current mid : G.Configuration}
    (hmid : mid ∈ (roundStepNode G joint node current).support)
    {who : Player} {action : PlayerAction G who}
    (hne : action.node ≠ node)
    (haction : action ∈ available G current who) :
    action ∈ available G mid who := by
  classical
  unfold roundStepNode at hmid
  cases hactor : (G.sem node).actor with
  | some owner =>
      cases hmove : joint owner with
      | none =>
          have hdst : mid = current := by
            simpa [hactor, hmove] using hmid
          subst mid
          exact haction
      | some roundAction =>
          by_cases havailable :
              ({ node := node, patch := roundAction.patch node } :
                PlayerAction G owner) ∈ available G current owner
          · have hdst :
                mid =
                  current.withPatch (roundAction.patch node)
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

private def roundNodeReady
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerRoundAction G))
    (cfg : G.Configuration) (node : G.Node) : Prop :=
  node ∈ cfg.frontier ∧
    match (G.sem node).actor with
    | some who =>
        ∃ action : PlayerRoundAction G who,
          joint who = some action ∧
            ({ node := node, patch := action.patch node } :
              PlayerAction G who) ∈ available G cfg who
    | none => True

private theorem roundNodeReady_of_legal
    (G : Vegas.EventGraph Player L)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    {node : G.Node}
    (hfrontier : node ∈ cfg.frontier) :
    roundNodeReady G joint cfg node := by
  classical
  refine ⟨hfrontier, ?_⟩
  cases hactor : (G.sem node).actor with
  | none =>
      trivial
  | some who =>
      have hactive : who ∈ roundActive G cfg :=
        (mem_roundActive_iff G cfg who).mpr ⟨node, hfrontier, hactor⟩
      have hcoord := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ roundActive G cfg ∧
                (∀ {node},
                  node ∈ cfg.frontier →
                  (G.sem node).actor = some who →
                    G.patchLegal node (action.patch node) ∧
                      G.actionLegal cfg.result node (action.patch node)) := by
            simpa [hmove, roundAvailable] using hcoord
          have hnodeLegal := hpair.2 hfrontier hactor
          exact ⟨action, hmove,
            ⟨hfrontier, hactor, hnodeLegal.1, hnodeLegal.2⟩⟩

private theorem roundStepNode_preserves_ready_of_ne
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (PlayerRoundAction G))
    {node candidate : G.Node}
    {current mid : G.Configuration}
    (hmid : mid ∈ (roundStepNode G joint node current).support)
    (hne : candidate ≠ node)
    (hready : roundNodeReady G joint current candidate) :
    roundNodeReady G joint mid candidate := by
  classical
  rcases hready with ⟨hcandidate, hdata⟩
  refine ⟨roundStepNode_frontier_of_ne G joint hcandidate hne hmid, ?_⟩
  cases hactor : (G.sem candidate).actor with
  | none =>
      simp [hactor] at hdata ⊢
  | some who =>
      rcases (by simpa [hactor] using hdata) with
        ⟨action, hmove, havailable⟩
      exact ⟨action, hmove,
        roundStepNode_preserves_available_of_ne
          G hsound joint hmid hne havailable⟩

private theorem roundStepNode_comm_of_ready
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (PlayerRoundAction G))
    (cfg : G.Configuration)
    {left right : G.Node}
    (hne : left ≠ right)
    (hleftReady : roundNodeReady G joint cfg left)
    (hrightReady : roundNodeReady G joint cfg right) :
    (roundStepNode G joint left cfg).bind
        (fun mid => roundStepNode G joint right mid) =
      (roundStepNode G joint right cfg).bind
        (fun mid => roundStepNode G joint left mid) := by
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
          roundStepNode G joint left cfg =
            PMF.pure
              (cfg.withPatch (leftAction.patch left)
                hleftFrontier hleftLegal) := by
        simp [roundStepNode, hleftActor, hleftMove, stepPlay, hleftAvail]
      cases hrightActor : (G.sem right).actor with
      | some rightWho =>
          rcases (by simpa [hrightActor] using hrightData) with
            ⟨rightAction, hrightMove, hrightAvail⟩
          have hrightLegal : G.patchLegal right (rightAction.patch right) :=
            hrightAvail.2.2.1
          have hrightStep :
              roundStepNode G joint right cfg =
                PMF.pure
                  (cfg.withPatch (rightAction.patch right)
                    hrightFrontier hrightLegal) := by
            simp [roundStepNode, hrightActor, hrightMove, stepPlay, hrightAvail]
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
              roundStepNode G joint right cfgLeft =
                PMF.pure
                  (cfgLeft.withPatch (rightAction.patch right)
                    hrightAvailAfterLeft.1 hrightLegal) := by
            simp [roundStepNode, hrightActor, hrightMove, stepPlay,
              hrightAvailAfterLeft]
          have hleftStepAfterRight :
              roundStepNode G joint left cfgRight =
                PMF.pure
                  (cfgRight.withPatch (leftAction.patch left)
                    hleftAvailAfterRight.1 hleftLegal) := by
            simp [roundStepNode, hleftActor, hleftMove, stepPlay,
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
          unfold roundStepNode
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
              roundStepNode G joint right cfg =
                PMF.pure
                  (cfg.withPatch (rightAction.patch right)
                    hrightFrontier hrightLegal) := by
            simp [roundStepNode, hrightActor, hrightMove, stepPlay, hrightAvail]
          have hleftKernelStable :
              G.internalKernel left
                  (cfg.withPatch (rightAction.patch right)
                    hrightFrontier hrightLegal).result =
                G.internalKernel left cfg.result :=
            hsound.internalKernelStable cfg hrightFrontier hleftFrontier
              hne hrightLegal
          rw [hrightStep, PMF.pure_bind]
          unfold roundStepNode
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
          unfold roundStepNode
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

private theorem roundTransitionGo_eq_of_perm_ready
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (PlayerRoundAction G)) :
    ∀ {nodes₁ nodes₂ : List G.Node} {current : G.Configuration},
      nodes₁.Perm nodes₂ →
      nodes₁.Nodup →
      (∀ node, node ∈ nodes₁ → roundNodeReady G joint current node) →
        roundTransitionGo G joint nodes₁ current =
          roundTransitionGo G joint nodes₂ current := by
  intro nodes₁ nodes₂ current hperm
  induction hperm generalizing current with
  | nil =>
      intro _hnodup _hready
      rfl
  | cons node hperm ih =>
      intro hnodup hready
      have hnodupTail := (List.nodup_cons.mp hnodup).2
      have hnodeNotTail := (List.nodup_cons.mp hnodup).1
      simp only [roundTransitionGo]
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (roundStepNode G joint node current) _ _ ?_
      intro mid hmid
      exact ih hnodupTail (fun candidate hcandidate =>
        roundStepNode_preserves_ready_of_ne G hsound joint hmid
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
          roundNodeReady G joint current left := hready left (by simp)
      have hrightReady :
          roundNodeReady G joint current right := hready right (by simp)
      simp only [roundTransitionGo]
      rw [← PMF.bind_bind, ← PMF.bind_bind]
      rw [roundStepNode_comm_of_ready
        G hsound joint current hleftNeRight hleftReady hrightReady]
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hnodup hready
      have hnodupMid := h₁.nodup hnodup
      have hreadyMid := fun node hnode =>
        hready node ((h₁.mem_iff).2 hnode)
      exact (ih₁ hnodup hready).trans (ih₂ hnodupMid hreadyMid)

/-- Executing one frontier node does not change the internal kernel of a
different frontier node under local frontier-round soundness. -/
theorem roundStepNode_preserves_internalKernel_of_ne
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (PlayerRoundAction G))
    {node candidate : G.Node}
    {current mid : G.Configuration}
    (hmid : mid ∈ (roundStepNode G joint node current).support)
    (hcandidate : candidate ∈ current.frontier)
    (hne : candidate ≠ node) :
    G.internalKernel candidate mid.result =
      G.internalKernel candidate current.result := by
  classical
  unfold roundStepNode at hmid
  cases hactor : (G.sem node).actor with
  | some owner =>
      cases hmove : joint owner with
      | none =>
          have hdst : mid = current := by
            simpa [hactor, hmove] using hmid
          subst mid
          rfl
      | some roundAction =>
          by_cases havailable :
              ({ node := node, patch := roundAction.patch node } :
                PlayerAction G owner) ∈ available G current owner
          · have hdst :
                mid =
                  current.withPatch (roundAction.patch node)
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
theorem roundTransitionGo_preserves_internalKernel_of_not_mem
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (PlayerRoundAction G))
    (nodes : List G.Node)
    {candidate : G.Node}
    {current dst : G.Configuration}
    (hcandidate : candidate ∈ current.frontier)
    (hnotmem : candidate ∉ nodes)
    (hsupp : dst ∈ (roundTransitionGo G joint nodes current).support) :
    G.internalKernel candidate dst.result =
      G.internalKernel candidate current.result := by
  classical
  induction nodes generalizing current with
  | nil =>
      have hdst : dst = current := by
        simpa [roundTransitionGo] using hsupp
      subst dst
      rfl
  | cons node rest ih =>
      simp only [roundTransitionGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨mid, hmid, hdstRest⟩
      have hnotData : candidate ≠ node ∧ candidate ∉ rest := by
        simpa using hnotmem
      have hne : candidate ≠ node := by
        intro h
        exact hnotData.1 h
      have hcandidateMid : candidate ∈ mid.frontier :=
        roundStepNode_frontier_of_ne G joint hcandidate hne hmid
      have hkernelMid :
          G.internalKernel candidate mid.result =
            G.internalKernel candidate current.result :=
        roundStepNode_preserves_internalKernel_of_ne
          G hsound joint hmid hcandidate hne
      exact (ih hcandidateMid hnotData.2 hdstRest).trans hkernelMid

/-- A legal player action for a source-frontier node remains available after
recording any disjoint subset of the same source frontier. -/
theorem available_after_withNodePatches_of_not_mem
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
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
    (hsound : G.HasLocalFrontierRounds)
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

private theorem roundTransitionGo_result_eq_of_not_mem
    (G : Vegas.EventGraph Player L)
    (joint : JointAction (PlayerRoundAction G))
    {candidate : G.Node}
    (nodes : List G.Node)
    {current dst : G.Configuration}
    (hnotmem : candidate ∉ nodes)
    (hsupp : dst ∈ (roundTransitionGo G joint nodes current).support) :
    dst.result candidate = current.result candidate := by
  classical
  induction nodes generalizing current with
  | nil =>
      have hdst : dst = current := by
        simpa [roundTransitionGo] using hsupp
      subst dst
      rfl
  | cons node rest ih =>
      simp only [roundTransitionGo, PMF.mem_support_bind_iff] at hsupp
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
          roundStepNode_result_eq_of_ne G joint hne hmid

private theorem realizedNodeEvent_eq_of_result_eq
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
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

private theorem explicitRoundBatchStep_support_of_roundStepNode
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    {node : G.Node}
    {events : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hfrontier : node ∈ current.frontier)
    (hnext : next ∈ (roundStepNode G joint node current).support) :
    (events ++ [realizedNodeEvent G iface joint node next], next) ∈
      (explicitRoundBatchStep G iface joint node
        (events, current)).support := by
  classical
  rw [explicitRoundBatchStep_eq_map_roundStepNode_of_frontier
    G iface joint node events current hfrontier]
  exact (PMF.mem_support_map_iff _ _ _).2 ⟨next, hnext, rfl⟩

private theorem explicitRoundBatchStep_support_runEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (node : G.Node)
    {events events' : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hsupp :
      (events', next) ∈
        (explicitRoundBatchStep G iface joint node
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
              explicitRoundBatchStep G iface joint node (events, current) =
                PMF.pure
                  (events ++ [Machine.Event.internal InternalEvent.idle],
                    current) := by
            unfold explicitRoundBatchStep
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
              explicitRoundBatchStep G iface joint node (events, current) =
                PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current) := by
            unfold explicitRoundBatchStep
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
              explicitRoundBatchStep G iface joint node (events, current) =
                (G.internalKernel node current.result).bind fun patch =>
                  PMF.map
                    (fun next =>
                      (events ++ [internalPrimitiveEvent G iface node patch],
                        next))
                    (stepInternal G (InternalEvent.node node patch)
                      current) := by
            unfold explicitRoundBatchStep
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
              explicitRoundBatchStep G iface joint node (events, current) =
                PMF.pure
                  (events ++ [Machine.Event.internal InternalEvent.idle],
                    current) := by
            unfold explicitRoundBatchStep
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

private theorem explicitRoundBatchStep_support_availableRunEvent
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) source joint)
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
        (explicitRoundBatchStep G iface joint node
          (events, current)).support) :
    ∃ event : (G.toMachine iface).Event,
      events' = events ++ [event] ∧
        (G.toMachine iface).EventAvailable current event ∧
          next ∈ ((G.toMachine iface).step event current).support := by
  classical
  cases hactor : (G.sem node).actor with
  | some who =>
      have hactive : who ∈ roundActive G source := by
        rw [mem_roundActive_iff]
        exact ⟨node, hsource, hactor⟩
      have hlocal := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G source := by
            simpa [hmove] using hlocal
          exact False.elim (hnot hactive)
      | some action =>
          let event :=
            playerPrimitiveEvent G iface who node (action.patch node)
          have hdist :
              explicitRoundBatchStep G iface joint node (events, current) =
                PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current) := by
            unfold explicitRoundBatchStep
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
                who ∈ roundActive G source ∧
                  action ∈ roundAvailable G source who := by
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
          explicitRoundBatchStep G iface joint node (events, current) =
            (G.internalKernel node current.result).bind fun patch =>
              PMF.map
                (fun next =>
                  (events ++ [internalPrimitiveEvent G iface node patch],
                    next))
                (stepInternal G (InternalEvent.node node patch)
                  current) := by
        unfold explicitRoundBatchStep
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

private theorem explicitRoundBatchStep_support_no_idle
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (node : G.Node)
    {events events' : List (G.toMachine iface).Event}
    {current next : G.Configuration}
    (hcurrent : node ∈ current.frontier)
    (hsource : node ∈ source.frontier)
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) source joint)
    (hnoEvents :
      (Machine.Event.internal InternalEvent.idle :
        (G.toMachine iface).Event) ∉ events)
    (hsupp :
      (events', next) ∈
        (explicitRoundBatchStep G iface joint node
          (events, current)).support) :
    (Machine.Event.internal InternalEvent.idle :
      (G.toMachine iface).Event) ∉ events' := by
  classical
  cases hactor : (G.sem node).actor with
  | some who =>
      have hactive : who ∈ roundActive G source := by
        rw [mem_roundActive_iff]
        exact ⟨node, hsource, hactor⟩
      have hlocal := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G source := by
            simpa [hmove] using hlocal
          exact False.elim (hnot hactive)
      | some action =>
          let event :=
            playerPrimitiveEvent G iface who node (action.patch node)
          have hdist :
              explicitRoundBatchStep G iface joint node (events, current) =
                PMF.map (fun next => (events ++ [event], next))
                  (stepPlay G who
                    { node := node, patch := action.patch node }
                    current) := by
            unfold explicitRoundBatchStep
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
            explicitRoundBatchStep G iface joint node (events, current) =
              (G.internalKernel node current.result).bind fun patch =>
                PMF.map
                  (fun next =>
                    (events ++ [internalPrimitiveEvent G iface node patch],
                      next))
                  (stepInternal G (InternalEvent.node node patch)
                    current) := by
          unfold explicitRoundBatchStep
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

private theorem explicitRoundBatchGo_support_runEventsFrom_suffix
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G)) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      (current : G.Configuration)
      {batch : List (G.toMachine iface).Event}
      {dst : G.Configuration},
      (batch, dst) ∈
        (explicitRoundBatchGo G iface joint nodes events current).support →
        ∃ suffix : List (G.toMachine iface).Event,
          batch = events ++ suffix ∧
            dst ∈
              ((G.toMachine iface).runEventsFrom suffix current).support
  | [], events, current, batch, dst, hsupp => by
      have hpure :
          (batch, dst) ∈ (PMF.pure (events, current)).support := by
        simpa [explicitRoundBatchGo] using hsupp
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
      simp only [explicitRoundBatchGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨next, hstepMass, hrestMass⟩
      rcases next with ⟨events₁, mid⟩
      have hstepSupport :
          (events₁, mid) ∈
            (explicitRoundBatchStep G iface joint node
              (events, current)).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      have hrestSupport :
          (batch, dst) ∈
            (explicitRoundBatchGo G iface joint rest events₁ mid).support :=
        (PMF.mem_support_iff _ _).2 hrestMass
      rcases explicitRoundBatchStep_support_runEvent
          G iface joint node hstepSupport with
        ⟨event, hevents₁, hstep⟩
      rcases explicitRoundBatchGo_support_runEventsFrom_suffix
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

private theorem explicitRoundBatchGo_support_availableRunFrom_suffix
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (hsound : G.HasLocalFrontierRounds)
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) source joint) :
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
        (explicitRoundBatchGo G iface joint nodes events current).support →
        ∃ suffix : List (G.toMachine iface).Event,
          batch = events ++ suffix ∧
            (G.toMachine iface).AvailableRunFrom current suffix dst
  | [], events, current, batch, dst, _hnodup, _hsource, _hcurrent,
      _havailable, hsupp => by
      have hpure :
          (batch, dst) ∈ (PMF.pure (events, current)).support := by
        simpa [explicitRoundBatchGo] using hsupp
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
      simp only [explicitRoundBatchGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨next, hstepMass, hrestMass⟩
      rcases next with ⟨events₁, mid⟩
      have hstepSupport :
          (events₁, mid) ∈
            (explicitRoundBatchStep G iface joint node
              (events, current)).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      have hrestSupport :
          (batch, dst) ∈
            (explicitRoundBatchGo G iface joint rest events₁ mid).support :=
        (PMF.mem_support_iff _ _).2 hrestMass
      have hnodeCurrent : node ∈ current.frontier :=
        hcurrent node (by simp)
      have hnodeSource : node ∈ source.frontier :=
        hsource node (by simp)
      rcases explicitRoundBatchStep_support_availableRunEvent
          G iface source joint hlegal node
          (fun hnode haction => havailable (by simp [hnode]) haction)
          hnodeCurrent hnodeSource hstepSupport with
        ⟨event, hevents₁, heventAvailable, hstep⟩
      have hmidRound :
          mid ∈ (roundStepNode G joint node current).support := by
        have hstepSupport' := hstepSupport
        rw [explicitRoundBatchStep_eq_map_roundStepNode_of_frontier
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
        exact roundStepNode_frontier_of_ne
          G joint hcandidateCurrent hne hmidRound
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
        exact roundStepNode_preserves_available_of_ne
          G hsound joint hmidRound hne hactionCurrent
      subst events₁
      rcases explicitRoundBatchGo_support_availableRunFrom_suffix
          G iface source joint hsound hlegal rest
          (events ++ [event]) mid
          hrestNodup hrestSource hrestCurrent havailableMid
          hrestSupport with
        ⟨suffix, hbatch, hrun⟩
      refine ⟨[event] ++ suffix, ?_, ?_⟩
      · simpa [List.append_assoc] using hbatch
      · exact Machine.AvailableRunFrom.cons heventAvailable hstep hrun

private theorem explicitRoundBatchGo_support_of_roundTransitionGo_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G)) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      {current dst : G.Configuration},
      nodes.Nodup →
      (∀ node, node ∈ nodes → node ∈ current.frontier) →
      dst ∈ (roundTransitionGo G joint nodes current).support →
        (events ++ nodes.map (fun node =>
          realizedNodeEvent G iface joint node dst), dst) ∈
          (explicitRoundBatchGo G iface joint nodes events current).support
  | [], events, current, dst, _hnodup, _hfrontier, hdst => by
      have hdstEq : dst = current := by
        simpa [roundTransitionGo] using hdst
      subst dst
      simp [explicitRoundBatchGo]
  | node :: rest, events, current, dst, hnodup, hfrontier, hdst => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      simp only [roundTransitionGo, PMF.mem_support_bind_iff] at hdst
      rcases hdst with ⟨mid, hmid, hdstRest⟩
      have hnodeFrontier : node ∈ current.frontier :=
        hfrontier node (by simp)
      have hstepSupport :
          (events ++ [realizedNodeEvent G iface joint node mid], mid) ∈
            (explicitRoundBatchStep G iface joint node
              (events, current)).support :=
        explicitRoundBatchStep_support_of_roundStepNode
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
        exact roundStepNode_frontier_of_ne
          G joint hcandidateFrontier hne hmid
      have hrestSupport :
          ((events ++ [realizedNodeEvent G iface joint node mid]) ++
              rest.map (fun node =>
                realizedNodeEvent G iface joint node dst), dst) ∈
            (explicitRoundBatchGo G iface joint rest
              (events ++ [realizedNodeEvent G iface joint node mid])
              mid).support :=
        explicitRoundBatchGo_support_of_roundTransitionGo_support
          G iface joint rest
          (events ++ [realizedNodeEvent G iface joint node mid])
          hrestNodup hrestFrontier hdstRest
      have hresult :
          dst.result node = mid.result node :=
        roundTransitionGo_result_eq_of_not_mem
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
          ((explicitRoundBatchStep G iface joint node (events, current)).bind
            fun next =>
              explicitRoundBatchGo G iface joint rest next.1 next.2).support
      rw [PMF.mem_support_bind_iff]
      refine ⟨(events ++ [realizedNodeEvent G iface joint node mid], mid),
        hstepSupport, ?_⟩
      simpa [List.map, List.append_assoc, hevent] using hrestSupport

private theorem explicitRoundBatchGo_eq_map_roundTransitionGo
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G)) :
    ∀ (nodes : List G.Node)
      (events : List (G.toMachine iface).Event)
      {current : G.Configuration},
      nodes.Nodup →
      (∀ node, node ∈ nodes → node ∈ current.frontier) →
        PMF.map
            (fun dst =>
              (events ++ nodes.map (fun node =>
                realizedNodeEvent G iface joint node dst), dst))
            (roundTransitionGo G joint nodes current) =
          explicitRoundBatchGo G iface joint nodes events current
  | [], events, current, _hnodup, _hfrontier => by
      simp [roundTransitionGo, explicitRoundBatchGo, PMF.pure_map]
  | node :: rest, events, current, hnodup, hfrontier => by
      classical
      have hnodupData := List.nodup_cons.mp hnodup
      have hnodeNotRest : node ∉ rest := hnodupData.1
      have hrestNodup : rest.Nodup := hnodupData.2
      have hnodeFrontier : node ∈ current.frontier :=
        hfrontier node (by simp)
      rw [roundTransitionGo, explicitRoundBatchGo]
      rw [explicitRoundBatchStep_eq_map_roundStepNode_of_frontier
        G iface joint node events current hnodeFrontier]
      rw [PMF.map_bind]
      rw [PMF.bind_map]
      refine Math.ProbabilityMassFunction.bind_congr_on_support
        (roundStepNode G joint node current) _ _ ?_
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
        exact roundStepNode_frontier_of_ne
          G joint hcandidateFrontier hne hmid
      have hmap :
          PMF.map
              (fun dst =>
                (events ++ (node :: rest).map (fun node =>
                  realizedNodeEvent G iface joint node dst), dst))
              (roundTransitionGo G joint rest mid) =
            PMF.map
              (fun dst =>
                ((events ++ [realizedNodeEvent G iface joint node mid]) ++
                  rest.map (fun node =>
                    realizedNodeEvent G iface joint node dst), dst))
              (roundTransitionGo G joint rest mid) := by
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
          (roundTransitionGo G joint rest mid) _ _ ?_
        intro dst hdst
        have hresult :
            dst.result node = mid.result node :=
          roundTransitionGo_result_eq_of_not_mem
            G joint rest hnodeNotRest hdst
        have hevent :
            realizedNodeEvent G iface joint node dst =
              realizedNodeEvent G iface joint node mid :=
          realizedNodeEvent_eq_of_result_eq
            G iface joint node hresult
        simp [List.map, List.append_assoc, hevent]
      rw [hmap]
      exact explicitRoundBatchGo_eq_map_roundTransitionGo
        G iface joint rest
        (events ++ [realizedNodeEvent G iface joint node mid])
        hrestNodup hrestFrontier

/-- Stepwise distribution over a realized primitive event batch and destination
of one frontier round. Internal stochastic choices are sampled before their
deterministic primitive event is executed. This is the operational sampler used
to justify the exported decorated event-batch distribution. -/
private noncomputable def explicitRoundBatchWalk
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF (List (G.toMachine iface).Event × G.Configuration) :=
  explicitRoundBatchGo G iface joint cfg.frontier.toList [] cfg

/-- Extract the realized primitive event batch from a completed round source,
joint action, and destination. For internal nodes, the destination result
determines which patch was realized. -/
noncomputable def realizedEventBatch
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (dst : G.Configuration) :
    List (G.toMachine iface).Event :=
  cfg.frontier.toList.map fun node =>
    realizedNodeEvent G iface joint node dst

private theorem explicitRoundBatchStep_map_state
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (node : G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration) :
    PMF.map Prod.snd
        (explicitRoundBatchStep G iface joint node (events, current)) =
      roundStepNode G joint node current := by
  classical
  unfold explicitRoundBatchStep roundStepNode
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

private theorem explicitRoundBatchGo_support_no_idle
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (source : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) source joint) :
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
        (explicitRoundBatchGo G iface joint nodes events current).support →
        (Machine.Event.internal InternalEvent.idle :
          (G.toMachine iface).Event) ∉ batch
  | [], events, current, batch, dst, _hnodup, _hsource, _hcurrent,
      hnoEvents, hsupp => by
      have hpure :
          (batch, dst) ∈ (PMF.pure (events, current)).support := by
        simpa [explicitRoundBatchGo] using hsupp
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
      simp only [explicitRoundBatchGo, PMF.mem_support_bind_iff] at hsupp
      rcases hsupp with ⟨next, hstepMass, hrestMass⟩
      rcases next with ⟨events₁, mid⟩
      have hstepSupport :
          (events₁, mid) ∈
            (explicitRoundBatchStep G iface joint node
              (events, current)).support :=
        (PMF.mem_support_iff _ _).2 hstepMass
      have hrestSupport :
          (batch, dst) ∈
            (explicitRoundBatchGo G iface joint rest events₁ mid).support :=
        (PMF.mem_support_iff _ _).2 hrestMass
      have hnodeCurrent : node ∈ current.frontier :=
        hcurrent node (by simp)
      have hnodeSource : node ∈ source.frontier :=
        hsource node (by simp)
      have hnoEvents₁ :
          (Machine.Event.internal InternalEvent.idle :
            (G.toMachine iface).Event) ∉ events₁ :=
        explicitRoundBatchStep_support_no_idle
          G iface source joint node hnodeCurrent hnodeSource hlegal
          hnoEvents hstepSupport
      have hmidRound :
          mid ∈ (roundStepNode G joint node current).support := by
        have hmap :
            mid ∈
              (PMF.map Prod.snd
                (explicitRoundBatchStep G iface joint node
                  (events, current))).support :=
          (PMF.mem_support_map_iff _ _ _).2
            ⟨(events₁, mid), hstepSupport, rfl⟩
        rw [explicitRoundBatchStep_map_state] at hmap
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
        exact roundStepNode_frontier_of_ne
          G joint hcandidateCurrent hne hmidRound
      exact explicitRoundBatchGo_support_no_idle
        G iface source joint hlegal rest events₁ hrestNodup
        hrestSource hrestCurrent hnoEvents₁ hrestSupport

private theorem explicitRoundBatchGo_map_state
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (joint : JointAction (PlayerRoundAction G))
    (nodes : List G.Node)
    (events : List (G.toMachine iface).Event)
    (current : G.Configuration) :
    PMF.map Prod.snd
        (explicitRoundBatchGo G iface joint nodes events current) =
      roundTransitionGo G joint nodes current := by
  induction nodes generalizing events current with
  | nil =>
      simp [explicitRoundBatchGo, roundTransitionGo, PMF.pure_map]
  | cons node nodes ih =>
      classical
      rw [explicitRoundBatchGo, roundTransitionGo]
      rw [PMF.map_bind]
      simp_rw [ih]
      rw [← explicitRoundBatchStep_map_state G iface joint node events current]
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

/-- Execute a frontier round using an explicit schedule. -/
noncomputable def roundTransitionWithSchedule
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (schedule : FrontierSchedule G cfg) :
    PMF G.Configuration :=
  roundTransitionGo G joint schedule.nodes cfg

/-- Execute the current frontier in the canonical list order.

This is the scheduled operational representative used for primitive
event-batch witnesses. The native round-view transition is the order-free
`frontierRealizationTransition`; for graph views exposed through
`HasLocalFrontierRounds`, frontier independence justifies treating this
canonical list as proof/execution presentation rather than strategic content. -/
noncomputable def roundTransition
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF G.Configuration :=
  roundTransitionGo G joint cfg.frontier.toList cfg

/-- Patch distribution for one order-free frontier coordinate. Player-owned
coordinates are fixed by the legal joint action; internal coordinates use the
graph's internal kernel at the source configuration. -/
noncomputable def frontierPatchDist
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (_hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
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
    (joint : JointAction (PlayerRoundAction G))
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint) :
    PMF (FrontierRealization G cfg) :=
  PMF.map
    (fun patch : (idx : FrontierIndex G cfg) → G.FieldPatch =>
      { patch := patch })
    (Math.PMFProduct.pmfPi
      (fun idx => frontierPatchDist G cfg joint hlegal idx))

/-- Coordinate support for a sampled order-free frontier realization. -/
theorem frontierRealizationDist_support_coord
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G))
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
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
    (joint : JointAction (PlayerRoundAction G))
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
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
      have hactive : who ∈ roundActive G cfg :=
        (mem_roundActive_iff G cfg who).mpr ⟨idx.1, idx.2, hactor⟩
      have hcoordLegal := hlegal.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G cfg := by
            simpa [hmove] using hcoordLegal
          exact False.elim (hnot hactive)
      | some action =>
          have hround :
              who ∈ roundActive G cfg ∧
                action ∈ roundAvailable G cfg who := by
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

/-- Order-free state transition induced by a legal frontier realization. The
fallback branch is unreachable on the support of well-formed event graphs; it
keeps the function total over Lean's unconstrained PMF samples. -/
noncomputable def frontierRealizationTransition
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg joint }) :
    PMF G.Configuration := by
  classical
  exact
    (frontierRealizationDist G cfg joint.1 joint.2).bind fun realization =>
      if hlegal : realization.Legal then
        PMF.pure (cfg.extendFrontier realization hlegal)
      else
        PMF.pure cfg

/-- Supported order-free round destinations come from a supported legal
frontier realization. -/
theorem frontierRealizationTransition_support_extend
    (G : Vegas.EventGraph Player L) (cfg : G.Configuration)
    (joint :
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg joint })
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
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg₁ joint }}
    {joint₂ :
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg₂ joint }}
    (hjoint : joint₁.1 = joint₂.1) :
    frontierRealizationTransition G cfg₁ joint₁ =
      frontierRealizationTransition G cfg₂ joint₂ := by
  subst cfg₂
  apply congrArg (frontierRealizationTransition G cfg₁)
  exact Subtype.ext hjoint

private theorem roundStepNode_support_withNodePatches_realization
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hjoint :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
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
      (roundStepNode G joint node current).support := by
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
      have hactive : who ∈ roundActive G cfg :=
        (mem_roundActive_iff G cfg who).mpr ⟨node, hnodeFrontier, hactor⟩
      have hcoordLegal := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ roundActive G cfg := by
            simpa [hmove] using hcoordLegal
          exact False.elim (hnot hactive)
      | some action =>
          have hround :
              who ∈ roundActive G cfg ∧
                action ∈ roundAvailable G cfg who := by
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
          rw [show roundStepNode G joint node current =
              stepPlay G who { node := node, patch := action.patch node }
                current by
            simp [roundStepNode, hactor, hmove]]
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
      rw [roundStepNode, hactor]
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

private theorem roundTransitionGo_support_extendFrontier_from_prefix
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hjoint :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
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
          (roundTransitionGo G joint nodes
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
      simp [roundTransitionGo, heq]
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
          mid ∈ (roundStepNode G joint node current).support := by
        dsimp [mid, current, nodePatch, donePatch, doneLegal]
        exact roundStepNode_support_withNodePatches_realization
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
            (roundTransitionGo G joint rest
              (cfg.withNodePatches done' hdoneSubset'
                donePatch' doneLegal')).support :=
        roundTransitionGo_support_extendFrontier_from_prefix
          G hsound hjoint hrealSupp hrealLegal rest done'
          hrestNodup hdoneSubset' hrestSubset hrestDisjoint hrestCover
      change cfg.extendFrontier realization hrealLegal ∈
        (roundTransitionGo G joint (node :: rest) current).support
      rw [roundTransitionGo.eq_def]
      rw [PMF.mem_support_bind_iff]
      refine ⟨mid, hstep, ?_⟩
      simpa [hmid]

/-- Every destination supported by the order-free frontier-realization
transition is also supported by the canonical scheduled representative. -/
theorem frontierRealizationTransition_support_roundTransition
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    {cfg : G.Configuration}
    (joint :
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg joint })
    {dst : G.Configuration}
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    dst ∈ (roundTransition G cfg joint.1).support := by
  classical
  rcases frontierRealizationTransition_support_extend G cfg joint hdst with
    ⟨realization, hrealSupp, hrealLegal, hdstEq⟩
  subst dst
  unfold roundTransition
  exact roundTransitionGo_support_extendFrontier_from_prefix
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
theorem roundTransitionWithSchedule_eq_roundTransition
    (G : Vegas.EventGraph Player L)
    (hsound : G.HasLocalFrontierRounds)
    {cfg : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    (schedule : FrontierSchedule G cfg) :
    roundTransitionWithSchedule G cfg joint schedule =
      roundTransition G cfg joint := by
  classical
  unfold roundTransitionWithSchedule roundTransition
  exact roundTransitionGo_eq_of_perm_ready G hsound joint
    schedule.perm_toCanonical schedule.nodup
    (fun node hnode =>
      roundNodeReady_of_legal G hlegal
        ((schedule.mem_iff node).1 hnode))

/-- Distribution over the realized primitive event batch and destination of one
frontier round.

The sampler walks the source frontier in canonical order, sampling internal
kernels from the threaded current result as their nodes are reached and
recording the concrete primitive event that is executed. Under
`HasLocalFrontierRounds`, the kernel-stability lemmas make this canonical
walk a representative linearization of the local frontier round. -/
noncomputable def explicitRoundBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF (List (G.toMachine iface).Event × G.Configuration) :=
  explicitRoundBatchWalk G iface cfg joint

/-- Forgetting realized primitive events from the explicit batch distribution
recovers the canonical scheduled representative transition. -/
theorem explicitRoundBatchDist_map_state_eq_roundTransition
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF.map Prod.snd (explicitRoundBatchDist G iface cfg joint) =
      roundTransition G cfg joint := by
  classical
  unfold explicitRoundBatchDist explicitRoundBatchWalk
  unfold roundTransition
  exact explicitRoundBatchGo_map_state G iface joint cfg.frontier.toList [] cfg

/-- Decorating every scheduled round destination with its realized primitive
event batch is exactly the operational explicit-batch distribution. -/
theorem roundTransition_map_realizedEventBatch_eq_explicitRoundBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (PlayerRoundAction G)) :
    PMF.map (fun dst => (realizedEventBatch G iface cfg joint dst, dst))
        (roundTransition G cfg joint) =
      explicitRoundBatchDist G iface cfg joint := by
  classical
  unfold realizedEventBatch explicitRoundBatchDist explicitRoundBatchWalk
  unfold roundTransition
  simpa using
    (explicitRoundBatchGo_eq_map_roundTransitionGo
      G iface joint cfg.frontier.toList []
      (by simpa using cfg.frontier.nodup_toList)
      (by
        intro node hnode
        simpa using hnode))

/-- Every supported explicit realized batch is executable as a primitive
machine event trace from the round source to its recorded destination. -/
theorem explicitRoundBatchDist_support_runEventsFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    {batch : List (G.toMachine iface).Event}
    (hsupp : (batch, dst) ∈
      (explicitRoundBatchDist G iface cfg joint).support) :
    dst ∈ ((G.toMachine iface).runEventsFrom batch cfg).support := by
  classical
  unfold explicitRoundBatchDist explicitRoundBatchWalk at hsupp
  rcases explicitRoundBatchGo_support_runEventsFrom_suffix
      G iface joint cfg.frontier.toList [] cfg hsupp with
    ⟨suffix, hbatch, hrun⟩
  rw [hbatch]
  simpa using hrun

/-- Under local frontier rounds, every supported explicit realized batch
is a primitive machine run whose events are available at the states where they
are executed. -/
theorem explicitRoundBatchDist_support_availableRunFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    {batch : List (G.toMachine iface).Event}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    (hsupp : (batch, dst) ∈
      (explicitRoundBatchDist G iface cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg batch dst := by
  classical
  unfold explicitRoundBatchDist explicitRoundBatchWalk at hsupp
  rcases explicitRoundBatchGo_support_availableRunFrom_suffix
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

/-- Nonzero-mass form of `explicitRoundBatchDist_support_runEventsFrom`, useful
for callers phrased directly in PMF weights. -/
theorem explicitRoundBatchDist_support_runEventsFrom_ne_zero
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    {batch : List (G.toMachine iface).Event}
    (hsupp : (batch, dst) ∈
      (explicitRoundBatchDist G iface cfg joint).support) :
    ((G.toMachine iface).runEventsFrom batch cfg) dst ≠ 0 := by
  exact (PMF.mem_support_iff _ _).mp
    (explicitRoundBatchDist_support_runEventsFrom G iface hsupp)

/-- Legal source rounds never emit the totality-only idle fallback in supported
explicit event batches. -/
theorem explicitRoundBatchDist_support_no_idle
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    {batch : List (G.toMachine iface).Event}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    (hsupp : (batch, dst) ∈
      (explicitRoundBatchDist G iface cfg joint).support) :
    (Machine.Event.internal InternalEvent.idle :
      (G.toMachine iface).Event) ∉ batch := by
  classical
  unfold explicitRoundBatchDist explicitRoundBatchWalk at hsupp
  exact explicitRoundBatchGo_support_no_idle
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
theorem realizedEventBatch_mem_explicitRoundBatchDist_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hdst : dst ∈ (roundTransition G cfg joint).support) :
    (realizedEventBatch G iface cfg joint dst, dst) ∈
      (explicitRoundBatchDist G iface cfg joint).support := by
  classical
  unfold explicitRoundBatchDist explicitRoundBatchWalk
  unfold roundTransition at hdst
  simpa [realizedEventBatch] using
    (explicitRoundBatchGo_support_of_roundTransitionGo_support
      G iface joint cfg.frontier.toList []
      (by simpa using cfg.frontier.nodup_toList)
      (by
        intro node hnode
        simpa using hnode)
      hdst)

/-- Order-free round destinations have the same realized primitive batch
witness as the canonical scheduled representative. -/
theorem realizedEventBatch_mem_explicitRoundBatchDist_support_of_frontier
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds)
    {cfg dst : G.Configuration}
    (joint :
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg joint })
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    (realizedEventBatch G iface cfg joint.1 dst, dst) ∈
      (explicitRoundBatchDist G iface cfg joint.1).support :=
  realizedEventBatch_mem_explicitRoundBatchDist_support G iface
    (frontierRealizationTransition_support_roundTransition
      G hsound joint hdst)

/-- Realized primitive batches extracted from the native order-free frontier
transition execute from the source configuration to the realized destination,
with every primitive event available at its execution state. -/
theorem realizedEventBatch_availableRunFrom_of_frontierRealizationTransition_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds)
    {cfg dst : G.Configuration}
    (joint :
      { joint : JointAction (PlayerRoundAction G) //
        JointActionLegal (PlayerRoundAction G) (roundActive G)
          Configuration.terminal (roundAvailable G) cfg joint })
    (hdst : dst ∈ (frontierRealizationTransition G cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg
      (realizedEventBatch G iface cfg joint.1 dst) dst :=
  explicitRoundBatchDist_support_availableRunFrom G iface hsound joint.2
    (realizedEventBatch_mem_explicitRoundBatchDist_support_of_frontier
      G iface hsound joint hdst)

/-- Legal supported round destinations have no totality-only idle fallback in
their realized primitive event batch. -/
theorem realizedEventBatch_no_idle_of_roundTransition_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    {cfg dst : G.Configuration}
    {joint : JointAction (PlayerRoundAction G)}
    (hlegal :
      JointActionLegal (PlayerRoundAction G) (roundActive G)
        Configuration.terminal (roundAvailable G) cfg joint)
    (hdst : dst ∈ (roundTransition G cfg joint).support) :
    (Machine.Event.internal InternalEvent.idle :
      (G.toMachine iface).Event) ∉
      realizedEventBatch G iface cfg joint dst := by
  exact explicitRoundBatchDist_support_no_idle G iface hlegal
    (realizedEventBatch_mem_explicitRoundBatchDist_support
      G iface hdst)

end EventGraph

end Vegas
