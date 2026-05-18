import Vegas.EventGraph.Frontier
import Vegas.GameBridge.FOSG.Basic

/-!
# FOSG bridge for event graphs

This module exposes local event-graph frontier steps as bounded FOSG rounds
and connects those strategic rounds back to primitive machine traces.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- FOSG presentation of a protocol-graph machine by local frontier steps. -/
noncomputable def toFOSGView
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) :
    (G.toMachine iface).FOSGView where
  Act := PlayerFrontierAction G
  active := frontierActive G
  availableActions := frontierAvailable G
  transition := fun cfg action => frontierRealizationTransition G cfg action
  reward := fun _ _ dst who => iface.utility (iface.outcome dst) who
  terminal_active_eq_empty := by
    intro cfg hterminal
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who hmem
    rcases (mem_frontierActive_iff G cfg who).mp hmem with
      ⟨node, hfrontier, _hactor⟩
    exact (cfg.not_terminal_of_mem_frontier hfrontier) hterminal
  nonterminal_exists_legal := by
    intro cfg hterminal
    classical
    let mkPatch (who : Player) (node : G.Node) : G.FieldPatch :=
      if h : node ∈ cfg.frontier ∧ (G.sem node).actor = some who then
        Classical.choose (hsound.availablePlayerActions cfg h.1 h.2)
      else
        fun _ => none
    let joint : JointAction (PlayerFrontierAction G) := fun who =>
      if who ∈ frontierActive G cfg then
        some { patch := mkPatch who }
      else
        none
    refine ⟨joint, hterminal, ?_⟩
    intro who
    by_cases hactive : who ∈ frontierActive G cfg
    · have hjoint : joint who = some { patch := mkPatch who } := by
        simp [joint, hactive]
      rw [hjoint]
      refine ⟨hactive, ?_⟩
      intro node hfrontier hactor
      have hnode : node ∈ cfg.frontier ∧ (G.sem node).actor = some who :=
        ⟨hfrontier, hactor⟩
      change
        G.patchLegal node (mkPatch who node) ∧
          G.actionLegal cfg.result node (mkPatch who node)
      unfold mkPatch
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
graph-level `frontierMenu`.  Bridges the strategic FOSG carrier (which pairs
each player's optional round move with a `none` for inactive strategic rounds) and the
direct configuration-level menu. -/
@[simp] theorem toFOSGView_toFOSG_availableMovesAtState_eq_frontierMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    (cfg : G.Configuration) (who : Player) :
    (G.toFOSGView iface hsound).toFOSG.availableMovesAtState cfg who =
      G.frontierMenu cfg who := by
  ext move
  cases move <;> rfl

/-- The bounded-FOSG version: before the horizon cutoff, optional frontier moves
agree with the player-facing graph menu. -/
theorem toFOSGView_toBoundedFOSG_availableMovesAtState_eq_frontierMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat) (who : Player)
    (state : (G.toMachine iface).BoundedState horizon)
    (hcut : ¬ horizon ≤ state.depth) :
    ((G.toFOSGView iface hsound).toBoundedFOSG horizon).availableMovesAtState
        state who =
      G.frontierMenu state.state who := by
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

/-- Primitive event batches extracted from a bounded graph-FOSG step list.

Each bounded FOSG step is one frontier step.  Internal chance patches are read
from the realized destination, so the batch is concrete. -/
noncomputable def boundedFOSGStepEventBatches
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    (steps :
      List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)) :
    List (List (G.toMachine iface).Event) :=
  steps.map fun step =>
    realizedEventBatch G iface step.src.state step.act.1 step.dst.state

/-- Primitive event batches extracted from a bounded graph-FOSG history. -/
noncomputable def boundedFOSGHistoryEventBatches
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    List (List (G.toMachine iface).Event) :=
  boundedFOSGStepEventBatches G iface hsound horizon h.steps

/-- The primitive batch extracted from one supported bounded FOSG step is an
available machine run from the step source to the step destination. -/
theorem boundedFOSGStepEventBatch_availableRunFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    (step :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)) :
    (G.toMachine iface).AvailableRunFrom step.src.state
      (realizedEventBatch G iface step.src.state step.act.1
        step.dst.state)
      step.dst.state := by
  classical
  let view := G.toFOSGView iface hsound
  let joint := view.boundedActionToAction horizon step.src step.act
  have hmemBounded :
      step.dst ∈
        ((view.toBoundedFOSG horizon).transition step.src step.act).support :=
    (PMF.mem_support_iff _ _).2 step.support
  have hmemState :
      step.dst.state ∈
        (PMF.map (fun bounded => bounded.state)
          ((view.toBoundedFOSG horizon).transition step.src step.act)).support :=
    (PMF.mem_support_map_iff _ _ _).2
      ⟨step.dst, hmemBounded, rfl⟩
  have hmap :=
    view.toBoundedFOSG_transition_map_state horizon step.src step.act
  rw [hmap] at hmemState
  have hdst :
      step.dst.state ∈
        (frontierRealizationTransition G step.src.state joint).support := by
    simpa [view, joint, toFOSGView] using hmemState
  simpa [joint, Machine.FOSGView.boundedActionToAction] using
    (realizedEventBatch_availableRunFrom_of_frontierRealizationTransition_support
      G iface hsound joint hdst)

/-- Event batches extracted from a bounded FOSG step chain form an available
primitive batch run between the chain endpoints. -/
theorem boundedFOSGStepEventBatches_availableRunBatchesFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps :
        List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)},
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).StepChainFrom
        start steps →
        (G.toMachine iface).AvailableRunBatchesFrom start.state
          (boundedFOSGStepEventBatches G iface hsound horizon steps)
          ((((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
            start steps).state)
  | start, [], _hchain => by
      simp [boundedFOSGStepEventBatches, GameTheory.FOSG.lastStateFrom,
        Machine.AvailableRunBatchesFrom.nil]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst start
      change (G.toMachine iface).AvailableRunBatchesFrom step.src.state
        (realizedEventBatch G iface step.src.state step.act.1
          step.dst.state ::
            boundedFOSGStepEventBatches G iface hsound horizon steps)
        ((((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
          step.dst steps).state)
      exact Machine.AvailableRunBatchesFrom.cons
        (boundedFOSGStepEventBatch_availableRunFrom
          G iface hsound horizon step)
        (boundedFOSGStepEventBatches_availableRunBatchesFrom
          G iface hsound horizon htail)

/-- Nonzero-support form of
`boundedFOSGStepEventBatches_availableRunBatchesFrom`. -/
theorem boundedFOSGStepEventBatches_lastState_mem_runEventBatchesFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    {start : (G.toMachine iface).BoundedState horizon}
    {steps :
      List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)}
    (hchain :
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).StepChainFrom
        start steps) :
    ((((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
      start steps).state) ∈
      ((G.toMachine iface).runEventBatchesFrom
        (boundedFOSGStepEventBatches G iface hsound horizon steps)
        start.state).support :=
  Machine.AvailableRunBatchesFrom.mem_runEventBatchesFrom_support
    (boundedFOSGStepEventBatches_availableRunBatchesFrom
      G iface hsound horizon hchain)

/-- Event batches extracted from a bounded FOSG history form an available
primitive batch run from the machine initial state to the history state. -/
theorem boundedFOSGHistory_availableRunBatchesFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    (G.toMachine iface).AvailableRunBatchesFrom (G.toMachine iface).init
      (boundedFOSGHistoryEventBatches G iface hsound horizon h)
      h.lastState.state := by
  simpa [boundedFOSGHistoryEventBatches] using
    (boundedFOSGStepEventBatches_availableRunBatchesFrom
      G iface hsound horizon h.chain)

/-- Nonzero-support form of
`boundedFOSGHistory_availableRunBatchesFrom`. -/
theorem boundedFOSGHistory_state_mem_runEventBatchesFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((G.toMachine iface).runEventBatchesFrom
        (boundedFOSGHistoryEventBatches G iface hsound horizon h)
        (G.toMachine iface).init).support :=
  Machine.AvailableRunBatchesFrom.mem_runEventBatchesFrom_support
    (boundedFOSGHistory_availableRunBatchesFrom G iface hsound horizon h)

/-- History-dependent event-batched primitive trace distribution induced by a
bounded graph-FOSG behavioral profile.

The state of this process is still the FOSG history: strategies are allowed to
depend on information-state history.  The machine contribution at each
nonterminal FOSG round is the primitive event batch selected by that round. -/
noncomputable def boundedFOSGEventBatchTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
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
        (boundedFOSGHistoryEventBatches G iface hsound horizon h,
          h.lastState.state)
  | n + 1, h => by
      classical
      exact
        if hterm :
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
              h.lastState then
          PMF.pure
            (boundedFOSGHistoryEventBatches G iface hsound horizon h,
              h.lastState.state)
        else
          (GameTheory.FOSG.legalActionLaw
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon)
            σ h hterm).bind fun action =>
            (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
              h.lastState action).bind fun dst =>
                boundedFOSGEventBatchTraceDistFrom
                  G iface hsound horizon σ n
                  (h.extendByOutcome action dst)

@[simp] theorem boundedFOSGEventBatchTraceDistFrom_zero
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    boundedFOSGEventBatchTraceDistFrom G iface hsound horizon σ 0 h =
      PMF.pure
        (boundedFOSGHistoryEventBatches G iface hsound horizon h,
          h.lastState.state) := rfl

theorem boundedFOSGEventBatchTraceDistFrom_succ_terminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
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
    boundedFOSGEventBatchTraceDistFrom G iface hsound horizon σ (n + 1) h =
      PMF.pure
        (boundedFOSGHistoryEventBatches G iface hsound horizon h,
          h.lastState.state) := by
  have hterm' :
      (G.toFOSGView iface hsound).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGEventBatchTraceDistFrom, hterm']

theorem boundedFOSGEventBatchTraceDistFrom_succ_nonterminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
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
    boundedFOSGEventBatchTraceDistFrom G iface hsound horizon σ (n + 1) h =
      (GameTheory.FOSG.legalActionLaw
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)
        σ h hterm).bind fun action =>
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action).bind fun dst =>
            boundedFOSGEventBatchTraceDistFrom
              G iface hsound horizon σ n
              (h.extendByOutcome action dst) := by
  have hterm' :
      ¬ (G.toFOSGView iface hsound).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGEventBatchTraceDistFrom, hterm']

/-- Bounded graph-FOSG execution, projected to extracted primitive event batches
and checkpoint state, equals the history-dependent event-batch machine trace
distribution induced by the same behavioral profile. -/
theorem boundedFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
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
            (boundedFOSGHistoryEventBatches G iface hsound horizon h',
              h'.lastState.state))
          (GameTheory.FOSG.History.runDistFrom
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h) =
        boundedFOSGEventBatchTraceDistFrom G iface hsound horizon σ n h
  | 0, h => by
      rw [GameTheory.FOSG.History.runDistFrom_zero]
      rw [boundedFOSGEventBatchTraceDistFrom_zero]
      rw [PMF.pure_map]
  | n + 1, h => by
      let BFOSG := (G.toFOSGView iface hsound).toBoundedFOSG horizon
      by_cases hterm : BFOSG.terminal h.lastState
      · rw [GameTheory.FOSG.History.runDistFrom_succ_terminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGEventBatchTraceDistFrom_succ_terminal
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) σ n h hterm]
        rw [PMF.pure_map]
      · rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGEventBatchTraceDistFrom_succ_nonterminal
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) σ n h hterm]
        rw [PMF.map_bind]
        congr
        funext action
        rw [PMF.map_bind]
        congr
        funext dst
        exact boundedFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
          G iface hsound horizon σ n (h.extendByOutcome action dst)

/-- Outcome projection of bounded graph-FOSG execution equals outcome
projection of the corresponding history-dependent event-batch machine trace
distribution. -/
theorem boundedFOSG_runDistFrom_map_outcome_eq_eventBatchTraceDistFrom_map_outcome
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
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
        (boundedFOSGEventBatchTraceDistFrom G iface hsound horizon σ n h) := by
  let project :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History) →
        List (List (G.toMachine iface).Event) × (G.toMachine iface).State :=
    fun h' =>
      (boundedFOSGHistoryEventBatches G iface hsound horizon h',
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
        (boundedFOSGEventBatchTraceDistFrom G iface hsound horizon σ n h) := by
          rw [boundedFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
            (G := G) (iface := iface) (hsound := hsound)
            (horizon := horizon) σ n h]

/-- Public bounded behavioral outcome kernel of a graph-FOSG view, computed as
the machine outcome map of the induced event-batched primitive trace distribution. -/
theorem boundedFOSG_outcomeFromBehavioral_eq_eventBatchTraceDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
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
        (boundedFOSGEventBatchTraceDistFrom G iface hsound horizon β.extend steps
          (GameTheory.FOSG.History.nil
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon))) := by
  simpa [Machine.FOSGView.boundedOutcomeFromBehavioral,
    Machine.FOSGView.boundedHistoryOutcome, GameTheory.FOSG.runDist] using
    (boundedFOSG_runDistFrom_map_outcome_eq_eventBatchTraceDistFrom_map_outcome
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon) β.extend steps
      (GameTheory.FOSG.History.nil
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)))

/-- Public bounded pure outcome kernel of a graph-FOSG view, computed as the
machine outcome map of the event-batched primitive trace distribution induced by the
pure profile's behavioral embedding. -/
theorem boundedFOSG_outcomeFromPure_eq_eventBatchTraceDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierSteps) (horizon : Nat)
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
        (boundedFOSGEventBatchTraceDistFrom G iface hsound horizon
          (GameTheory.FOSG.legalPureToBehavioral
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) π.extend)
          steps
          (GameTheory.FOSG.History.nil
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon))) := by
  simpa [Machine.FOSGView.boundedOutcomeFromPure,
    Machine.FOSGView.boundedHistoryOutcome, GameTheory.FOSG.runDist] using
    (boundedFOSG_runDistFrom_map_outcome_eq_eventBatchTraceDistFrom_map_outcome
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon)
      (GameTheory.FOSG.legalPureToBehavioral
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon) π.extend)
      steps
      (GameTheory.FOSG.History.nil
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)))

end EventGraph

end Vegas
