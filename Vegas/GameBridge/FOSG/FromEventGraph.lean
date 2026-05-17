import Vegas.EventGraph.Round
import Vegas.GameBridge.FOSG.Basic

/-!
# FOSG bridge for event graphs

This module exposes independent event-graph frontiers as bounded FOSG rounds
and connects those rounds back to primitive machine traces.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- FOSG presentation of a protocol-graph machine by independent frontier rounds. -/
noncomputable def toFOSGView
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) :
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
    let mkPatch (who : Player) (node : G.Node) : G.FieldPatch :=
      if h : node ∈ cfg.frontier ∧ (G.sem node).actor = some who then
        Classical.choose (hsound.availablePlayerActions cfg h.1 h.2)
      else
        fun _ => none
    let joint : JointAction (PlayerRoundAction G) := fun who =>
      if who ∈ roundActive G cfg then
        some { patch := mkPatch who }
      else
        none
    refine ⟨joint, hterminal, ?_⟩
    intro who
    by_cases hactive : who ∈ roundActive G cfg
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
graph-level `roundMenu`.  Bridges the strategic FOSG carrier (which pairs
each player's optional round move with a `none` for inactive rounds) and the
direct configuration-level menu. -/
@[simp] theorem toFOSGView_toFOSG_availableMovesAtState_eq_roundMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds)
    (cfg : G.Configuration) (who : Player) :
    (G.toFOSGView iface hsound).toFOSG.availableMovesAtState cfg who =
      G.roundMenu cfg who := by
  ext move
  cases move <;> rfl

/-- The bounded-FOSG version: before the horizon cutoff, optional round moves
agree with the player-facing graph menu. -/
theorem toFOSGView_toBoundedFOSG_availableMovesAtState_eq_roundMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat) (who : Player)
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
is the state marginal of the explicit realized-batch distribution. -/
theorem toFOSGView_toBoundedFOSG_transition_map_state_eq_explicitRoundBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action) =
      PMF.map Prod.snd
        (explicitRoundBatchDist G iface state.state action.1) := by
  rw [Machine.FOSGView.toBoundedFOSG_transition_map_state]
  change
    roundTransition G state.state action.1 =
      PMF.map Prod.snd
        (explicitRoundBatchDist G iface state.state action.1)
  exact (explicitRoundBatchDist_map_state_eq_roundTransition
    G iface state.state action.1).symm

/-- One bounded graph-FOSG transition, decorated with the realized primitive
event batch extracted from its destination, is exactly the explicit realized
batch distribution for the underlying frontier round. -/
theorem toFOSGView_toBoundedFOSG_transition_map_realizedBatch_state_eq_explicitRoundBatchDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map
        (fun bounded =>
          (realizedEventBatch G iface state.state action.1 bounded.state,
            bounded.state))
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action) =
      explicitRoundBatchDist G iface state.state action.1 := by
  let decorate : G.Configuration → List (G.toMachine iface).Event × G.Configuration :=
    fun dst => (realizedEventBatch G iface state.state action.1 dst, dst)
  calc
    PMF.map
        (fun bounded =>
          (realizedEventBatch G iface state.state action.1 bounded.state,
            bounded.state))
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action)
        = PMF.map decorate
            (PMF.map (fun bounded => bounded.state)
              (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
                state action)) := by
          exact (PMF.map_comp
            (p := (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
              state action))
            (f := fun bounded => bounded.state)
            (g := decorate)).symm
    _ = PMF.map decorate (roundTransition G state.state action.1) := by
          apply congrArg (PMF.map decorate)
          simpa [toFOSGView] using
            (Machine.FOSGView.toBoundedFOSG_transition_map_state
              (G.toFOSGView iface hsound) horizon state action)
    _ = explicitRoundBatchDist G iface state.state action.1 := by
          simpa [decorate] using
            roundTransition_map_realizedEventBatch_eq_explicitRoundBatchDist
              G iface state.state action.1

/-- Primitive event batches extracted from a bounded graph-FOSG step list.

Each bounded FOSG step is one frontier round.  Internal chance patches are read
from the realized destination, so the batch is concrete. -/
noncomputable def boundedFOSGStepEventBatches
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
    (steps :
      List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)) :
    List (List (G.toMachine iface).Event) :=
  steps.map fun step =>
    realizedEventBatch G iface step.src.state step.act.1 step.dst.state

/-- Primitive event batches extracted from a bounded graph-FOSG history. -/
noncomputable def boundedFOSGHistoryEventBatches
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    List (List (G.toMachine iface).Event) :=
  boundedFOSGStepEventBatches G iface hsound horizon h.steps

/-- Every realized bounded graph-FOSG step chain is backed by primitive
event-batch executions whose events are available at the states where they run. -/
theorem boundedFOSGStepEventBatches_lastState_availableRunBatchesFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps :
        List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)},
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).StepChainFrom
          start steps →
        (G.toMachine iface).AvailableRunBatchesFrom start.state
            (boundedFOSGStepEventBatches G iface hsound horizon steps)
            (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
              start steps).state
  | start, [], _hchain => by
      simp [boundedFOSGStepEventBatches, GameTheory.FOSG.lastStateFrom,
        Machine.AvailableRunBatchesFrom.nil]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      cases hsrc
      let batch : List (G.toMachine iface).Event :=
        realizedEventBatch G iface step.src.state step.act.1
          step.dst.state
      have hstateSupport :
          step.dst.state ∈
            (roundTransition G step.src.state step.act.1).support := by
        have hmap :
            step.dst.state ∈
              (PMF.map (fun bounded => bounded.state)
                (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
                  step.src step.act)).support := by
          exact (PMF.mem_support_map_iff _ _ _).2
            ⟨step.dst, (PMF.mem_support_iff _ _).2 step.support, rfl⟩
        rw [Machine.FOSGView.toBoundedFOSG_transition_map_state] at hmap
        change step.dst.state ∈
          (roundTransition G step.src.state step.act.1).support at hmap
        exact hmap
      have hexplicit :
          (batch, step.dst.state) ∈
            (explicitRoundBatchDist G iface step.src.state
              step.act.1).support := by
        simpa [batch] using
          (realizedEventBatch_mem_explicitRoundBatchDist_support
            G iface hstateSupport)
      have hlegal :
          JointActionLegal (PlayerRoundAction G) (roundActive G)
            Configuration.terminal (roundAvailable G)
            step.src.state step.act.1 := by
        simpa [toFOSGView] using
          ((G.toFOSGView iface hsound).boundedActionToAction
            horizon step.src step.act).2
      have hbatch :
          (G.toMachine iface).AvailableRunFrom
            step.src.state batch step.dst.state := by
        simpa [batch] using
          (explicitRoundBatchDist_support_availableRunFrom
            G iface hsound hlegal hexplicit)
      have htailSupport :
          (G.toMachine iface).AvailableRunBatchesFrom
              step.dst.state
              (boundedFOSGStepEventBatches G iface hsound horizon steps)
              (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
                step.dst steps).state :=
        boundedFOSGStepEventBatches_lastState_availableRunBatchesFrom
          G iface hsound horizon htail
      simpa [boundedFOSGStepEventBatches, batch] using
        Machine.AvailableRunBatchesFrom.cons hbatch htailSupport

/-- Every realized bounded graph-FOSG step chain is backed by a primitive
machine event-batch run whose support contains the same checkpoint endpoint. -/
theorem boundedFOSGStepEventBatches_lastState_mem_runEventBatchesFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps :
        List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)},
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).StepChainFrom
          start steps →
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
            start steps).state ∈
          ((G.toMachine iface).runEventBatchesFrom
            (boundedFOSGStepEventBatches G iface hsound horizon steps)
            start.state).support := by
  intro start steps hchain
  exact
    (boundedFOSGStepEventBatches_lastState_availableRunBatchesFrom
      G iface hsound horizon hchain).mem_runEventBatchesFrom_support

/-- Every realized bounded graph-FOSG history extracts primitive event batches
whose events are available along the checkpoint execution from the machine
initial state to the history's checkpoint state. -/
theorem boundedFOSGHistory_state_availableRunBatchesFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    (G.toMachine iface).AvailableRunBatchesFrom
      (G.toMachine iface).init
      (boundedFOSGHistoryEventBatches G iface hsound horizon h)
      h.lastState.state := by
  simpa [boundedFOSGHistoryEventBatches,
    boundedFOSGStepEventBatches, GameTheory.FOSG.History.lastState,
    EventGraph.toMachine_init] using
    (boundedFOSGStepEventBatches_lastState_availableRunBatchesFrom
      G iface hsound horizon h.chain)

/-- Every realized bounded graph-FOSG history extracts a primitive machine
event-batch trace whose endpoint support contains the history's checkpoint
state. -/
theorem boundedFOSGHistory_state_mem_runEventBatchesFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((G.toMachine iface).runEventBatchesFrom
        (boundedFOSGHistoryEventBatches G iface hsound horizon h)
        (G.toMachine iface).init).support := by
  exact
    (boundedFOSGHistory_state_availableRunBatchesFrom
      G iface hsound horizon h).mem_runEventBatchesFrom_support

/-- History-dependent event-batched primitive trace distribution induced by a
bounded graph-FOSG behavioral profile.

The state of this process is still the FOSG history: strategies are allowed to
depend on information-state history.  The machine contribution at each
nonterminal FOSG round is the primitive event batch selected by that round. -/
noncomputable def boundedFOSGEventBatchTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
    (hsound : G.HasIndependentFrontierRounds) (horizon : Nat)
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
