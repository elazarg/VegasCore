import Vegas.EventGraph.Round
import Vegas.Machine.RoundView

/-!
# Native round views for event graphs

This module packages event-graph frontiers as native machine
`RoundView`s. The FOSG bridge reuses the same frontier-round definitions but
is not needed here.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Native round-view presentation of a protocol-graph machine by local explicit
frontier rounds. -/
noncomputable def toRoundView
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds) :
    (G.toMachine iface).RoundView where
  Act := PlayerRoundAction G
  active := roundActive G
  availableActions := roundAvailable G
  transition := fun cfg action => frontierRealizationTransition G cfg action
  eventBatch := fun cfg joint dst => realizedEventBatch G iface cfg joint dst
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

/-- The primitive batch extracted from one supported native bounded round step
is an available machine run from the step source to the step destination. -/
theorem boundedRoundStepEventBatch_availableRunFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds) (horizon : Nat)
    (step : ((G.toRoundView iface hsound).BoundedStep horizon)) :
    (G.toMachine iface).AvailableRunFrom step.src.state
      ((G.toRoundView iface hsound).eventBatch step.src.state step.act.1
        step.dst.state)
      step.dst.state := by
  classical
  let view := G.toRoundView iface hsound
  let joint := view.boundedActionToAction horizon step.src step.act
  have hmemBounded :
      step.dst ∈ (view.boundedTransition horizon step.src step.act).support :=
    (PMF.mem_support_iff _ _).2 step.support
  have hmemState :
      step.dst.state ∈
        (PMF.map (fun bounded => bounded.state)
          (view.boundedTransition horizon step.src step.act)).support :=
    (PMF.mem_support_map_iff _ _ _).2
      ⟨step.dst, hmemBounded, rfl⟩
  have hmap := view.boundedTransition_map_state horizon step.src step.act
  rw [hmap] at hmemState
  have hdst :
      step.dst.state ∈
        (frontierRealizationTransition G step.src.state joint).support := by
    simpa [view, joint, toRoundView] using hmemState
  simpa [view, joint, toRoundView, Machine.RoundView.boundedActionToAction]
    using
      (realizedEventBatch_availableRunFrom_of_frontierRealizationTransition_support
        G iface hsound joint hdst)

private theorem boundedRoundStepBatches_availableRunBatchesFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps : List ((G.toRoundView iface hsound).BoundedStep horizon)},
      (G.toRoundView iface hsound).StepChainFrom horizon start steps →
        (G.toMachine iface).AvailableRunBatchesFrom start.state
          (steps.map fun step =>
            (G.toRoundView iface hsound).eventBatch step.src.state step.act.1
              step.dst.state)
          (((G.toRoundView iface hsound).lastStateFrom horizon start steps).state)
  | start, [], _hchain => by
      simpa [Machine.RoundView.lastStateFrom] using
        Machine.AvailableRunBatchesFrom.nil start.state
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst start
      change (G.toMachine iface).AvailableRunBatchesFrom step.src.state
        ((G.toRoundView iface hsound).eventBatch step.src.state step.act.1
          step.dst.state ::
            steps.map fun step =>
              (G.toRoundView iface hsound).eventBatch step.src.state
                step.act.1 step.dst.state)
        (((G.toRoundView iface hsound).lastStateFrom horizon step.dst steps).state)
      exact Machine.AvailableRunBatchesFrom.cons
        (boundedRoundStepEventBatch_availableRunFrom
          G iface hsound horizon step)
        (boundedRoundStepBatches_availableRunBatchesFrom
          G iface hsound horizon htail)

/-- Primitive batches extracted from a native bounded event-graph history form
an available machine batch run from the machine initial state to the history
state. -/
theorem boundedRoundHistory_availableRunBatchesFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds) (horizon : Nat)
    (h : ((G.toRoundView iface hsound).BoundedHistory horizon)) :
    (G.toMachine iface).AvailableRunBatchesFrom (G.toMachine iface).init
      ((G.toRoundView iface hsound).boundedHistoryEventBatches horizon h)
      h.lastState.state := by
  simpa [Machine.RoundView.boundedHistoryEventBatches,
    Machine.RoundView.BoundedHistory.lastState] using
    (boundedRoundStepBatches_availableRunBatchesFrom
      G iface hsound horizon h.chain)

/-- Nonzero-support form of `boundedRoundHistory_availableRunBatchesFrom`. -/
theorem boundedRoundHistory_state_mem_runEventBatchesFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasLocalFrontierRounds) (horizon : Nat)
    (h : ((G.toRoundView iface hsound).BoundedHistory horizon)) :
    h.lastState.state ∈
      ((G.toMachine iface).runEventBatchesFrom
        ((G.toRoundView iface hsound).boundedHistoryEventBatches horizon h)
        (G.toMachine iface).init).support :=
  Machine.AvailableRunBatchesFrom.mem_runEventBatchesFrom_support
    (boundedRoundHistory_availableRunBatchesFrom G iface hsound horizon h)

end EventGraph

end Vegas
