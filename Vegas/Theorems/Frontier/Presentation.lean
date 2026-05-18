import Vegas.EventGraph.RoundView

/-!
# Event-Graph Frontier Presentation

Facts about the generic frontier-step presentation of an `EventGraph`.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Forgetting realized primitive events from the explicit batch distribution
recovers the scheduled frontier transition. -/
theorem eventGraph_explicitFrontierBatchDist_map_state_eq_scheduledFrontierTransition
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (EventGraph.PlayerFrontierAction G)) :
    PMF.map Prod.snd
        (EventGraph.explicitFrontierBatchDist G iface cfg joint) =
      EventGraph.scheduledFrontierTransition G cfg joint :=
  EventGraph.explicitFrontierBatchDist_map_state_eq_scheduledFrontierTransition
    G iface cfg joint

/-- Decorating scheduled frontier destinations with their realized primitive event
batches recovers the explicit batch distribution. -/
theorem eventGraph_scheduledFrontierTransition_map_realizedEventBatch_eq_explicitFrontierBatchDist
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (EventGraph.PlayerFrontierAction G)) :
    PMF.map
        (fun dst =>
          (EventGraph.realizedEventBatch G iface cfg joint dst, dst))
        (EventGraph.scheduledFrontierTransition G cfg joint) =
      EventGraph.explicitFrontierBatchDist G iface cfg joint :=
  EventGraph.scheduledFrontierTransition_map_realizedEventBatch_eq_explicitFrontierBatchDist
    G iface cfg joint

/-- A prefix of distinct frontier executions does not change the internal
kernel of a source-frontier node that the prefix does not execute. -/
theorem eventGraph_scheduledFrontierTransitionGo_preserves_internalKernel_of_not_mem
    {G : EventGraph P L}
    (hsound : G.HasLocalFrontierSteps)
    (joint : JointAction (EventGraph.PlayerFrontierAction G))
    (nodes : List G.Node)
    {candidate : G.Node}
    {current dst : G.Configuration}
    (hcandidate : candidate ∈ current.frontier)
    (hnotmem : candidate ∉ nodes)
    (hsupp : dst ∈
      (EventGraph.scheduledFrontierTransitionGo G joint nodes current).support) :
    G.internalKernel candidate dst.result =
      G.internalKernel candidate current.result :=
  EventGraph.scheduledFrontierTransitionGo_preserves_internalKernel_of_not_mem
    G hsound joint nodes hcandidate hnotmem hsupp

/-- Any explicit source-frontier schedule induces the same state kernel as the
canonical scheduled frontier representative. -/
theorem eventGraph_frontierTransitionWithSchedule_eq_scheduledFrontierTransition
    {G : EventGraph P L}
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    {joint : JointAction (EventGraph.PlayerFrontierAction G)}
    (hlegal :
      JointActionLegal (EventGraph.PlayerFrontierAction G)
        (EventGraph.frontierActive G)
        EventGraph.Configuration.terminal
        (EventGraph.frontierAvailable G) cfg joint)
    (schedule : EventGraph.FrontierSchedule G cfg) :
    EventGraph.frontierTransitionWithSchedule G cfg joint schedule =
      EventGraph.scheduledFrontierTransition G cfg joint :=
  EventGraph.frontierTransitionWithSchedule_eq_scheduledFrontierTransition
    G hsound hlegal schedule

/-- Every sampled order-free frontier realization carries legal patches. -/
theorem eventGraph_frontierRealizationDist_support_legal
    {G : EventGraph P L}
    (cfg : G.Configuration)
    (joint : JointAction (EventGraph.PlayerFrontierAction G))
    (hlegal :
      JointActionLegal (EventGraph.PlayerFrontierAction G)
        (EventGraph.frontierActive G)
        EventGraph.Configuration.terminal
        (EventGraph.frontierAvailable G) cfg joint)
    {realization : EventGraph.FrontierRealization G cfg}
    (hsupp : realization ∈
      (EventGraph.frontierRealizationDist G cfg joint hlegal).support) :
    realization.Legal :=
  EventGraph.frontierRealizationDist_support_legal
    G cfg joint hlegal hsupp

/-- Supported order-free frontier destinations are exactly whole-frontier
extensions of supported legal realizations. -/
theorem eventGraph_frontierRealizationTransition_support_extend
    {G : EventGraph P L}
    (cfg : G.Configuration)
    (joint :
      { joint : JointAction (EventGraph.PlayerFrontierAction G) //
        JointActionLegal (EventGraph.PlayerFrontierAction G)
          (EventGraph.frontierActive G)
          EventGraph.Configuration.terminal
          (EventGraph.frontierAvailable G) cfg joint })
    {dst : G.Configuration}
    (hdst : dst ∈
      (EventGraph.frontierRealizationTransition G cfg joint).support) :
    ∃ realization,
      realization ∈
        (EventGraph.frontierRealizationDist G cfg joint.1 joint.2).support ∧
        ∃ hlegal : realization.Legal,
          dst = cfg.extendFrontier realization hlegal :=
  EventGraph.frontierRealizationTransition_support_extend
    G cfg joint hdst

/-- Order-free frontier-realization transitions are supported by the canonical
scheduled frontier representative. This reconnects native round histories to
primitive machine execution theorems. -/
theorem eventGraph_frontierRealizationTransition_support_scheduledFrontierTransition
    {G : EventGraph P L}
    (hsound : G.HasLocalFrontierSteps)
    {cfg : G.Configuration}
    (joint :
      { joint : JointAction (EventGraph.PlayerFrontierAction G) //
        JointActionLegal (EventGraph.PlayerFrontierAction G)
          (EventGraph.frontierActive G)
          EventGraph.Configuration.terminal
          (EventGraph.frontierAvailable G) cfg joint })
    {dst : G.Configuration}
    (hdst : dst ∈
      (EventGraph.frontierRealizationTransition G cfg joint).support) :
    dst ∈ (EventGraph.scheduledFrontierTransition G cfg joint.1).support :=
  EventGraph.frontierRealizationTransition_support_scheduledFrontierTransition
    G hsound joint hdst

/-- Local, legal explicit frontier batches are primitive runs whose
events are available at the states where they execute. -/
theorem eventGraph_explicitFrontierBatchDist_support_availableRunFrom
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg dst : G.Configuration}
    {joint : JointAction (EventGraph.PlayerFrontierAction G)}
    {batch : List (G.toMachine iface).Event}
    (hlegal :
      JointActionLegal (EventGraph.PlayerFrontierAction G)
        (EventGraph.frontierActive G)
        EventGraph.Configuration.terminal
        (EventGraph.frontierAvailable G) cfg joint)
    (hsupp : (batch, dst) ∈
      (EventGraph.explicitFrontierBatchDist G iface cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg batch dst :=
  EventGraph.explicitFrontierBatchDist_support_availableRunFrom
    G iface hsound hlegal hsupp

/-- Realized batches extracted from native order-free frontier destinations are
available primitive runs to that destination. -/
theorem eventGraph_realizedEventBatch_availableRunFrom_of_frontier
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    {cfg dst : G.Configuration}
    (joint :
      { joint : JointAction (EventGraph.PlayerFrontierAction G) //
        JointActionLegal (EventGraph.PlayerFrontierAction G)
          (EventGraph.frontierActive G)
          EventGraph.Configuration.terminal
          (EventGraph.frontierAvailable G) cfg joint })
    (hdst : dst ∈
      (EventGraph.frontierRealizationTransition G cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg
      (EventGraph.realizedEventBatch G iface cfg joint.1 dst) dst :=
  EventGraph.realizedEventBatch_availableRunFrom_of_frontierRealizationTransition_support
    G iface hsound joint hdst

/-- Native bounded event-graph histories extract primitive batches that execute
from the machine initial state to the history endpoint. -/
theorem eventGraph_boundedRoundHistory_availableRunBatchesFrom
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (hsound : G.HasLocalFrontierSteps)
    (horizon : Nat)
    (h :
      ((G.toRoundView iface hsound).BoundedHistory horizon)) :
    (G.toMachine iface).AvailableRunBatchesFrom (G.toMachine iface).init
      ((G.toRoundView iface hsound).boundedHistoryEventBatches horizon h)
      h.lastState.state :=
  EventGraph.boundedRoundHistory_availableRunBatchesFrom
    G iface hsound horizon h

end Vegas
