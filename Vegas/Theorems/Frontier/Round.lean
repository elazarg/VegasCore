import Vegas.EventGraph.RoundView

/-!
# Event-Graph Frontier Rounds

Facts about the generic frontier-round presentation of an `EventGraph`.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Forgetting realized primitive events from the explicit batch distribution
recovers the graph frontier-round transition. -/
theorem eventGraph_explicitRoundBatchDist_map_state_eq_roundTransition
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (EventGraph.PlayerRoundAction G)) :
    PMF.map Prod.snd
        (EventGraph.explicitRoundBatchDist G iface cfg joint) =
      EventGraph.roundTransition G cfg joint :=
  EventGraph.explicitRoundBatchDist_map_state_eq_roundTransition
    G iface cfg joint

/-- Decorating native round destinations with their realized primitive event
batches recovers the explicit batch distribution. -/
theorem eventGraph_roundTransition_map_realizedEventBatch_eq_explicitRoundBatchDist
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (EventGraph.PlayerRoundAction G)) :
    PMF.map
        (fun dst =>
          (EventGraph.realizedEventBatch G iface cfg joint dst, dst))
        (EventGraph.roundTransition G cfg joint) =
      EventGraph.explicitRoundBatchDist G iface cfg joint :=
  EventGraph.roundTransition_map_realizedEventBatch_eq_explicitRoundBatchDist
    G iface cfg joint

/-- A prefix of distinct frontier executions does not change the internal
kernel of a source-frontier node that the prefix does not execute. -/
theorem eventGraph_roundTransitionGo_preserves_internalKernel_of_not_mem
    {G : EventGraph P L}
    (hsound : G.HasLocalFrontierRounds)
    (joint : JointAction (EventGraph.PlayerRoundAction G))
    (nodes : List G.Node)
    {candidate : G.Node}
    {current dst : G.Configuration}
    (hcandidate : candidate ∈ current.frontier)
    (hnotmem : candidate ∉ nodes)
    (hsupp : dst ∈
      (EventGraph.roundTransitionGo G joint nodes current).support) :
    G.internalKernel candidate dst.result =
      G.internalKernel candidate current.result :=
  EventGraph.roundTransitionGo_preserves_internalKernel_of_not_mem
    G hsound joint nodes hcandidate hnotmem hsupp

/-- Any explicit source-frontier schedule induces the same state kernel as the
canonical frontier-round representative. -/
theorem eventGraph_roundTransitionWithSchedule_eq_roundTransition
    {G : EventGraph P L}
    (hsound : G.HasLocalFrontierRounds)
    {cfg : G.Configuration}
    {joint : JointAction (EventGraph.PlayerRoundAction G)}
    (hlegal :
      JointActionLegal (EventGraph.PlayerRoundAction G)
        (EventGraph.roundActive G)
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable G) cfg joint)
    (schedule : EventGraph.FrontierSchedule G cfg) :
    EventGraph.roundTransitionWithSchedule G cfg joint schedule =
      EventGraph.roundTransition G cfg joint :=
  EventGraph.roundTransitionWithSchedule_eq_roundTransition
    G hsound hlegal schedule

/-- Local, legal explicit frontier batches are primitive runs whose
events are available at the states where they execute. -/
theorem eventGraph_explicitRoundBatchDist_support_availableRunFrom
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (hsound : G.HasLocalFrontierRounds)
    {cfg dst : G.Configuration}
    {joint : JointAction (EventGraph.PlayerRoundAction G)}
    {batch : List (G.toMachine iface).Event}
    (hlegal :
      JointActionLegal (EventGraph.PlayerRoundAction G)
        (EventGraph.roundActive G)
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable G) cfg joint)
    (hsupp : (batch, dst) ∈
      (EventGraph.explicitRoundBatchDist G iface cfg joint).support) :
    (G.toMachine iface).AvailableRunFrom cfg batch dst :=
  EventGraph.explicitRoundBatchDist_support_availableRunFrom
    G iface hsound hlegal hsupp

end Vegas
