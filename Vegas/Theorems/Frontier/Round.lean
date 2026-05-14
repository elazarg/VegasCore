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

/-- A graph frontier round is the primitive machine run of the corresponding
frontier event list. -/
theorem eventGraph_roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    {G : EventGraph P L}
    (iface : EventGraph.MachineInterface G)
    (cfg : G.Configuration)
    (joint : JointAction (EventGraph.PlayerRoundAction G)) :
    EventGraph.roundTransition G cfg joint =
      (G.toMachine iface).runEventsFrom
        (EventGraph.roundPrimitiveEvents G iface cfg joint) cfg :=
  EventGraph.roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    G iface cfg joint

end Vegas
