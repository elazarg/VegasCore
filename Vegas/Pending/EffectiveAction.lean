module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.EventGraph.SchedulerErasure

@[expose] public section

/-! # Realizability of a graph action by a ledger decision -/

namespace Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A requested opening is realizable precisely when the immutable binding
contains a value. Deferred guard rejection does not prevent the attempt. -/
def EffectiveAction (config : graph.Config)
    (event : graph.EventId)
    (action : graph.Action event) : Prop :=
  match nodeView graph event with
  | .resolve _ _ binding _ outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true →
        ∃ value, binding.get? config.store = some (.success value)
  | _ => True

/-- Every action drawn at a reachable, ready event can be realized by a native client. -/
def RealizableProfile (inputs : PMF graph.Inputs) (reference : graph.BehavioralProfile) : Prop :=
  ∀ initial ∈ inputs.support, ∀ config : graph.Config, config.Reachable initial →
    ∀ event, config.cut.Ready event →
      ∀ action ∈ (EventGraph.actionLaw reference config event).support,
      EffectiveAction config event action

end Vegas.EventGraphRuntime
