module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.TurnClient
public import Vegas.EventGraph.SchedulerErasure

@[expose] public section

/-! # The canonical ledger callback realizes the graph action distribution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- At an owner's actual turn the ledger callback implements the graph action law,
including forced failure after a default. -/
theorem referencePolicy_actionDistribution (reference : graph.BehavioralProfile) (owner : Player)
    (current : (app).Execution) (event : graph.EventId)
    (selected : current.application.publicView.ownTurn? owner = some event)
    (owned : graph.actor? event = some owner) :
    referencePolicy timeouts leaks reference owner (current.logs owner)
        (current.observe (app) owner) =
      (EventGraph.actionDistribution reference current.application.config event).map
        (canonicalServiceDecision timeouts leaks owner (current.logs owner)
          (current.observe (app) owner) event) := by
  rw [EventGraph.actionDistribution_of_actor reference current.application.config owned]
  unfold referencePolicy
  rw [dite_eq_left (show (current.observe (app) owner).application.who = owner from rfl)]
  have turn : (current.observe (app) owner).application.publicView.ownTurn? owner = some event :=
    selected
  rw [turn]
  simp only [dite_eq_left owned]
  by_cases inactive : owner ∈ current.application.config.defaulted
  · rw [dite_eq_left inactive, PMF.pure_map, canonicalServiceDecision_defaulted timeouts leaks owner
      (current.logs owner) (current.observe (app) owner) event _ inactive]
    exact dite_eq_left inactive
  · have observed : owner ∉ (current.observe (app) owner).application.observation.defaulted :=
      inactive
    simp only [dite_eq_right inactive, dite_eq_right observed]
    rfl

end Vegas.EventGraphRuntime
