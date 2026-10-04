/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedPolicy
import Vegas.Pending.ReactiveCleanPrefixProbability

/-! # Actual prescribed probabilities before persistent service risk

For every prescribed turn timing, a clean prefix in the risk-menu game has
the same probability as that exact prefix under the physical prescribed
policy. Canonical admission is derived from actual legal retained histories.
The clean event keeps its original probability mass; there is no posterior
or full-support premise. Behavior after menu expansion is not identified.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every event of clean complete realized prefixes has its actual physical
prescribed probability in the finite risk-menu game. Arbitrary timing includes
earlier silent deferrals. Equality is not conditioned or normalized. -/
theorem sourceServiceTurnPolicy_cleanPrefix_event_probability
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program (CommitmentInterface.values _))
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) (fuel : Nat)
    (event : Set ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History)
    (clear : ∀ history ∈ event,
      (runtime setup).AllPersistentServiceRiskClear leaks bound history.state) :
    let risk := bounds.riskMenu (runtime setup) leaks bound
    let players := sourceServiceTurnPolicy setup leaks bound turns timing profile
    (((risk.information (initialLaw setup) horizon scheduler).runBehavioral
      (fun who => risk.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
        fuel).map (risk.toRawHistory (initialLaw setup) horizon scheduler)).toOuterMeasure event =
    (((application setup leaks).information (initialLaw setup) horizon scheduler).runBehavioral
      (fun who => (application setup leaks).encodePolicy (players who)) fuel).toOuterMeasure
        event := by
  intro risk players
  let canonical := bounds.canonicalMenu (runtime setup) leaks
  have admitted : ∀ who, canonical.Admissible (initialLaw setup) horizon scheduler who
      (players who) := by
    intro who control trace _ response chosen
    exact sourceServiceTurnPolicy_retained bounds covered initialCovered capacity bound turns
      timing profile who (permitted who) control trace response chosen
  have physical :
      (((canonical.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => canonical.restrictPolicy (initialLaw setup) horizon scheduler who
          (players who)) fuel).map
        (canonical.toRawHistory (initialLaw setup) horizon scheduler)) =
      ((application setup leaks).information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => (application setup leaks).encodePolicy (players who)) fuel :=
    canonical.run_restrict (initialLaw setup) horizon scheduler players admitted fuel
      (canonical.protocol (initialLaw setup) horizon scheduler).initHistory
  have menus := bounds.cleanPrefix_event_probability (runtime setup) leaks bound (initialLaw setup)
    horizon scheduler players fuel event clear
  exact menus.symm.trans (congrArg (fun law => law.toOuterMeasure event) physical)

/-- The individual history probability retains every private response,
network observation, application result and realized scheduler command. -/
theorem sourceServiceTurnPolicy_cleanPrefix_probability
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program (CommitmentInterface.values _))
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) (fuel : Nat)
    (history : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History)
    (clear : (runtime setup).AllPersistentServiceRiskClear leaks bound history.state) :
    let risk := bounds.riskMenu (runtime setup) leaks bound
    let players := sourceServiceTurnPolicy setup leaks bound turns timing profile
    (((risk.information (initialLaw setup) horizon scheduler).runBehavioral
      (fun who => risk.restrictPolicy (initialLaw setup) horizon scheduler who (players who))
        fuel).map (risk.toRawHistory (initialLaw setup) horizon scheduler)) history =
    (((application setup leaks).information (initialLaw setup) horizon scheduler).runBehavioral
      (fun who => (application setup leaks).encodePolicy (players who)) fuel) history := by
  intro risk players
  have event := sourceServiceTurnPolicy_cleanPrefix_event_probability bounds covered initialCovered
    capacity bound turns timing profile permitted horizon scheduler fuel {history}
    (fun final member => Set.mem_singleton_iff.mp member ▸ clear)
  simpa only [PMF.toOuterMeasure_apply_singleton] using event

end Vegas
