/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteCompiler
import Interaction.ReactiveConsistentAssessment

/-! # Consistent beliefs for the finite reactive compiler

The total finite representation of the reactive compiler admits a consistent
belief completion. Domain and capacity bounds separately ensure that restriction
preserves the original physical policy on legal histories. The beliefs are not asserted to
transport a source assessment or make compiled continuations optimal.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph)

/-- For every source profile, the actual finite compiled profile has some
sequentially consistent native beliefs. No source equilibrium premise is used. -/
theorem compileFinitePolicy_exists_consistent_assessment
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (profile : graph.BehavioralProfile) :
    ∃ assessment : ((bounds.rawMenu runtime leaks).information (inputs.map State.initial)
        horizon scheduler).BehavioralAssessment,
      assessment.strategy = (fun who => bounds.compileFinitePolicy runtime leaks inputs
        horizon scheduler who (profile who)) ∧
      assessment.IsSequentiallyConsistent
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain
          (inputs.map State.initial) horizon scheduler) :=
  (bounds.rawMenu runtime leaks).exists_consistent_assessment (inputs.map State.initial)
    horizon scheduler _

end Vegas.EventGraphRuntime.MessageBounds
