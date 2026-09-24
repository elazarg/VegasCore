/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteCompiler
import Interaction.ReactiveConsistentAssessment

/-! # Consistent beliefs for the finite reactive compiler

Static output-value coverage and horizon-sized handle capacity place the actual
compiler, including recovery, in the complete finite response menu. Its profile
then admits a consistent belief completion. The beliefs are not asserted to
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
    (values : bounds.CoversOutputValues) (capacity : horizon ≤ bounds.candidateCount)
    (profile : graph.BehavioralProfile) :
    ∃ assessment : ((bounds.menu runtime leaks).information (inputs.map State.initial)
        horizon scheduler).BehavioralAssessment,
      assessment.strategy = (fun who => bounds.compileFinitePolicy runtime leaks inputs
        horizon scheduler values capacity who (profile who)) ∧
      assessment.IsSequentiallyConsistent
        ((bounds.menu runtime leaks).decisionInformationAntichain
          (inputs.map State.initial) horizon scheduler) :=
  (bounds.menu runtime leaks).exists_consistent_assessment (inputs.map State.initial)
    horizon scheduler _

end Vegas.EventGraphRuntime.MessageBounds
