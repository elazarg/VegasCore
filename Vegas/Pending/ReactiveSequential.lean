/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSequential
import Vegas.Pending.ReactiveRuntime

/-! # The raw response carrier cannot support finite-support full mixing

Arbitrarily large private natural numbers already suffice for the obstruction.
It applies at any legal decision site, including sites off the prescribed path.
It does not assert nonexistence for a finite runtime instance or a different
probability interface.
-/

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

instance : Infinite (ResponseMemory graph) := by
  apply Infinite.of_injective (fun value : Nat =>
    (⟨none, [.inl value]⟩ : ResponseMemory graph))
  intro first second same
  have data := congrArg ResponseMemory.privateData same
  simpa using data

theorem reactive_not_fullyMixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (assessment : ((runtime.reactiveApplication leaks).information initial horizon
      scheduler).BehavioralAssessment)
    (who : Player)
    (site : ((runtime.reactiveApplication leaks).information initial horizon
      scheduler).InformationSite who) : ¬ assessment.IsFullyMixed := by
  let : Infinite (runtime.reactiveApplication leaks).Memory :=
    inferInstanceAs (Infinite (ResponseMemory graph))
  exact (runtime.reactiveApplication leaks).not_fullyMixed_of_infinite_memory
    initial horizon scheduler assessment who site

end Vegas.EventGraphRuntime
