/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPrefix

/-! # Finite native nature from finite recovery nature

The two applications use the same pending-observation law. Native graph
sampling already has finite support independently of automatic service. The
initial prior and scheduler are direct images, so no drain-image inversion is
needed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (RecoveryState graph))
  (scheduler : (runtime.recoveryApplication leaks).Scheduler)

/-- The native comparison scheduler is finitely branching whenever the actual
recovery nature is. Native chance support is proved before automatic service. -/
instance nativeSchedulerFiniteNature
    [(runtime.recoveryApplication leaks).FiniteNature initial scheduler] :
    (runtime.reactiveApplication leaks).FiniteNature (initial.map RecoveryState.native)
      (nativeScheduler runtime leaks scheduler) where
  observePending_finite who pending :=
    ReactiveApplication.FiniteEnvironment.observePending_finite
      (app := runtime.recoveryApplication leaks) who pending
  environment_finite := runtime.environmentStep_support_finite
  initial_finite := by
    rw [PMF.support_map]
    exact (ReactiveApplication.FiniteNature.initial_finite
      (app := runtime.recoveryApplication leaks) scheduler).image _
  scheduler_finite past view := by
    rw [nativeScheduler, PMF.support_map]
    exact (ReactiveApplication.FiniteNature.scheduler_finite
      (app := runtime.recoveryApplication leaks) initial _ _).image _

end Vegas.EventGraphRuntime.RecoveryProjection
