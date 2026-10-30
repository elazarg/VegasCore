/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRuntime

/-! # Finite nature of the native application

The graph environment and automatic drain already have finite-support laws.
Thus finite native nature requires exactly finite-support pending observations,
initial draws and scheduler decisions. No finiteness of payloads, states or
observation carriers is required.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The native environment contributes no additional finiteness premise beyond
those on actual pending observations, initialization and scheduling laws. -/
theorem reactiveApplication_finiteNature_iff
    (initial : PMF (runtime.reactiveApplication leaks).State)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).FiniteNature initial scheduler ↔
      leaks.FiniteSupport ∧ initial.support.Finite ∧
        ∀ past view, (scheduler past view).support.Finite := by
  constructor
  · intro nature
    exact ⟨⟨nature.toFiniteEnvironment.observePending_finite⟩,
      nature.initial_finite, nature.scheduler_finite⟩
  · rintro ⟨observations, initialFinite, schedulerFinite⟩
    let := observations
    exact
      { toFiniteEnvironment := inferInstance
        initial_finite := initialFinite
        scheduler_finite := schedulerFinite }

end Vegas.EventGraphRuntime
