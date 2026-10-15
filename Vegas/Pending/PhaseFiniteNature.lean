/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ReactiveRuntime

/-! # Finite nature in the actual physical phase application -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Normalization is deterministic; the physical application's only nature
laws are the original finite leak and finite native environment laws. -/
instance phaseApplication_finiteEnvironment [leaks.FiniteSupport] :
    (phaseApplication runtime leaks).FiniteEnvironment where
  observePending_finite :=
    MessageNetwork.ObservationRule.FiniteSupport.support_finite (leaks := leaks)
  environment_finite state command := by
    change (state.environment runtime command).support.Finite
    unfold PhaseRuntimeState.environment
    split
    · rw [PMF.support_map]
      exact (runtime.environmentStep_support_finite _ _).image _
    · simp only [PMF.support_pure]
      exact Set.finite_singleton _

/-- The original finite initial prior and finite scheduler branches supply
physical finite nature. Opportunity, inclusion and timing impose no such
finiteness condition by themselves. -/
theorem phaseApplication_finiteNature [leaks.FiniteSupport]
    (initial : PMF (phaseApplication runtime leaks).State)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (initialFinite : initial.support.Finite)
    (schedulerFinite : ∀ past view, (scheduler past view).support.Finite) :
    (phaseApplication runtime leaks).FiniteNature initial scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := initialFinite
  scheduler_finite := schedulerFinite

end Vegas.EventGraphRuntime
