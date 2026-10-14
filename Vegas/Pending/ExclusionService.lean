/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionLiftTrace
import Vegas.Pending.ReactiveServiceConditions

/-! # Timing and completion by the actual recovery service

Opportunity, protected inclusion, and completion quantify over actual recovery
histories, including histories after exclusion. Their transport to native execution
is restricted to public-clear histories; no global native contract is imposed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Actual recovery histories satisfy the native timing opportunity condition
on their projected full environment recall. -/
def Opportunity (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (delay : graph.EventId → Nat) : Prop :=
  ∀ control, ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    OpportunityAt runtime leaks (RecoveryProjection.execution runtime leaks control.execution) delay

/-- Protected inclusion is required on actual recovery histories. Projection only
selects the native public fields and retained packets used by the timing premise. -/
def ProtectedInclusion (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (bound : graph.EventId → Nat) : Prop :=
  ∀ control, ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    ProtectedInclusionAt runtime leaks
      (RecoveryProjection.execution runtime leaks control.execution) bound

/-- Every actual terminal recovery execution has completed the native graph. -/
def CompletesPlay (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler) : Prop :=
  ∀ control, ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    (runtime.recoveryApplication leaks).terminal (some control) →
    control.execution.application.native.config.cut.Terminal

/-- The recovery service contract refers throughout to actual wrapper histories. -/
structure AsyncContract (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (delay bound : graph.EventId → Nat) : Prop where
  opportunity : Opportunity runtime leaks initial horizon scheduler delay
  inclusion : ProtectedInclusion runtime leaks initial horizon scheduler bound
  completes : CompletesPlay runtime leaks initial horizon scheduler

/-- Recovery opportunity holds at every genuine public-clear native history. -/
theorem Opportunity.clear_native
    {initial : PMF (RecoveryState graph)}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay : graph.EventId → Nat}
    (opportunity : Opportunity runtime leaks initial horizon scheduler delay)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (clear : PublicExclusionRecord (⟨control.execution.application, ∅⟩ : RecoveryState graph)) :
    OpportunityAt runtime leaks control.execution delay := by
  have lifted := RecoveryProjection.recoveryTrace runtime leaks initial initialized horizon
    scheduler trace (by intro current same; cases Option.some.inj same; exact clear)
  have actual := opportunity (RecoveryProjection.liftControl runtime leaks control) lifted
  change OpportunityAt runtime leaks (RecoveryProjection.execution runtime leaks
    (RecoveryProjection.liftExecution runtime leaks control.execution)) delay at actual
  simpa only [RecoveryProjection.execution_liftExecution] using actual

/-- Recovery inclusion holds at every genuine public-clear native history. -/
theorem ProtectedInclusion.clear_native
    {initial : PMF (RecoveryState graph)}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {bound : graph.EventId → Nat}
    (inclusion : ProtectedInclusion runtime leaks initial horizon scheduler bound)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (clear : PublicExclusionRecord (⟨control.execution.application, ∅⟩ : RecoveryState graph)) :
    ProtectedInclusionAt runtime leaks control.execution bound := by
  have lifted := RecoveryProjection.recoveryTrace runtime leaks initial initialized horizon
    scheduler trace (by intro current same; cases Option.some.inj same; exact clear)
  have actual := inclusion (RecoveryProjection.liftControl runtime leaks control) lifted
  change ProtectedInclusionAt runtime leaks (RecoveryProjection.execution runtime leaks
    (RecoveryProjection.liftExecution runtime leaks control.execution)) bound at actual
  simpa only [RecoveryProjection.execution_liftExecution] using actual

/-- Recovery completion implies native completion at clear native terminal
histories, without assuming completion of native histories after failure. -/
theorem CompletesPlay.clear_native
    {initial : PMF (RecoveryState graph)}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState graph))
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    (completes : CompletesPlay runtime leaks initial horizon scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (initial.map RecoveryState.native)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (clear : PublicExclusionRecord (⟨control.execution.application, ∅⟩ : RecoveryState graph))
    (stopped : (runtime.reactiveApplication leaks).terminal (some control)) :
    control.execution.application.config.cut.Terminal := by
  have lifted := RecoveryProjection.recoveryTrace runtime leaks initial initialized horizon
    scheduler trace (by intro current same; cases Option.some.inj same; exact clear)
  exact completes (RecoveryProjection.liftControl runtime leaks control) lifted
    ((RecoveryProjection.terminal_liftProtocolState runtime leaks (some control)).mpr stopped)

end Vegas.EventGraphRuntime.Recovery
