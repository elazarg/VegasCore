/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionLiftTrace
import Vegas.Pending.ReactiveAsyncContract

/-! # Completion by the recovery service

Completion is required on actual recovery histories, including histories after
exclusion. Its transport to the native runtime is restricted to public-clear
histories; it does not impose a global native completion contract.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Every actual terminal recovery execution has completed the native graph. -/
def CompletesPlay (initial : PMF (RecoveryState graph)) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler) : Prop :=
  ∀ control, ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some control) →
    (runtime.recoveryApplication leaks).terminal (some control) →
    control.execution.application.native.config.cut.Terminal

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
