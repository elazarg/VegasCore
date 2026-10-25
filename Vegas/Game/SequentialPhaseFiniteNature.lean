/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseTransition
import Vegas.Pending.ExclusionFiniteNature

/-! # Original-prior finite nature for the decoded sequential service

The decoded scheduler is a direct image of the original phase scheduler at its
decoded input, even when that input is unreachable. Statically tagged pending
lists supply the original observation law. Projecting the actual initial phase
state retains the same inputs and the empty permanent exclusion set.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseSchedulerInformation

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks (plan)
local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication (recoveryLeaks)
local notation "N" => runtime.reactiveApplication (recoveryLeaks)

/-- Finite nature of the actual phase service supplies finite nature of the
decoded recovery service with exactly the same original input prior. -/
theorem recovery_finiteNature
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs)
    (original : (P).Scheduler)
    [(P).FiniteNature (inputs.map (PhaseRuntimeState.initial (plan))) original] :
    (R).FiniteNature
      (inputs.map fun draw => (⟨State.initial draw, ∅⟩ : RecoveryState _))
      (scheduler program runtime leaks (recoveryLeaks) original) where
  observePending_finite who pending :=
    ReactiveApplication.FiniteEnvironment.observePending_finite (app := (P)) who
      (pending.map (Message.mapPayload (plan).stampPacket))
  environment_finite state command := by
    change (RecoveryState.environment runtime state command).support.Finite
    rw [RecoveryState.environment, PMF.support_map]
    exact (runtime.environmentStep_support_finite _ _).image _
  initial_finite := by
    have projected := (ReactiveApplication.FiniteNature.initial_finite
      (app := (P)) (initial := inputs.map (PhaseRuntimeState.initial (plan))) original).image
        PhaseRuntimeState.current
    have same : (inputs.map (PhaseRuntimeState.initial (plan))).map PhaseRuntimeState.current =
        inputs.map fun draw => (⟨State.initial draw, ∅⟩ : RecoveryState _) := by
      rw [PMF.map_comp]
      congr 1
      funext draw
      exact PhaseRuntimeState.initial_current_sequential (plan) draw
    rw [← PMF.support_map, same] at projected
    exact projected
  scheduler_finite past view := by
    rw [scheduler, PMF.support_map]
    exact (ReactiveApplication.FiniteNature.scheduler_finite
      (app := (P)) (inputs.map (PhaseRuntimeState.initial (plan))) _ _).image _

/-- The existing recovery-to-native instance retains that same original input
prior; no separate native-nature assumption is needed. -/
theorem native_finiteNature
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs)
    (original : (P).Scheduler)
    [(P).FiniteNature (inputs.map (PhaseRuntimeState.initial (plan))) original] :
    (N).FiniteNature (inputs.map State.initial)
      (RecoveryProjection.nativeScheduler runtime (recoveryLeaks)
        (scheduler program runtime leaks (recoveryLeaks) original)) := by
  have := recovery_finiteNature program runtime leaks inputs original
  have native := (inferInstance : (N).FiniteNature
    ((inputs.map fun draw => (⟨State.initial draw, ∅⟩ : RecoveryState _)).map RecoveryState.native)
    (RecoveryProjection.nativeScheduler runtime (recoveryLeaks)
      (scheduler program runtime leaks (recoveryLeaks) original)))
  simpa only [PMF.map_comp, Function.comp_def] using native

end Vegas.EventGraphRuntime.SequentialPhaseSchedulerInformation
