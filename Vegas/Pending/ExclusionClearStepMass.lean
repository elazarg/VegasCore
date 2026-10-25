/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionLiftedSteps

/-! # Actual environment probabilities before public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem liftExecution_injective : Function.Injective (liftExecution runtime leaks) :=
  Function.LeftInverse.injective (execution_liftExecution runtime leaks)

theorem environmentStep_lift_support_iff
    (current next : (runtime.reactiveApplication leaks).Execution)
    (valid : ExclusionEvidence 0 ∅ (⟨current.application, ∅⟩ : RecoveryState graph))
    (chosen : (runtime.reactiveApplication leaks).Command)
    (clear : ExclusionEvidence 0 ∅ (⟨next.application, ∅⟩ : RecoveryState graph)) :
    liftExecution runtime leaks next ∈ ((liftExecution runtime leaks current).environmentStep
      (runtime.recoveryApplication leaks) (liftCommand runtime leaks chosen)).support ↔
      next ∈ (current.environmentStep (runtime.reactiveApplication leaks) chosen).support := by
  constructor
  · intro supported
    have projected := environmentStep_projected_support runtime leaks
      (liftExecution runtime leaks current) (liftExecution runtime leaks next)
      (liftCommand runtime leaks chosen) rfl rfl supported
    simpa only [execution_liftExecution, command_liftCommand] using projected
  · exact environmentStep_lift_support runtime leaks current next valid chosen clear

/-- Every full native execution with no public failure has exactly the same
one-step environment probability as its genuine recovery lift. -/
theorem environmentStep_lift_apply
    (current next : (runtime.reactiveApplication leaks).Execution)
    (valid : ExclusionEvidence 0 ∅ (⟨current.application, ∅⟩ : RecoveryState graph))
    (chosen : (runtime.reactiveApplication leaks).Command)
    (clear : ExclusionEvidence 0 ∅ (⟨next.application, ∅⟩ : RecoveryState graph)) :
    ((liftExecution runtime leaks current).environmentStep (runtime.recoveryApplication leaks)
        (liftCommand runtime leaks chosen)) (liftExecution runtime leaks next) =
      (current.environmentStep (runtime.reactiveApplication leaks) chosen) next := by
  classical
  by_cases supported : next ∈
      (current.environmentStep (runtime.reactiveApplication leaks) chosen).support
  · have newSupported := environmentStep_lift_support runtime leaks current next valid chosen
      clear supported
    cases chosen with
    | wait =>
      simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        at supported newSupported ⊢
      rw [(PMF.mem_support_pure_iff _ _).mp newSupported,
        (PMF.mem_support_pure_iff _ _).mp supported, PMF.pure_apply_self, PMF.pure_apply_self]
    | «include» id =>
      simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        at supported newSupported ⊢
      rw [(PMF.mem_support_pure_iff _ _).mp newSupported,
        (PMF.mem_support_pure_iff _ _).mp supported, PMF.pure_apply_self, PMF.pure_apply_self]
    | activate who =>
      have law : (liftExecution runtime leaks current).environmentStep
          (runtime.recoveryApplication leaks) (liftCommand runtime leaks (.activate who)) =
          (current.environmentStep (runtime.reactiveApplication leaks) (.activate who)).map
            (liftExecution runtime leaks) := by
        simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.map_comp,
          Function.comp_def]
        congr 1
        funext selected
        simp only [liftExecution, List.map_append, List.map_cons, List.map_nil,
          liftEnvironmentEntry, liftEnvironmentView]
        rfl
      rw [law, pmf_map_apply_of_injective _ (liftExecution_injective runtime leaks)]
    | application chosen =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, Function.comp_def]
        at supported
      rw [PMF.mem_support_map_iff] at supported
      obtain ⟨native, nativeSupported, rfl⟩ := supported
      let oldNext : State graph → (runtime.reactiveApplication leaks).Execution := fun state =>
        ⟨state, current.network, current.receipts, current.recall,
          current.environmentRecall ++
            [⟨current.observeEnvironment (runtime.reactiveApplication leaks), .application chosen⟩]⟩
      let newNext : RecoveryState graph → (runtime.recoveryApplication leaks).Execution :=
        fun state => ⟨state, (liftExecution runtime leaks current).network,
          (liftExecution runtime leaks current).receipts,
          (liftExecution runtime leaks current).recall,
          (liftExecution runtime leaks current).environmentRecall ++
            [⟨(liftExecution runtime leaks current).observeEnvironment
              (runtime.recoveryApplication leaks), .application chosen⟩]⟩
      have oldInjective : Function.Injective oldNext := fun first second same =>
        congrArg (fun execution => execution.application) same
      have newInjective : Function.Injective newNext := fun first second same =>
        congrArg (fun execution => execution.application) same
      have lifted : liftExecution runtime leaks (oldNext native) = newNext ⟨native, ∅⟩ := by
        simp only [oldNext, newNext, liftExecution, List.map_append, List.map_cons, List.map_nil,
          liftEnvironmentEntry, liftEnvironmentView]
        rfl
      simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.map_comp,
        Function.comp_def]
      change (((⟨current.application, ∅⟩ : RecoveryState graph).environment runtime chosen).map
          newNext) (liftExecution runtime leaks (oldNext native)) =
        ((environmentStep runtime current.application chosen).map oldNext) (oldNext native)
      rw [lifted, pmf_map_apply_of_injective _ newInjective,
        pmf_map_apply_of_injective _ oldInjective]
      exact environment_apply_clear runtime _ valid chosen native clear
  · have absent : liftExecution runtime leaks next ∉
        ((liftExecution runtime leaks current).environmentStep (runtime.recoveryApplication leaks)
          (liftCommand runtime leaks chosen)).support := by
      rw [environmentStep_lift_support_iff runtime leaks current next valid chosen clear]
      exact supported
    rw [(PMF.apply_eq_zero_iff _ _).mpr absent, (PMF.apply_eq_zero_iff _ _).mpr supported]

end Vegas.EventGraphRuntime.RecoveryProjection
