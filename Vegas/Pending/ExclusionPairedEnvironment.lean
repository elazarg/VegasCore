/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionProjection
import Vegas.Pending.ExclusionBoundary

/-! # Paired actual environment kernels before exclusion

The native and recovery environments share their random selection and native
application outcome. Their complete executions agree under projection whenever
the recovery transition has not crossed into permanent exclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Native inclusion agrees with projected recovery inclusion when its start
and its result both have empty permanent exclusion. -/
theorem includePending_of_empty_after
    (current : (runtime.recoveryApplication leaks).Execution) (id : MessageId Player)
    (empty : current.application.excluded = ∅)
    (clear : (current.includePending (runtime.recoveryApplication leaks) id).application.excluded =
      ∅) :
    execution runtime leaks (current.includePending (runtime.recoveryApplication leaks) id) =
      (execution runtime leaks current).includePending (runtime.reactiveApplication leaks) id := by
  classical
  simp only [ReactiveApplication.Execution.includePending, execution] at clear ⊢
  generalize current.network.includePending id = queued at clear ⊢
  rcases queued with ⟨envelope, network⟩
  cases envelope with
  | none => rfl
  | some message =>
    by_cases token : message.payload.tokenValid = true
    · cases accepted : EventGraphRuntime.handle runtime current.application.native
        ⟨message.id, message.payload.call⟩ with
      | none =>
        simp only [recoveryApplication, RecoveryState.handle,
          RecoveryState.excludedCall_of_empty current.application empty,
          Bool.false_eq_true, ↓reduceIte, token, accepted, Option.map_none, Option.getD_none,
          Option.isSome_none, reactiveApplication]
      | some native =>
        have resultEmpty :
            (current.application.inclusionResult message.payload.call native).excluded = ∅ := by
          simpa only [recoveryApplication, RecoveryState.handle,
            RecoveryState.excludedCall_of_empty current.application empty,
            Bool.false_eq_true, ↓reduceIte, token, accepted, Option.map_some, Option.getD_some,
            RecoveryState.drain_excluded] using clear
        simp only [recoveryApplication, RecoveryState.handle,
          RecoveryState.excludedCall_of_empty current.application empty,
          Bool.false_eq_true, ↓reduceIte, token, accepted, Option.map_some, Option.getD_some,
          Option.isSome_some, reactiveApplication,
          RecoveryState.inclusionResult_drain_of_empty current.application
            message.payload.call native resultEmpty]
    · have invalid : message.payload.tokenValid = false := Bool.eq_false_iff.mpr token
      simp only [recoveryApplication, RecoveryState.handle,
        RecoveryState.excludedCall_of_empty current.application empty,
        Bool.false_eq_true, ↓reduceIte, invalid, Option.getD_none, Option.isSome_none,
        reactiveApplication]

private theorem recorded_environment_projection
    (current next : (runtime.recoveryApplication leaks).Execution)
    (chosen : (runtime.recoveryApplication leaks).Command) :
    execution runtime leaks { next with environmentRecall := current.environmentRecall ++
      [⟨current.observeEnvironment (runtime.recoveryApplication leaks), chosen⟩] } =
      { execution runtime leaks next with
        environmentRecall := (execution runtime leaks current).environmentRecall ++
          [⟨(execution runtime leaks current).observeEnvironment
            (runtime.reactiveApplication leaks), command runtime leaks chosen⟩] } := by
  rw [observeEnvironment runtime leaks current]
  simp only [execution, List.map_append, List.map_cons, List.map_nil, environmentEntry]

/-- Couple actual environment steps by their common selection or ordinary
native outcome. After a clear start, projection agrees at every coupled result
whose permanent excluded set remains empty. -/
theorem exists_paired_environmentStep
    (current : (runtime.recoveryApplication leaks).Execution)
    (chosen : (runtime.recoveryApplication leaks).Command)
    (empty : current.application.excluded = ∅) :
    ∃ joint : PMF ((runtime.reactiveApplication leaks).Execution ×
        (runtime.recoveryApplication leaks).Execution),
      joint.map Prod.fst = (execution runtime leaks current).environmentStep
        (runtime.reactiveApplication leaks) (command runtime leaks chosen) ∧
      joint.map Prod.snd = current.environmentStep (runtime.recoveryApplication leaks) chosen ∧
      ∀ pair ∈ joint.support, pair.2.application.excluded = ∅ →
        pair.1 = execution runtime leaks pair.2 := by
  classical
  let firstRemember : (runtime.reactiveApplication leaks).Execution →
      (runtime.reactiveApplication leaks).Execution := fun next =>
    { next with environmentRecall := (execution runtime leaks current).environmentRecall ++
      [⟨(execution runtime leaks current).observeEnvironment (runtime.reactiveApplication leaks),
        command runtime leaks chosen⟩] }
  let secondRemember : (runtime.recoveryApplication leaks).Execution →
      (runtime.recoveryApplication leaks).Execution := fun next =>
    { next with environmentRecall := current.environmentRecall ++
      [⟨current.observeEnvironment (runtime.recoveryApplication leaks), chosen⟩] }
  have remembered (next : (runtime.recoveryApplication leaks).Execution) :
      execution runtime leaks (secondRemember next) =
        firstRemember (execution runtime leaks next) :=
    recorded_environment_projection runtime leaks current next chosen
  cases chosen with
  | activate who =>
    let firstNext := fun selected => firstRemember
      { execution runtime leaks current with network := current.network.learn who selected }
    let secondNext := fun selected => secondRemember
      { current with network := current.network.learn who selected }
    refine ⟨(leaks who current.network.pending).map
      (fun selected => (firstNext selected, secondNext selected)), ?_, ?_, ?_⟩
    · simp only [PMF.map_comp, Function.comp_def, firstNext, firstRemember,
        ReactiveApplication.Execution.environmentStep, command, reactiveApplication, execution]
    · simp only [PMF.map_comp, Function.comp_def, secondNext, secondRemember,
        ReactiveApplication.Execution.environmentStep, recoveryApplication]
    · intro pair member _clear
      rw [PMF.mem_support_map_iff] at member
      obtain ⟨selected, _supported, rfl⟩ := member
      exact (remembered { current with network := current.network.learn who selected }).symm
  | wait =>
    refine ⟨PMF.pure (firstRemember (execution runtime leaks current), secondRemember current),
      ?_, ?_, ?_⟩
    · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, command,
        firstRemember]
    · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, secondRemember]
    · intro pair member _clear
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp member
      exact (remembered current).symm
  | «include» id =>
    let firstNext := (execution runtime leaks current).includePending
      (runtime.reactiveApplication leaks) id
    let secondNext := current.includePending (runtime.recoveryApplication leaks) id
    refine ⟨PMF.pure (firstRemember firstNext, secondRemember secondNext), ?_, ?_, ?_⟩
    · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, command,
        firstNext, firstRemember]
    · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep,
        secondNext, secondRemember]
    · intro pair member clear
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp member
      have same := includePending_of_empty_after runtime leaks current id empty clear
      exact (congrArg firstRemember same).symm.trans (remembered secondNext).symm
  | application chosen =>
    let firstNext := fun native => firstRemember
      { execution runtime leaks current with application := native }
    let secondNext := fun native => secondRemember
      { current with application := (current.application.environmentResult chosen native).drain }
    refine ⟨(environmentStep runtime current.application.native chosen).map
      (fun native => (firstNext native, secondNext native)), ?_, ?_, ?_⟩
    · simp only [PMF.map_comp, Function.comp_def, firstNext, firstRemember,
        ReactiveApplication.Execution.environmentStep, command, reactiveApplication, execution]
    · simp only [PMF.map_comp, Function.comp_def, secondNext, secondRemember,
        ReactiveApplication.Execution.environmentStep, recoveryApplication,
        RecoveryState.environment]
      rfl
    · intro pair member clear
      rw [PMF.mem_support_map_iff] at member
      obtain ⟨native, _supported, rfl⟩ := member
      have resultEmpty : (current.application.environmentResult chosen native).excluded = ∅ := by
        simpa only [secondNext, secondRemember, RecoveryState.drain_excluded] using clear
      have same : execution runtime leaks
          { current with application :=
            (current.application.environmentResult chosen native).drain } =
          { execution runtime leaks current with application := native } := by
        rw [RecoveryState.environmentResult_drain_of_empty current.application chosen native
          resultEmpty]
        rfl
      exact (congrArg firstRemember same).symm.trans
        (remembered { current with application :=
          (current.application.environmentResult chosen native).drain }).symm

end Vegas.EventGraphRuntime.RecoveryProjection
