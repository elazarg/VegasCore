/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionClearKernel

/-! # Genuine recovery lifts of clear native execution steps -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A publicly clear native inclusion cannot activate automatic exclusion. -/
theorem includePending_empty_of_record
    (current : (runtime.recoveryApplication leaks).Execution)
    (valid : PublicExclusionRecord current.application)
    (empty : current.application.excluded = ∅) (id : MessageId Player)
    (clear : PublicExclusionRecord
      (⟨((execution runtime leaks current).includePending
        (runtime.reactiveApplication leaks) id).application, ∅⟩ : RecoveryState graph)) :
    (current.includePending (runtime.recoveryApplication leaks) id).application.excluded = ∅ := by
  classical
  simp only [ReactiveApplication.Execution.includePending, execution] at clear ⊢
  generalize current.network.includePending id = queued at clear ⊢
  rcases queued with ⟨envelope, network⟩
  cases envelope with
  | none => exact empty
  | some message =>
    by_cases token : message.payload.tokenValid = true
    · cases accepted : EventGraphRuntime.handle runtime current.application.native
        ⟨message.id, message.payload.call⟩ with
      | none =>
        simpa only [recoveryApplication, RecoveryState.handle,
          RecoveryState.excludedCall_of_empty current.application empty,
          Bool.false_eq_true, ↓reduceIte, token, accepted, Option.map_none,
          Option.getD_none] using empty
      | some native =>
        have clearNative : PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState graph) := by
          simpa only [reactiveApplication, token, ↓reduceIte, accepted, Option.getD_some]
            using clear
        have reduced := inclusionResult_eq_of_record runtime current.application valid _
          native accepted clearNative
        simp only [recoveryApplication, RecoveryState.handle,
          RecoveryState.excludedCall_of_empty current.application empty,
          Bool.false_eq_true, ↓reduceIte, token, accepted, Option.map_some,
          Option.getD_some, reduced]
    · have invalid : message.payload.tokenValid = false := Bool.eq_false_iff.mpr token
      simpa only [recoveryApplication, RecoveryState.handle,
        RecoveryState.excludedCall_of_empty current.application empty,
        Bool.false_eq_true, ↓reduceIte, invalid, Option.getD_none] using empty


/-- Clear lifting commutes with responses, including the complete private
recall and the emitted witnessed packet. -/
theorem respond_lift (current : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action) :
    (liftExecution runtime leaks current).respond (runtime.recoveryApplication leaks) who
        (liftAction runtime leaks response) =
      liftExecution runtime leaks (current.respond (runtime.reactiveApplication leaks)
        who response) := by
  cases response with
  | mk transmission =>
    cases transmission with
    | none =>
      simp only [ReactiveApplication.Execution.respond, liftExecution, liftAction]
      congr 1
      funext observer
      split <;> simp_all only [List.map_append, List.map_cons, List.map_nil]
      rfl
    | some material =>
      have packet : (runtime.recoveryApplication leaks).packet
          ((runtime.recoveryApplication leaks).submit
            (⟨current.application, ∅⟩ : RecoveryState graph) who material)
          who (current.network.known who) material =
        (runtime.reactiveApplication leaks).packet
          ((runtime.reactiveApplication leaks).submit current.application who material)
          who (current.network.known who) material :=
        RecoveryState.emit_of_empty
          ((runtime.recoveryApplication leaks).submit
            (⟨current.application, ∅⟩ : RecoveryState graph) who material)
          rfl who (current.network.known who) material
      simp only [ReactiveApplication.Execution.respond, liftExecution, liftAction]
      rw [packet]
      congr 1
      funext observer
      split <;> simp_all only [List.map_append, List.map_cons, List.map_nil]
      rfl

/-- Lift a genuine native environment outcome that has no public failure.
The shared leak draw or application draw is also an actual recovery draw. -/
theorem environmentStep_lift_support
    (current next : (runtime.reactiveApplication leaks).Execution)
    (valid : PublicExclusionRecord (⟨current.application, ∅⟩ : RecoveryState graph))
    (chosen : (runtime.reactiveApplication leaks).Command)
    (clear : PublicExclusionRecord (⟨next.application, ∅⟩ : RecoveryState graph))
    (realized : next ∈ (current.environmentStep (runtime.reactiveApplication leaks)
      chosen).support) :
    liftExecution runtime leaks next ∈ ((liftExecution runtime leaks current).environmentStep
      (runtime.recoveryApplication leaks) (liftCommand runtime leaks chosen)).support := by
  classical
  cases chosen with
  | wait =>
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff] at realized
    subst next
    simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff, liftExecution, List.map_append, List.map_cons, List.map_nil,
      liftEnvironmentEntry, liftEnvironmentView]
    rfl
  | activate who =>
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, Function.comp_def]
      at realized
    rw [PMF.mem_support_map_iff] at realized
    obtain ⟨selected, supported, rfl⟩ := realized
    simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.map_comp,
      Function.comp_def]
    rw [PMF.mem_support_map_iff]
    refine ⟨selected, supported, ?_⟩
    simp only [liftExecution, List.map_append, List.map_cons, List.map_nil,
      liftEnvironmentEntry, liftEnvironmentView]
    rfl
  | «include» id =>
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff] at realized
    subst next
    have targetClear : PublicExclusionRecord
        (⟨(current.includePending (runtime.reactiveApplication leaks) id).application, ∅⟩ :
          RecoveryState graph) := clear
    have empty := includePending_empty_of_record runtime leaks (liftExecution runtime leaks
      current) valid rfl id (by simpa only [execution_liftExecution] using targetClear)
    have projected := includePending_of_empty_after runtime leaks
      (liftExecution runtime leaks current) id rfl empty
    rw [execution_liftExecution] at projected
    have completeClear := liftExecution_execution_of_clear runtime leaks
      ((liftExecution runtime leaks current).includePending (runtime.recoveryApplication leaks) id)
      empty ?_ ?_
    · have liftedIncluded : liftExecution runtime leaks
          (current.includePending (runtime.reactiveApplication leaks) id) =
          (liftExecution runtime leaks current).includePending
            (runtime.recoveryApplication leaks) id := by
        rw [← projected]
        exact completeClear
      simp only [liftCommand, ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff]
      calc
        _ = { liftExecution runtime leaks
              (current.includePending (runtime.reactiveApplication leaks) id) with
            environmentRecall := (liftExecution runtime leaks current).environmentRecall ++
              [(⟨(liftExecution runtime leaks current).observeEnvironment
                (runtime.recoveryApplication leaks), .include id⟩ :
                  (runtime.recoveryApplication leaks).EnvironmentEntry)] } := by
          simp only [liftExecution, List.map_append, List.map_cons, List.map_nil,
            liftEnvironmentEntry, liftEnvironmentView]
          rfl
        _ = _ := by rw [liftedIncluded]
    · intro who entry member
      have unchanged : ((liftExecution runtime leaks current).includePending
          (runtime.recoveryApplication leaks) id).recall =
          (liftExecution runtime leaks current).recall := by
        unfold ReactiveApplication.Execution.includePending
        split
        split <;> rfl
      rw [unchanged] at member
      change entry ∈ (current.recall who).map (liftPlayerEntry runtime leaks) at member
      obtain ⟨old, _supported, rfl⟩ := List.mem_map.mp member
      rfl
    · intro entry member
      have unchanged : ((liftExecution runtime leaks current).includePending
          (runtime.recoveryApplication leaks) id).environmentRecall =
          (liftExecution runtime leaks current).environmentRecall := by
        unfold ReactiveApplication.Execution.includePending
        split
        split <;> rfl
      rw [unchanged] at member
      change entry ∈ current.environmentRecall.map (liftEnvironmentEntry runtime leaks) at member
      obtain ⟨old, _supported, rfl⟩ := List.mem_map.mp member
      rfl
  | application chosen =>
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, Function.comp_def]
      at realized
    rw [PMF.mem_support_map_iff] at realized
    obtain ⟨native, supported, rfl⟩ := realized
    have clearNative : PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState graph) := clear
    have reduced := environmentResult_eq_of_record runtime
      (⟨current.application, ∅⟩ : RecoveryState graph) valid chosen native supported clearNative
    simp only [liftCommand, ReactiveApplication.Execution.environmentStep, recoveryApplication,
      RecoveryState.environment, PMF.map_comp, Function.comp_def]
    rw [PMF.mem_support_map_iff]
    refine ⟨native, supported, ?_⟩
    simp only [liftExecution, reduced, List.map_append, List.map_cons, List.map_nil,
      liftEnvironmentEntry, liftEnvironmentView]
    rfl

end Vegas.EventGraphRuntime.RecoveryProjection
