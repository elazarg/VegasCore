/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingExpiryReplay

/-! # Replaying actual clear phased expiry outcomes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A realized clear expiry has a genuine paired outcome in the image's actual
command law. Both the stuttering disallowed branch and automatic installation
after an allowed command retain the pre-command physical observation. -/
theorem expiry_coupling (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (next : (phaseApplication runtime leaks).Execution)
    (reached : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application (.expire event))).support)
    (clear : next.application.current.excluded = ∅) :
    ∃ image ∈ (repaired.environmentStep (phaseApplication runtime leaks)
        (.application (.expire event))).support,
      Frame runtime leaks memory owner next image := by
  let app := phaseApplication runtime leaks
  let chosen : app.Command := .application (.expire event)
  let finish (physical : app.Execution) (state : PhaseRuntimeState graph) : app.Execution :=
    { physical with
      application := state
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment app, chosen⟩] }
  have resultSelf (state : RecoveryState graph) :
      state.environmentResult (.expire event) state.native = state := by
    change (⟨state.native, if event ∉ state.native.config.cut.completed ∧
      event ∈ state.native.config.cut.completed then _ else state.excluded⟩ :
        RecoveryState graph) = state
    have impossible : ¬(event ∉ state.native.config.cut.completed ∧
        event ∈ state.native.config.cut.completed) := fun both => both.1 both.2
    simp only [impossible, ↓reduceIte]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
  change next ∈ ((original.application.environment runtime (.expire event)).map
    (finish original)).support at reached
  obtain ⟨state, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  cases allowed : original.application.commandAllowed (.expire event) with
  | false =>
      have same : state = original.application := (PMF.mem_support_pure_iff _ _).mp (by
        simpa only [PhaseRuntimeState.environment, allowed, Bool.false_eq_true, ↓reduceIte]
          using moved)
      subst state
      have rightAllowed : repaired.application.commandAllowed (.expire event) = false := by
        change (repaired.application.phases.head?.any _) = false
        rw [← frame.phases]
        exact allowed
      have actual : repaired.environmentStep app chosen =
          PMF.pure (finish repaired repaired.application) := by
        simp only [ReactiveApplication.Execution.environmentStep, app, chosen, phaseApplication,
          PhaseRuntimeState.environment, rightAllowed, Bool.false_eq_true, ↓reduceIte,
          PMF.pure_map]
        rfl
      refine ⟨finish repaired repaired.application, ?_, frame.record_environment chosen⟩
      rw [actual, PMF.mem_support_pure_iff]
  | true =>
      have nativeMove : state ∈ ((environmentStep runtime original.application.current.native
          (.expire event)).map fun native =>
            ({ original.application with current :=
              original.application.current.environmentResult (.expire event) native } :
                PhaseRuntimeState graph).normalize).support := by
        simpa only [PhaseRuntimeState.environment, allowed, ↓reduceIte] using moved
      obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp nativeMove
      have rawClear : (original.application.current.environmentResult (.expire event)
          native).excluded = ∅ := by
        have preserved := (PhaseRuntimeState.settle_physical original.application.phases
          original.application.generation original.application.entry
          (original.application.current.environmentResult (.expire event) native)
          original.application.retired).1
        exact preserved.symm.trans clear
      have stutters := frame.expiry_native_stutter event native supported rawClear
      rw [stutters.1, PMF.mem_support_pure_iff] at supported
      subst native
      have rightAllowed : repaired.application.commandAllowed (.expire event) = true := by
        change (repaired.application.phases.head?.any _) = true
        rw [← frame.phases]
        exact allowed
      have actual : repaired.environmentStep app chosen =
          PMF.pure (PhaseRuntimeState.normalizeExecution runtime leaks
            (finish repaired repaired.application)) := by
        simp only [ReactiveApplication.Execution.environmentStep, app, chosen, phaseApplication,
          PhaseRuntimeState.environment, rightAllowed, ↓reduceIte, stutters.2, PMF.pure_map,
          resultSelf]
        rfl
      refine ⟨PhaseRuntimeState.normalizeExecution runtime leaks
        (finish repaired repaired.application), ?_, ?_⟩
      · rw [actual, PMF.mem_support_pure_iff]
      · have eta : ({ original.application with current := original.application.current } :
            PhaseRuntimeState graph) = original.application := by
          cases original.application; rfl
        have pair := (frame.record_environment chosen).normalize
        simpa only [finish, resultSelf, eta, PhaseRuntimeState.normalizeExecution] using pair

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
