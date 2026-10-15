/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingEnvironmentTrace

/-! # Every actual clear application command has a paired physical outcome -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

theorem command_admission (frame : Frame runtime leaks memory owner original repaired)
    (chosen : EnvironmentCommand graph) :
    original.application.commandAllowed chosen = repaired.application.commandAllowed chosen := by
  cases chosen <;> simp only [PhaseRuntimeState.commandAllowed, frame.phases]

private theorem disallowed_application (frame : Frame runtime leaks memory owner original repaired)
    (chosen : EnvironmentCommand graph)
    (denied : original.application.commandAllowed chosen = false)
    (next : (phaseApplication runtime leaks).Execution)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application chosen)).support) :
    ∃ image ∈ (repaired.environmentStep (phaseApplication runtime leaks)
        (.application chosen)).support, Frame runtime leaks memory owner next image := by
  let app := phaseApplication runtime leaks
  let finish (physical : app.Execution) : app.Execution :=
    { physical with environmentRecall := physical.environmentRecall ++
      [⟨physical.observeEnvironment app, .application chosen⟩] }
  have actual (physical : app.Execution)
      (disallowed : physical.application.commandAllowed chosen = false) :
      physical.environmentStep app (.application chosen) = PMF.pure (finish physical) := by
    simp only [ReactiveApplication.Execution.environmentStep, app, phaseApplication,
      PhaseRuntimeState.environment, disallowed, Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
    rfl
  rw [actual original denied, PMF.mem_support_pure_iff] at moved
  subst next
  refine ⟨finish repaired, ?_, frame.record_environment (.application chosen)⟩
  rw [actual repaired ((frame.command_admission chosen).symm.trans denied),
    PMF.mem_support_pure_iff]

private theorem inactive_sample (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId)
    (allowed : original.application.commandAllowed (.executeSample event) = true)
    (leftNative : environmentStep runtime original.application.current.native
      (.executeSample event) = PMF.pure original.application.current.native)
    (rightNative : environmentStep runtime repaired.application.current.native
      (.executeSample event) = PMF.pure repaired.application.current.native)
    (next : (phaseApplication runtime leaks).Execution)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application (.executeSample event))).support) :
    ∃ image ∈ (repaired.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event))).support,
      Frame runtime leaks memory owner next image := by
  let app := phaseApplication runtime leaks
  let finish (physical : app.Execution) : app.Execution :=
    PhaseRuntimeState.normalizeExecution runtime leaks
      { physical with environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment app, .application (.executeSample event)⟩] }
  have actual (physical : app.Execution)
      (admitted : physical.application.commandAllowed (.executeSample event) = true)
      (native : environmentStep runtime physical.application.current.native (.executeSample event) =
        PMF.pure physical.application.current.native) :
      physical.environmentStep app (.application (.executeSample event)) =
        PMF.pure (finish physical) := by
    have eta : ({ physical.application with current := physical.application.current } :
        PhaseRuntimeState graph) = physical.application := by
      cases physical.application; rfl
    simp only [ReactiveApplication.Execution.environmentStep, app, phaseApplication,
      PhaseRuntimeState.environment, admitted, ↓reduceIte, native, PMF.pure_map,
      RecoveryState.environmentResult]
    change PMF.pure { physical with
      application := ({ physical.application with current := physical.application.current } :
        PhaseRuntimeState graph).normalize
      environmentRecall := physical.environmentRecall ++ [_] } = _
    rw [eta]
    rfl
  rw [actual original allowed leftNative, PMF.mem_support_pure_iff] at moved
  subst next
  refine ⟨finish repaired, ?_, (frame.record_environment
    (.application (.executeSample event))).normalize⟩
  rw [actual repaired ((frame.command_admission _).symm.trans allowed) rightNative,
    PMF.mem_support_pure_iff]

/-- All actual application-command cases are replayed, including disallowed
commands, public chance, physical clock advancement, and clear surviving expiry.
No image support, target transition, or application service law is supplied. -/
theorem application_coupling (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner) (chosen : EnvironmentCommand graph)
    (next : (phaseApplication runtime leaks).Execution)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application chosen)).support)
    (clear : next.application.current.excluded = ∅) :
    ∃ image ∈ (repaired.environmentStep (phaseApplication runtime leaks)
        (.application chosen)).support, Frame runtime leaks memory owner next image := by
  cases chosen with
  | advanceClock =>
      rw [clock_environment, PMF.mem_support_pure_iff] at moved
      subst next
      refine ⟨_, ?_, frame.clock⟩
      rw [clock_environment, PMF.mem_support_pure_iff]
  | expire event => exact frame.expiry_coupling event next moved clear
  | executeSample event =>
      by_cases allowed : original.application.commandAllowed (.executeSample event) = true
      · have publicNative : original.application.current.native.publicView =
            repaired.application.current.native.publicView := frame.live.publicView
        by_cases ready : original.application.current.native.config.cut.Ready event
        · have rightReady : repaired.application.current.native.config.cut.Ready event := by
            rw [← State.publicView_eventReady, ← publicNative, State.publicView_eventReady]
            exact ready
          cases node : nodeView graph event with
          | bind actor payload outputEq codeEq =>
              have nonsample : ∀ payload law outputEq codeEq,
                  nodeView graph event ≠ .sample payload law outputEq codeEq := by
                intro _ _ _ _ impossible
                rw [node] at impossible
                cases impossible
              exact frame.inactive_sample event allowed
                (environmentStep_executeSample_of_nonsample runtime _ event ready nonsample)
                (environmentStep_executeSample_of_nonsample runtime _ event rightReady nonsample)
                next moved
          | resolve actor payload binding checks outputEq codeEq =>
              have nonsample : ∀ payload law outputEq codeEq,
                  nodeView graph event ≠ .sample payload law outputEq codeEq := by
                intro _ _ _ _ impossible
                rw [node] at impossible
                cases impossible
              exact frame.inactive_sample event allowed
                (environmentStep_executeSample_of_nonsample runtime _ event ready nonsample)
                (environmentStep_executeSample_of_nonsample runtime _ event rightReady nonsample)
                next moved
          | sample payload law outputEq codeEq =>
              obtain ⟨coupled, leftLaw, rightLaw, valid⟩ := frame.sample_coupling onlyBindings
                event ready payload law outputEq codeEq node allowed
              rw [← leftLaw, PMF.mem_support_map_iff] at moved
              obtain ⟨pair, supported, same⟩ := moved
              refine ⟨pair.2, ?_, ?_⟩
              · rw [← rightLaw, PMF.mem_support_map_iff]
                exact ⟨pair, supported, rfl⟩
              · rw [← same]
                exact valid pair supported
        · have rightReady : ¬ repaired.application.current.native.config.cut.Ready event := by
            rw [← State.publicView_eventReady, ← publicNative, State.publicView_eventReady]
            exact ready
          exact frame.inactive_sample event allowed
            (environmentStep_executeSample_of_not_ready runtime _ event ready)
            (environmentStep_executeSample_of_not_ready runtime _ event rightReady) next moved
      · exact frame.disallowed_application (.executeSample event)
          (Bool.eq_false_iff.mpr allowed) next moved

/-- Every supported clear source application move extends the actual repaired
prefix under the very same scheduler, with no target history hypothesis. -/
theorem application_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩))
    (onlyBindings : memory.shadow.OwnBindings owner) (chosen : EnvironmentCommand graph)
    (next : (phaseApplication runtime leaks).Execution)
    (selected : ((.application chosen) : (phaseApplication runtime leaks).Command) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks)
      (.application chosen)).support)
    (clear : next.application.current.excluded = ∅) :
    ∃ image, Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, image⟩)) ∧ Frame runtime leaks memory owner next image := by
  obtain ⟨image, supported, paired⟩ :=
    frame.application_coupling onlyBindings chosen next moved clear
  have atom : ((.application chosen) : (phaseApplication runtime leaks).Command) ∈
      (scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  exact ⟨image, menu.trace_environment initial horizon scheduler remaining repaired _
    (.application chosen) prior atom supported, paired⟩

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
