/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingExpiry

/-! # Application commands along a completed binding-repair frame

Public chance, clock advancement and expiry have joint laws in the actual
reactive evaluator. A completed shadow permits every application command:
its remembered outcomes concern completed events, so a ready event cannot
have a pending private override. This does not cover packet inclusion or
expiry while an overridden binding is still pending.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Actual application stutters preserve the full frame and append equal
service observations, even while a private completion override is pending. -/
theorem application_stutter_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (command : EnvironmentCommand graph)
    (leftStays : environmentStep runtime original.application command =
      PMF.pure original.application)
    (rightStays : environmentStep runtime repaired.application command =
      PMF.pure repaired.application) :
    let app := runtime.reactiveApplication leaks
    ∃ coupled : PMF (app.Execution × app.Execution),
      coupled.map Prod.fst = original.environmentStep app (.application command) ∧
      coupled.map Prod.snd = repaired.environmentStep app (.application command) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  let app := runtime.reactiveApplication leaks
  let record (execution : app.Execution) : app.Execution :=
    { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application command⟩] }
  have actual (execution : app.Execution)
      (stays : environmentStep runtime execution.application command =
        PMF.pure execution.application) :
      execution.environmentStep app (.application command) = PMF.pure (record execution) := by
    change ((environmentStep runtime execution.application command).map _).map _ = _
    rw [stays, PMF.pure_map, PMF.pure_map]
  refine ⟨PMF.pure (record original, record repaired), ?_, ?_, ?_⟩
  · rw [PMF.pure_map, actual original leftStays]
  · rw [PMF.pure_map, actual repaired rightStays]
  · intro pair supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact { frame with
      service := by
        change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
        rw [frame.service, frame.environment] }

/-- Every sample command has a common-draw coupling, including unready events
and commands addressed to binding or resolution nodes that stutter. -/
theorem executeSample_coupling (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner) (event : graph.EventId) :
    let app := runtime.reactiveApplication leaks
    ∃ coupled : PMF (app.Execution × app.Execution),
      coupled.map Prod.fst = original.environmentStep app (.application (.executeSample event)) ∧
      coupled.map Prod.snd = repaired.environmentStep app (.application (.executeSample event)) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  have readiness : original.application.config.cut.Ready event ↔
      repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← State.publicView_eventReady, frame.publicView]
  by_cases ready : original.application.config.cut.Ready event
  · cases node : nodeView graph event with
    | sample payload law outputEq codeEq =>
        exact frame.sample_coupling onlyBindings event ready payload law outputEq codeEq node
    | bind actor payload outputEq codeEq =>
        have notSample : ∀ ty law shape code,
            nodeView graph event ≠ .sample ty law shape code := by
          intro ty law shape code
          rw [node]
          intro impossible
          cases impossible
        exact frame.application_stutter_coupling (.executeSample event)
          (environmentStep_executeSample_of_nonsample runtime original.application event ready
            notSample)
          (environmentStep_executeSample_of_nonsample runtime repaired.application event
            (readiness.mp ready) notSample)
    | resolve actor payload binding checks outputEq codeEq =>
        have notSample : ∀ ty law shape code,
            nodeView graph event ≠ .sample ty law shape code := by
          intro ty law shape code
          rw [node]
          intro impossible
          cases impossible
        exact frame.application_stutter_coupling (.executeSample event)
          (environmentStep_executeSample_of_nonsample runtime original.application event ready
            notSample)
          (environmentStep_executeSample_of_nonsample runtime repaired.application event
            (readiness.mp ready) notSample)
  · exact frame.application_stutter_coupling (.executeSample event)
      (environmentStep_executeSample_of_not_ready runtime original.application event ready)
      (environmentStep_executeSample_of_not_ready runtime repaired.application event
        (fun other => ready (readiness.mpr other)))

/-- The actual clock command preserves the frame and records both equal
service observations. No event-specific timing premise is needed. -/
theorem advanceClock_coupling (frame : Frame runtime leaks memory owner original repaired) :
    let app := runtime.reactiveApplication leaks
    ∃ coupled : PMF (app.Execution × app.Execution),
      coupled.map Prod.fst = original.environmentStep app (.application .advanceClock) ∧
      coupled.map Prod.snd = repaired.environmentStep app (.application .advanceClock) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  let app := runtime.reactiveApplication leaks
  let advance (execution : app.Execution) : app.Execution :=
    { execution with
      application := { execution.application with clock := execution.application.clock + 1 }
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .application .advanceClock⟩] }
  have actual (execution : app.Execution) :
      execution.environmentStep app (.application .advanceClock) =
        PMF.pure (advance execution) := by
    change ((PMF.pure { execution.application with
      clock := execution.application.clock + 1 }).map _).map _ = _
    rw [PMF.pure_map, PMF.pure_map]
  refine ⟨PMF.pure (advance original, advance repaired), ?_, ?_, ?_⟩
  · rw [PMF.pure_map, actual]
  · rw [PMF.pure_map, actual]
  · intro pair supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact frame.advanceClock

/-- Expiry is coupled once remembered outcomes refer only to completed
events. Pending overrides are deliberately outside this premise. -/
theorem expire_completed_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (past : memory.shadow.CompletedAt original.application.config) (event : graph.EventId) :
    let app := runtime.reactiveApplication leaks
    ∃ coupled : PMF (app.Execution × app.Execution),
      coupled.map Prod.fst = original.environmentStep app (.application (.expire event)) ∧
      coupled.map Prod.snd = repaired.environmentStep app (.application (.expire event)) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  let app := runtime.reactiveApplication leaks
  by_cases ready : original.application.config.cut.Ready event
  · obtain ⟨noAction, noValue⟩ := past.ready_none event ready
    let left := original.environmentStep app (.application (.expire event))
    let right := repaired.environmentStep app (.application (.expire event))
    let coupled := left.bind fun first => right.map fun second => (first, second)
    refine ⟨coupled, ?_, ?_, ?_⟩
    · simp only [coupled, PMF.map_bind, PMF.map_comp, Function.comp_def]
      rw [show (fun first => right.map (fun _ => first)) =
          (fun first => PMF.pure first) from funext fun _ => PMF.map_const _ _]
      exact PMF.bind_pure _
    · simp only [coupled, PMF.map_bind, PMF.map_comp, Function.comp_def]
      change (left.bind fun _ => right.map id) = right
      rw [PMF.map_id]
      exact PMF.bind_const _ _
    · intro pair supported
      obtain ⟨first, leftSupport, next⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨second, rightSupport, rfl⟩ := PMF.support_map .. ▸ next
      exact frame.expiry_unmodified event noValue noAction first second leftSupport rightSupport
  · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
      rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
      exact ready
    exact frame.application_stutter_coupling (.expire event)
      (environmentStep_expire_of_not_ready runtime original.application event ready)
      (environmentStep_expire_of_not_ready runtime repaired.application event rightNotReady)

/-- All runtime application commands are covered at completed repair
boundaries. The joint relation includes actual private recall and audit data. -/
theorem application_coupling (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (command : EnvironmentCommand graph) :
    let app := runtime.reactiveApplication leaks
    ∃ coupled : PMF (app.Execution × app.Execution),
      coupled.map Prod.fst = original.environmentStep app (.application command) ∧
      coupled.map Prod.snd = repaired.environmentStep app (.application command) ∧
      ∀ pair ∈ coupled.support, Frame runtime leaks memory owner pair.1 pair.2 := by
  cases command with
  | advanceClock => exact frame.advanceClock_coupling
  | executeSample event => exact frame.executeSample_coupling onlyBindings event
  | expire event => exact frame.expire_completed_coupling past event

end Vegas.EventGraphRuntime.BindingMemory.Frame
