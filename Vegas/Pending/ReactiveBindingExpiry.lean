/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameStep

/-! # Clock padding and expiry across a private binding repair

Expiry reads public readiness and deadline data. An event without a private
shadow entry therefore takes the same real failure or stuttering transition
on both executions. Public disclosures satisfy this condition even when their
underlying private commitments were repaired.
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

private theorem expiry_application_frame
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId)
    (noValue : memory.shadow.values (.inr event) = none)
    (noAction : memory.shadow.actions event = none)
    (left right : State graph)
    (leftSupport : left ∈ (environmentStep runtime original.application (.expire event)).support)
    (rightSupport : right ∈
      (environmentStep runtime repaired.application (.expire event)).support) :
    Frame runtime leaks memory owner { original with application := left }
      { repaired with application := right } := by
  have cuts := cut_eq_of_completionOrder_eq original.application.config repaired.application.config
    (congrArg (fun view : PublicView graph => view.observation.completionOrder) frame.publicView)
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have activations : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  by_cases ready : original.application.config.cut.Ready event
  · have rightReady : repaired.application.config.cut.Ready event := by
      rw [← cuts]
      exact ready
    cases activated : original.application.activatedAt event with
    | none =>
        have rightActivated : repaired.application.activatedAt event = none := by
          rw [← activations]
          exact activated
        rw [environmentStep_expire_of_not_activated runtime original.application event ready
          activated, FinDist.mem_support_pure] at leftSupport
        rw [environmentStep_expire_of_not_activated runtime repaired.application event rightReady
          rightActivated, FinDist.mem_support_pure] at rightSupport
        subst left
        subst right
        exact frame
    | some entered =>
        have rightActivated : repaired.application.activatedAt event = some entered := by
          rw [← activations]
          exact activated
        by_cases due : runtime.deadline event ≤ original.application.clock - entered
        · have rightDue : runtime.deadline event ≤ repaired.application.clock - entered := by
            rw [← clocks]
            exact due
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime original.application event ready entered
                activated due payload law outputEq codeEq node,
                  FinDist.mem_support_pure] at leftSupport
              rw [environmentStep_expire_sample_eq runtime repaired.application event rightReady
                entered rightActivated rightDue payload law outputEq codeEq node,
                  FinDist.mem_support_pure] at rightSupport
              subst left
              subst right
              exact frame
          | bind actor payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq runtime original.application event ready entered
                activated due actor payload outputEq codeEq node,
                  FinDist.mem_support_pure] at leftSupport
              rw [environmentStep_expire_bind_eq runtime repaired.application event rightReady
                entered rightActivated rightDue actor payload outputEq codeEq node,
                  FinDist.mem_support_pure] at rightSupport
              subst left
              subst right
              exact frame.complete_unmodified event ready rightReady noValue noAction _ _
          | resolve actor payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq runtime original.application event ready entered
                activated due actor payload binding checks outputEq codeEq node,
                  FinDist.mem_support_pure] at leftSupport
              rw [environmentStep_expire_resolve_eq runtime repaired.application event rightReady
                entered rightActivated rightDue actor payload binding checks outputEq codeEq node,
                  FinDist.mem_support_pure] at rightSupport
              subst left
              subst right
              exact frame.complete_unmodified event ready rightReady noValue noAction _ _
        · have rightNotDue : ¬ runtime.deadline event ≤ repaired.application.clock - entered := by
            rw [← clocks]
            exact due
          rw [environmentStep_expire_of_not_due runtime original.application event ready entered
            activated due, FinDist.mem_support_pure] at leftSupport
          rw [environmentStep_expire_of_not_due runtime repaired.application event rightReady
            entered rightActivated rightNotDue, FinDist.mem_support_pure] at rightSupport
          subst left
          subst right
          exact frame
  · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
      rw [← cuts]
      exact ready
    rw [environmentStep_expire_of_not_ready runtime original.application event ready,
      FinDist.mem_support_pure] at leftSupport
    rw [environmentStep_expire_of_not_ready runtime repaired.application event rightNotReady,
      FinDist.mem_support_pure] at rightSupport
    subst left
    subst right
    exact frame

/-- Actual expiry preserves the complete joint frame whenever the addressed
event has no private override. No readiness, completion or timing premise is
needed: all real stuttering and due branches are included. -/
theorem expiry_unmodified
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId)
    (noValue : memory.shadow.values (.inr event) = none)
    (noAction : memory.shadow.actions event = none)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftSupport : left ∈ (original.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support)
    (rightSupport : right ∈ (repaired.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support) :
    Frame runtime leaks memory owner left right := by
  let app := runtime.reactiveApplication leaks
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_comp]
    at leftSupport rightSupport
  obtain ⟨leftState, leftMoved, rfl⟩ := FinDist.support_map .. ▸ leftSupport
  obtain ⟨rightState, rightMoved, rfl⟩ := FinDist.support_map .. ▸ rightSupport
  have next := frame.expiry_application_frame event noValue noAction leftState rightState
    leftMoved rightMoved
  exact { next with
    service := by
      change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
      rw [frame.service, frame.environment] }

/-- Public event expiry cannot reveal a repaired hidden binding. -/
theorem expiry_public
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : graph.EventId) (visible : (graph.outputLayout event).IsPublic)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftSupport : left ∈ (original.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support)
    (rightSupport : right ∈ (repaired.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support) :
    Frame runtime leaks memory owner left right :=
  frame.expiry_unmodified event (onlyBindings.public_value_none (.inr event) visible)
    (onlyBindings.public_action_none event visible) left right leftSupport rightSupport

/-- The entire existing padding/expiry service suffix preserves the frame,
including legal withholding that completes only at the deadline. -/
theorem clock_tail_unmodified
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId)
    (noValue : memory.shadow.values (.inr event) = none)
    (noAction : memory.shadow.actions event = none)
    (ticks : Nat) (left right : (runtime.reactiveApplication leaks).Execution)
    (leftSupport : left ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]) original).support)
    (rightSupport : right ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]) repaired).support) :
    Frame runtime leaks memory owner left right := by
  let app := runtime.reactiveApplication leaks
  induction ticks generalizing original repaired with
  | zero =>
      have expireLaw (execution : app.Execution) :
          runtime.runInteractionPlan leaks players network [.expire event] execution =
            execution.environmentStep app (.application (.expire event)) := by
        simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
          FinDist.bind_pure]
        change (execution.environmentStep app (.application (.expire event))).bind FinDist.pure = _
        exact FinDist.bind_pure _
      exact frame.expiry_unmodified event noValue noAction left right
        ((expireLaw original) ▸ leftSupport) ((expireLaw repaired) ▸ rightSupport)
  | succ ticks ih =>
      let advance (execution : app.Execution) : app.Execution :=
        { execution with
          application := { execution.application with clock := execution.application.clock + 1 }
          environmentRecall := execution.environmentRecall ++
            [⟨execution.observeEnvironment app, .application .advanceClock⟩] }
      have tickLaw (execution : app.Execution) :
          runtime.interactionStep leaks players network .tick execution =
            FinDist.pure (advance execution) := by
        simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
        change (execution.environmentStep app (.application .advanceClock)).bind FinDist.pure = _
        rw [FinDist.bind_pure]
        change ((FinDist.pure { execution.application with
          clock := execution.application.clock + 1 }).map _).map _ = _
        rw [FinDist.map_pure, FinDist.map_pure]
      rw [List.replicate_succ, List.cons_append, runInteractionPlan, tickLaw,
        FinDist.pure_bind] at leftSupport rightSupport
      exact ih frame.advanceClock leftSupport rightSupport

/-- The two actual public-event service tails have a joint law on complete
frames. No successful publication or early completion premise is needed. -/
theorem public_clock_tail_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId)
    (visible : (graph.outputLayout event).IsPublic) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : FinDist (app.Execution × app.Execution),
      coupling.map Prod.fst = runtime.runInteractionPlan leaks players network
        (List.replicate ticks .tick ++ [.expire event]) original ∧
      coupling.map Prod.snd = runtime.runInteractionPlan leaks players network
        (List.replicate ticks .tick ++ [.expire event]) repaired ∧
      ∀ next ∈ coupling.support, Frame runtime leaks memory owner next.1 next.2 := by
  intro app
  let left := runtime.runInteractionPlan leaks players network
    (List.replicate ticks .tick ++ [.expire event]) original
  let right := runtime.runInteractionPlan leaks players network
    (List.replicate ticks .tick ++ [.expire event]) repaired
  refine ⟨FinDist.product left right, FinDist.map_fst_product ..,
    FinDist.map_snd_product .., ?_⟩
  intro next supported
  have first : next.1 ∈ left.support := by
    rw [← FinDist.map_fst_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  have second : next.2 ∈ right.support := by
    rw [← FinDist.map_snd_product left right, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  exact frame.clock_tail_unmodified players network event
    (onlyBindings.public_value_none (.inr event) visible)
    (onlyBindings.public_action_none event visible) ticks next.1 next.2 first second

end Vegas.EventGraphRuntime.BindingMemory.Frame
