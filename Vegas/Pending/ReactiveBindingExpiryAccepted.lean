/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRejectedInclusion
import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.EventBindingInvariant

/-! # Binding expiry in histories without an omission -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- A real binding-expiry command in an omission-free prefix stutters jointly.
Due expiry of a ready binding would create a completed event without an
accepted handle, so that branch is excluded by the actual public endpoint. -/
theorem binding_expiry (frame : Frame runtime leaks memory owner original repaired)
    (valid : original.application.BindingInvariant)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (nextOriginal nextRepaired : (runtime.reactiveApplication leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support)
    (right : nextRepaired ∈ (repaired.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support)
    (notMissed : nextOriginal.application.publicView.missedBinding event = false) :
    Frame runtime leaks memory owner nextOriginal nextRepaired := by
  let app := runtime.reactiveApplication leaks
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at left right
  obtain ⟨first, firstMoved, rfl⟩ := PMF.support_map .. ▸ left
  obtain ⟨second, secondMoved, rfl⟩ := PMF.support_map .. ▸ right
  change first ∈ (environmentStep runtime original.application (.expire event)).support
    at firstMoved
  change second ∈ (environmentStep runtime repaired.application (.expire event)).support
    at secondMoved
  change first.publicView.missedBinding event = false at notMissed
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have activations : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  have laws : environmentStep runtime original.application (.expire event) =
        PMF.pure original.application ∧
      environmentStep runtime repaired.application (.expire event) =
        PMF.pure repaired.application := by
    by_cases ready : original.application.config.cut.Ready event
    · have rightReady : repaired.application.config.cut.Ready event := by
        rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
        exact ready
      cases activated : original.application.activatedAt event with
      | none =>
          have rightActivated : repaired.application.activatedAt event = none := by
            rw [← activations]
            exact activated
          exact ⟨environmentStep_expire_of_not_activated runtime original.application event ready
            activated, environmentStep_expire_of_not_activated runtime repaired.application event
              rightReady rightActivated⟩
      | some entered =>
          have rightActivated : repaired.application.activatedAt event = some entered := by
            rw [← activations]
            exact activated
          by_cases due : runtime.deadline event ≤ original.application.clock - entered
          · have absent : original.application.accepted (.inr event) = none := by
              cases found : original.application.accepted (.inr event) with
              | none => rfl
              | some candidate =>
                  exact False.elim (ready.1 (valid.accepted_complete event candidate found))
            have missed := runtime.missedBinding_expire original.application first event ready
              entered activated due actor payload outputEq codeEq node absent firstMoved
            rw [notMissed] at missed
            cases missed
          · have rightNotDue : ¬ runtime.deadline event ≤ repaired.application.clock - entered := by
              rwa [← clocks]
            exact ⟨environmentStep_expire_of_not_due runtime original.application event ready
              entered activated due, environmentStep_expire_of_not_due runtime repaired.application
                event rightReady entered rightActivated rightNotDue⟩
    · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
        rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
        exact ready
      exact ⟨environmentStep_expire_of_not_ready runtime original.application event ready,
        environmentStep_expire_of_not_ready runtime repaired.application event rightNotReady⟩
  rw [laws.1, PMF.mem_support_pure_iff _ _] at firstMoved
  rw [laws.2, PMF.mem_support_pure_iff _ _] at secondMoved
  subst first
  subst second
  exact frame.recordEnvironment (.application (.expire event))

end Vegas.EventGraphRuntime.BindingMemory.Frame
