/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingRejectedInclusion
import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.EventBindingInvariant

/-! # Binding expiry in histories without an omission -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : ((reactiveApplication timeouts) leaks).Execution}

/-- A real binding-expiry command in an omission-free prefix stutters jointly.
Due expiry of a ready binding would create a completed event without an
accepted handle, so that branch is excluded by the actual public endpoint. -/
theorem binding_expiry (frame : Frame timeouts leaks memory owner original repaired)
    (clear : original.application.config.defaulted = ∅)
    (valid : original.application.BindingInvariant)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (nextOriginal nextRepaired : ((reactiveApplication timeouts) leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.expire event))).support)
    (right : nextRepaired ∈ (repaired.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.expire event))).support)
    (notMissed : nextOriginal.application.publicView.missedBinding event = false) :
    Frame timeouts leaks memory owner nextOriginal nextRepaired := by
  let app := (reactiveApplication timeouts) leaks
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at left right
  obtain ⟨first, firstMoved, rfl⟩ := PMF.support_map .. ▸ left
  obtain ⟨second, secondMoved, rfl⟩ := PMF.support_map .. ▸ right
  change first ∈ ((environmentStep timeouts original.application (.expire event)).map
    State.drain).support at firstMoved
  change second ∈ ((environmentStep timeouts repaired.application (.expire event)).map
    State.drain).support at secondMoved
  obtain ⟨firstNative, firstRawMoved, rfl⟩ := PMF.support_map .. ▸ firstMoved
  obtain ⟨secondNative, secondRawMoved, rfl⟩ := PMF.support_map .. ▸ secondMoved
  change firstNative.drain.publicView.missedBinding event = false at notMissed
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have activations : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  have laws : environmentStep timeouts original.application (.expire event) =
        PMF.pure original.application ∧
      environmentStep timeouts repaired.application (.expire event) =
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
          exact ⟨environmentStep_expire_of_not_activated timeouts original.application event ready
            activated, environmentStep_expire_of_not_activated timeouts repaired.application event
              rightReady rightActivated⟩
      | some entered =>
          have rightActivated : repaired.application.activatedAt event = some entered := by
            rw [← activations]
            exact activated
          by_cases due : timeouts.duration event ≤ original.application.clock - entered
          · have absent : original.application.accepted (.inr event) = none := by
              cases found : original.application.accepted (.inr event) with
              | none => rfl
              | some candidate =>
                  exact False.elim (ready.1 (valid.accepted_complete event candidate found))
            have missed := (missedBinding_expire timeouts) original.application firstNative event
              ready
              entered activated due actor payload outputEq codeEq node absent firstRawMoved
            obtain ⟨completed, unaccepted⟩ :=
              (State.publicView_missedBinding firstNative event actor payload outputEq).mp missed
            have afterMissed : firstNative.drain.publicView.missedBinding event = true :=
              (State.publicView_missedBinding firstNative.drain event actor payload outputEq).mpr
                ⟨Config.Step.path_completed_mono firstNative.drain_graph_steps completed,
                  by rw [(firstNative.drain_tables).1]; exact unaccepted⟩
            rw [notMissed] at afterMissed
            cases afterMissed
          · have rightNotDue : ¬ timeouts.duration event ≤ repaired.application.clock - entered
              := by
              rwa [← clocks]
            exact ⟨environmentStep_expire_of_not_due timeouts original.application event ready
              entered activated due, environmentStep_expire_of_not_due timeouts repaired.application
                event rightReady entered rightActivated rightNotDue⟩
    · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
        rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
        exact ready
      exact ⟨environmentStep_expire_of_not_ready timeouts original.application event ready,
        environmentStep_expire_of_not_ready timeouts repaired.application event rightNotReady⟩
  rw [laws.1, PMF.mem_support_pure_iff _ _] at firstRawMoved
  rw [laws.2, PMF.mem_support_pure_iff _ _] at secondRawMoved
  subst firstNative
  subst secondNative
  have rightClear : repaired.application.config.defaulted = ∅ :=
    (congrArg (fun view : PublicView graph => view.observation.defaulted)
      frame.publicView).symm.trans clear
  rw [original.application.drain_eq_of_empty clear,
    repaired.application.drain_eq_of_empty rightClear]
  exact frame.recordEnvironment (.application (.expire event))

end Vegas.EventGraphRuntime.BindingMemory.Frame
