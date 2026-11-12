module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingFrameStep

@[expose] public section

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
  {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : ((reactiveApplication timeouts) leaks).Execution}

private theorem expiry_application_frame
    (frame : Frame timeouts leaks memory owner original repaired)
    (event : graph.EventId)
    (noValue : memory.shadow.values (.inr event) = none)
    (noAction : memory.shadow.actions event = none)
    (left right : State graph)
    (leftSupport : left ∈ (environmentStep timeouts original.application (.expire event)).support)
    (rightSupport : right ∈
      (environmentStep timeouts repaired.application (.expire event)).support) :
    Frame timeouts leaks memory owner { original with application := left }
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
        rw [environmentStep_expire_of_not_activated timeouts original.application event ready
          activated, PMF.mem_support_pure_iff _ _] at leftSupport
        rw [environmentStep_expire_of_not_activated timeouts repaired.application event rightReady
          rightActivated, PMF.mem_support_pure_iff _ _] at rightSupport
        subst left
        subst right
        exact frame
    | some entered =>
        have rightActivated : repaired.application.activatedAt event = some entered := by
          rw [← activations]
          exact activated
        by_cases due : timeouts.duration event ≤ original.application.clock - entered
        · have rightDue : timeouts.duration event ≤ repaired.application.clock - entered := by
            rw [← clocks]
            exact due
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq timeouts original.application event ready entered
                activated due payload law outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at leftSupport
              rw [environmentStep_expire_sample_eq timeouts repaired.application event rightReady
                entered rightActivated rightDue payload law outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at rightSupport
              subst left
              subst right
              exact frame
          | bind actor payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq timeouts original.application event ready entered
                activated due actor payload outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at leftSupport
              rw [environmentStep_expire_bind_eq timeouts repaired.application event rightReady
                entered rightActivated rightDue actor payload outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at rightSupport
              subst left
              subst right
              exact frame.complete_unmodified event ready rightReady noValue noAction _ _
          | resolve actor payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq timeouts original.application event ready
                entered
                activated due actor payload binding checks outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at leftSupport
              rw [environmentStep_expire_resolve_eq timeouts repaired.application event rightReady
                entered rightActivated rightDue actor payload binding checks outputEq codeEq node,
                  PMF.mem_support_pure_iff _ _] at rightSupport
              subst left
              subst right
              exact frame.complete_unmodified event ready rightReady noValue noAction _ _
        · have rightNotDue : ¬ timeouts.duration event ≤ repaired.application.clock - entered := by
            rw [← clocks]
            exact due
          rw [environmentStep_expire_of_not_due timeouts original.application event ready entered
            activated due, PMF.mem_support_pure_iff _ _] at leftSupport
          rw [environmentStep_expire_of_not_due timeouts repaired.application event rightReady
            entered rightActivated rightNotDue, PMF.mem_support_pure_iff _ _] at rightSupport
          subst left
          subst right
          exact frame
  · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
      rw [← cuts]
      exact ready
    rw [environmentStep_expire_of_not_ready timeouts original.application event ready,
      PMF.mem_support_pure_iff _ _] at leftSupport
    rw [environmentStep_expire_of_not_ready timeouts repaired.application event rightNotReady,
      PMF.mem_support_pure_iff _ _] at rightSupport
    subst left
    subst right
    exact frame

/-- Expiry ending without public default preserves the complete joint frame
when the addressed event has no private override. The clear endpoint makes
automatic completion inert on both sides. -/
theorem expiry_unmodified
    (frame : Frame timeouts leaks memory owner original repaired)
    (event : graph.EventId)
    (noValue : memory.shadow.values (.inr event) = none)
    (noAction : memory.shadow.actions event = none)
    (left right : ((reactiveApplication timeouts) leaks).Execution)
    (leftSupport : left ∈ (original.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.expire event))).support)
    (endpointClear : left.application.config.defaulted = ∅)
    (rightSupport : right ∈ (repaired.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.expire event))).support) :
    Frame timeouts leaks memory owner left right := by
  let app := (reactiveApplication timeouts) leaks
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    at leftSupport rightSupport
  obtain ⟨leftState, leftMoved, rfl⟩ := PMF.support_map .. ▸ leftSupport
  obtain ⟨rightState, rightMoved, rfl⟩ := PMF.support_map .. ▸ rightSupport
  change leftState ∈ ((environmentStep timeouts original.application (.expire event)).map
    State.drain).support at leftMoved
  change rightState ∈ ((environmentStep timeouts repaired.application (.expire event)).map
    State.drain).support at rightMoved
  obtain ⟨leftNative, leftRawMoved, rfl⟩ := PMF.support_map .. ▸ leftMoved
  obtain ⟨rightNative, rightRawMoved, rfl⟩ := PMF.support_map .. ▸ rightMoved
  change leftNative.drain.config.defaulted = ∅ at endpointClear
  have leftEmpty : leftNative.config.defaulted = ∅ :=
    (leftNative.drainFuel_defaulted leftNative.config.remaining).symm.trans endpointClear
  have next := frame.expiry_application_frame event noValue noAction leftNative rightNative
    leftRawMoved rightRawMoved
  have rightEmpty : rightNative.config.defaulted = ∅ :=
    (congrArg (fun view : PublicView graph => view.observation.defaulted)
      next.publicView).symm.trans leftEmpty
  rw [leftNative.drain_eq_of_empty leftEmpty, rightNative.drain_eq_of_empty rightEmpty]
  exact { next with
    service := by
      change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
      rw [frame.service, frame.environment] }

/-- Public event expiry cannot reveal a repaired hidden binding. -/
theorem expiry_public
    (frame : Frame timeouts leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : graph.EventId) (visible : (graph.outputLayout event).IsPublic)
    (left right : ((reactiveApplication timeouts) leaks).Execution)
    (leftSupport : left ∈ (original.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.expire event))).support)
    (endpointClear : left.application.config.defaulted = ∅)
    (rightSupport : right ∈ (repaired.environmentStep ((reactiveApplication timeouts) leaks)
      (.application (.expire event))).support) :
    Frame timeouts leaks memory owner left right :=
  frame.expiry_unmodified event (onlyBindings.public_value_none (.inr event) visible)
    (onlyBindings.public_action_none event visible) left right leftSupport endpointClear
      rightSupport

end Vegas.EventGraphRuntime.BindingMemory.Frame
