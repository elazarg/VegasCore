/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSampleReplay

/-! # Clear actual expiry under equal public observations -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryState

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}

/-- If the actual raw expiry result is clear, no due strategic event was
consumed. The same public readiness, stamps and clock force both native expiry
laws to stutter, independently of all hidden binding results. -/
theorem expiry_native_stutter (original repaired : RecoveryState graph)
    (publics : original.native.publicView = repaired.native.publicView)
    (event : graph.EventId) (native : State graph)
    (supported : native ∈ (environmentStep runtime original.native
      (.expire event)).support)
    (clear : (original.environmentResult (.expire event) native).excluded = ∅) :
    environmentStep runtime original.native (.expire event) =
        PMF.pure original.native ∧
      environmentStep runtime repaired.native (.expire event) =
        PMF.pure repaired.native := by
  have clocks : original.native.clock =
      repaired.native.clock := congrArg PublicView.clock publics
  have stamps : original.native.activatedAt =
      repaired.native.activatedAt := congrArg PublicView.activatedAt publics
  by_cases ready : original.native.config.cut.Ready event
  · have rightReady : repaired.native.config.cut.Ready event := by
      rw [← State.publicView_eventReady, ← publics, State.publicView_eventReady]
      exact ready
    cases activated : original.native.activatedAt event with
    | none =>
        have rightActivated : repaired.native.activatedAt event = none := by
          rw [← stamps]; exact activated
        exact ⟨environmentStep_expire_of_not_activated runtime _ event ready activated,
          environmentStep_expire_of_not_activated runtime _ event rightReady rightActivated⟩
    | some entered =>
        have rightActivated : repaired.native.activatedAt event =
            some entered := (congrFun stamps event).symm.trans activated
        by_cases due : runtime.deadline event ≤ original.native.clock - entered
        · have rightDue : runtime.deadline event ≤
              repaired.native.clock - entered := clocks ▸ due
          have noStrategic (actor : Player) (acting : graph.actor? event = some actor)
              (completed : event ∈ native.config.cut.completed) : False := by
            have excluded : (original.environmentResult (.expire event)
                native).excluded = insert actor original.excluded := by
              simp only [RecoveryState.environmentResult]
              split
              · simp only [RecoveryState.excludeEvent, acting]
              · rename_i impossible
                exact (impossible ⟨ready.1, completed⟩).elim
            have member : actor ∈
                (original.environmentResult (.expire event)
                  native).excluded := by
              rw [excluded]
              exact Finset.mem_insert_self _ _
            simp only [clear, Finset.notMem_empty] at member
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq =>
              exact ⟨environmentStep_expire_sample_eq runtime _ event ready entered activated due
                payload law outputEq codeEq node,
                environmentStep_expire_sample_eq runtime _ event rightReady entered rightActivated
                  rightDue payload law outputEq codeEq node⟩
          | bind actor payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq runtime _ event ready entered activated due
                actor payload outputEq codeEq node, PMF.mem_support_pure_iff] at supported
              subst native
              have acting : graph.actor? event = some actor :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                  (congrArg EventCode.actor codeEq)
              exact (noStrategic actor acting (by
                change event ∈ (original.native.config.cut.complete
                  event ready).completed
                rw [EventOrder.Cut.mem_complete]
                exact Or.inl rfl)).elim
          | resolve actor payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq runtime _ event ready entered activated due
                actor payload binding checks outputEq codeEq node,
                PMF.mem_support_pure_iff] at supported
              subst native
              have acting : graph.actor? event = some actor :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                  (congrArg EventCode.actor codeEq)
              exact (noStrategic actor acting (by
                change event ∈ (original.native.config.cut.complete
                  event ready).completed
                rw [EventOrder.Cut.mem_complete]
                exact Or.inl rfl)).elim
        · have rightDue : ¬ runtime.deadline event ≤
              repaired.native.clock - entered := by rwa [← clocks]
          exact ⟨environmentStep_expire_of_not_due runtime _ event ready entered activated due,
            environmentStep_expire_of_not_due runtime _ event rightReady entered rightActivated
              rightDue⟩
  · have rightReady : ¬ repaired.native.config.cut.Ready event := by
      rw [← State.publicView_eventReady, ← publics, State.publicView_eventReady]
      exact ready
    exact ⟨environmentStep_expire_of_not_ready runtime _ event ready,
      environmentStep_expire_of_not_ready runtime _ event rightReady⟩

end Vegas.EventGraphRuntime.RecoveryState
