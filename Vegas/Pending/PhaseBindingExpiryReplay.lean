/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSampleReplay

/-! # Clear actual expiry cannot consume a live strategic event -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- If the actual raw expiry result is clear, no due strategic event was
consumed. The same public readiness, stamps and clock force both native expiry
laws to stutter, independently of all hidden binding results. -/
theorem expiry_native_stutter (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (native : State graph)
    (supported : native ∈ (environmentStep runtime original.application.current.native
      (.expire event)).support)
    (clear : (original.application.current.environmentResult (.expire event) native).excluded = ∅) :
    environmentStep runtime original.application.current.native (.expire event) =
        PMF.pure original.application.current.native ∧
      environmentStep runtime repaired.application.current.native (.expire event) =
        PMF.pure repaired.application.current.native := by
  have publics : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have clocks : original.application.current.native.clock =
      repaired.application.current.native.clock := congrArg PublicView.clock publics
  have stamps : original.application.current.native.activatedAt =
      repaired.application.current.native.activatedAt := congrArg PublicView.activatedAt publics
  by_cases ready : original.application.current.native.config.cut.Ready event
  · have rightReady : repaired.application.current.native.config.cut.Ready event := by
      rw [← State.publicView_eventReady, ← publics, State.publicView_eventReady]
      exact ready
    cases activated : original.application.current.native.activatedAt event with
    | none =>
        have rightActivated : repaired.application.current.native.activatedAt event = none := by
          rw [← stamps]; exact activated
        exact ⟨environmentStep_expire_of_not_activated runtime _ event ready activated,
          environmentStep_expire_of_not_activated runtime _ event rightReady rightActivated⟩
    | some entered =>
        have rightActivated : repaired.application.current.native.activatedAt event =
            some entered := (congrFun stamps event).symm.trans activated
        by_cases due : runtime.deadline event ≤ original.application.current.native.clock - entered
        · have rightDue : runtime.deadline event ≤
              repaired.application.current.native.clock - entered := clocks ▸ due
          have noStrategic (actor : Player) (acting : graph.actor? event = some actor)
              (completed : event ∈ native.config.cut.completed) : False := by
            have excluded : (original.application.current.environmentResult (.expire event)
                native).excluded = insert actor original.application.current.excluded := by
              simp only [RecoveryState.environmentResult]
              split
              · simp only [RecoveryState.excludeEvent, acting]
              · rename_i impossible
                exact (impossible ⟨ready.1, completed⟩).elim
            have member : actor ∈
                (original.application.current.environmentResult (.expire event)
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
                change event ∈ (original.application.current.native.config.cut.complete
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
                change event ∈ (original.application.current.native.config.cut.complete
                  event ready).completed
                rw [EventOrder.Cut.mem_complete]
                exact Or.inl rfl)).elim
        · have rightDue : ¬ runtime.deadline event ≤
              repaired.application.current.native.clock - entered := by rwa [← clocks]
          exact ⟨environmentStep_expire_of_not_due runtime _ event ready entered activated due,
            environmentStep_expire_of_not_due runtime _ event rightReady entered rightActivated
              rightDue⟩
  · have rightReady : ¬ repaired.application.current.native.config.cut.Ready event := by
      rw [← State.publicView_eventReady, ← publics, State.publicView_eventReady]
      exact ready
    exact ⟨environmentStep_expire_of_not_ready runtime _ event ready,
      environmentStep_expire_of_not_ready runtime _ event rightReady⟩

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
