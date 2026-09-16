/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayEnvironment

/-! # Deadline expiry introduces no private-data-dependent observation -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Expiry is determined by public readiness and clock metadata. Its failure
completion is independent of hidden candidates and private cached actions. -/
theorem environmentStep_expire_playerView_congr
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    (left right leftNext rightNext : State graph)
    (publicEq : left.publicView = right.publicView)
    (observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config)
    (rememberedEq : (fun query => if graph.actor? query = some focal then
      left.remembered query else none) =
      fun query => if graph.actor? query = some focal then right.remembered query else none)
    (candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot))
    (leftSupported : leftNext ∈ (environmentStep runtime left (.expire event)).support)
    (rightSupported : rightNext ∈ (environmentStep runtime right (.expire event)).support) :
    leftNext.playerView focal = rightNext.playerView focal := by
  have views : left.playerView focal = right.playerView focal := by
    unfold State.playerView
    congr 1
  have cuts := cut_eq_of_completionOrder_eq left.config right.config
    (congrArg PlayerObservation.completionOrder observationEq)
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  by_cases leftReady : left.config.cut.Ready event
  · have rightReady : right.config.cut.Ready event := by rw [← cuts]; exact leftReady
    cases leftActivated : left.activatedAt event with
    | none =>
        have rightActivated : right.activatedAt event = none := by
          rw [← activatedEq]; exact leftActivated
        rw [environmentStep_expire_of_not_activated runtime left event leftReady leftActivated,
          FinDist.mem_support_pure] at leftSupported
        rw [environmentStep_expire_of_not_activated runtime right event rightReady rightActivated,
          FinDist.mem_support_pure] at rightSupported
        subst leftNext
        subst rightNext
        exact views
    | some entered =>
        have rightActivated : right.activatedAt event = some entered := by
          rw [← activatedEq]; exact leftActivated
        by_cases due : runtime.deadline event ≤ left.clock - entered
        · have rightDue : runtime.deadline event ≤ right.clock - entered := by
            rw [← clockEq]; exact due
          cases view : nodeView graph event with
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime left event leftReady entered
                leftActivated due payload law outputEq codeEq view,
                FinDist.mem_support_pure] at leftSupported
              rw [environmentStep_expire_sample_eq runtime right event rightReady entered
                rightActivated rightDue payload law outputEq codeEq view,
                FinDist.mem_support_pure] at rightSupported
              subst leftNext
              subst rightNext
              exact views
          | bind owner payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq runtime left event leftReady entered
                leftActivated due owner payload outputEq codeEq view,
                FinDist.mem_support_pure] at leftSupported
              rw [environmentStep_expire_bind_eq runtime right event rightReady entered
                rightActivated rightDue owner payload outputEq codeEq view,
                FinDist.mem_support_pure] at rightSupported
              subst leftNext
              subst rightNext
              exact State.complete_playerView_congr left right focal publicEq observationEq
                rememberedEq candidatesEq event leftReady rightReady _ _ _ _
                (fun _ => rfl) (fun _ => rfl)
          | resolve owner payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq runtime left event leftReady entered
                leftActivated due owner payload binding checks outputEq codeEq view,
                FinDist.mem_support_pure] at leftSupported
              rw [environmentStep_expire_resolve_eq runtime right event rightReady entered
                rightActivated rightDue owner payload binding checks outputEq codeEq view,
                FinDist.mem_support_pure] at rightSupported
              subst leftNext
              subst rightNext
              exact State.complete_playerView_congr left right focal publicEq observationEq
                rememberedEq candidatesEq event leftReady rightReady _ _ _ _
                (fun _ => rfl) (fun _ => rfl)
        · have rightNotDue : ¬runtime.deadline event ≤ right.clock - entered := by
            rw [← clockEq]; exact due
          rw [environmentStep_expire_of_not_due runtime left event leftReady entered leftActivated
            due, FinDist.mem_support_pure] at leftSupported
          rw [environmentStep_expire_of_not_due runtime right event rightReady entered
            rightActivated rightNotDue, FinDist.mem_support_pure] at rightSupported
          subst leftNext
          subst rightNext
          exact views
  · have rightNotReady : ¬right.config.cut.Ready event := by rw [← cuts]; exact leftReady
    rw [environmentStep_expire_of_not_ready runtime left event leftReady,
      FinDist.mem_support_pure] at leftSupported
    rw [environmentStep_expire_of_not_ready runtime right event rightNotReady,
      FinDist.mem_support_pure] at rightSupported
    subst leftNext
    subst rightNext
    exact views

/-- Expiring the same event preserves native replay without a hypothesis
about either resulting public observation. -/
theorem NativeReplay.environmentExpire
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (.expire event))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (.expire event))).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have nativeSupport (before after : runtime.application.PolicyExecution)
      (supported : after ∈ (runtime.application.environmentPolicyStep before
        (.application (.expire event))).support) :
      after.native.application ∈
        (environmentStep runtime before.native.application (.expire event)).support := by
    have native : after.native ∈
        ((runtime.application.environmentPolicyStep before
          (.application (.expire event))).map MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨after, supported, rfl⟩
    rw [runtime.application.environmentStep_native] at native
    simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
      MessageApplication.step, FinDist.support_map, Set.mem_image] at native
    obtain ⟨next, nextSupported, equal⟩ := native
    rw [← equal]
    exact nextSupported
  have views := environmentStep_expire_playerView_congr runtime focal event
    left.native.application right.native.application leftNext.native.application
    rightNext.native.application replay.publicView replay.observation replay.remembered
    replay.candidates (nativeSupport left leftNext leftSupported)
    (nativeSupport right rightNext rightSupported)
  apply replay.environmentExpire_of_result runtime focal event leftSupported rightSupported
  · exact congrArg PlayerView.publicView views
  · have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) views
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed

end Vegas.EventGraphRuntime
