/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.SuffixExclusionRecord
import Vegas.Pending.ReactiveFrontierEnvironment

/-! # Expiry preserves a retained frontier when public failure is impossible -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Any expiry that changes the graph configuration produces an owned public
failure. Sample events never expire. -/
theorem environmentStep_expire_config_eq_of_no_publicFailure
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (valid : state.ReceiptsComplete) (event : graph.EventId)
    (supported : next ∈ (environmentStep runtime state (.expire event)).support)
    (noFailure : ∀ owner, graph.actor? event = some owner → ¬next.PublicFailure event) :
    next.config = state.config := by
  by_contra changed
  obtain same | ⟨ready, _action, _step⟩ :=
    environmentStep_expire_config_eq_or_mem_step runtime state next event supported
  · exact changed same
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      cases activated : state.activatedAt event with
      | none =>
          rw [environmentStep_expire_of_not_activated runtime state event ready activated,
            PMF.mem_support_pure_iff] at supported
          exact changed (congrArg State.config supported)
      | some entered =>
          by_cases due : runtime.deadline event ≤ state.clock - entered
          · rw [environmentStep_expire_sample_eq runtime state event ready entered activated due
              payload law outputEq codeEq node, PMF.mem_support_pure_iff] at supported
            exact changed (congrArg State.config supported)
          · rw [environmentStep_expire_of_not_due runtime state event ready entered activated due,
              PMF.mem_support_pure_iff] at supported
            exact changed (congrArg State.config supported)
  | bind owner payload outputEq codeEq =>
      have acting : graph.actor? event = some owner :=
        (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
      exact noFailure owner acting (SuffixExclusionRecord.expire_publicFailure runtime state next
        valid event supported changed acting)
  | resolve owner payload binding checks outputEq codeEq =>
      have acting : graph.actor? event = some owner :=
        (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
      exact noFailure owner acting (SuffixExclusionRecord.expire_publicFailure runtime state next
        valid event supported changed acting)

/-- A supported expiry with no possible new public failure preserves the same
sampled semantic frontier and the complete private-memory profile. -/
theorem ReactiveFrontier.expire_of_no_publicFailure (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks execution memories frontier)
    (valid : execution.application.ReceiptsComplete) (event : graph.EventId)
    (supported : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support)
    (noFailure : ∀ owner, graph.actor? event = some owner →
      ¬next.application.PublicFailure event) :
    runtime.ReactiveFrontier leaks next memories frontier := by
  obtain ⟨updated, updatedSupported, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨native, nativeSupported, rfl⟩ := PMF.support_map .. ▸ updatedSupported
  have same := environmentStep_expire_config_eq_of_no_publicFailure runtime execution.application
    native valid event nativeSupported noFailure
  exact related.congr_execution runtime leaks _ _ memories frontier same.symm rfl rfl

end Vegas.EventGraphRuntime
