/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.CanonicalStep

/-! # Reachable-policy congruence for canonical execution

Only kernels at the selected source rank matter. Policies may differ on
unreachable observations and at events not currently selected.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Agreement at reachable canonical decisions suffices for equality of the
complete configuration law. No source syntax or information restriction is
needed for this executor congruence. -/
theorem runPolicies_canonical_eq_of_reachable
    (left right : graph.BehavioralProfile) (inputs : graph.Inputs)
    (kernels : ∀ (config : graph.Config), config.Reachable inputs →
      ∀ (offset : Nat), config.cut.IsPrefix offset →
      ∀ (event : graph.EventId), config.cut.Ready event → event.val = offset →
      ∀ (who : Player) (actor : graph.actor? event = some who),
        left who event actor (graph.playerObserve who config) =
          right who event actor (graph.playerObserve who config)) :
    graph.runPolicies graph.canonicalScheduler left inputs =
      graph.runPolicies graph.canonicalScheduler right inputs := by
  have continuation : ∀ fuel (config : graph.Config), config.Reachable inputs →
      ∀ offset, config.cut.IsPrefix offset →
        graph.runPlan (graph.policyPlan left graph.canonicalScheduler) fuel config =
          graph.runPlan (graph.policyPlan right graph.canonicalScheduler) fuel config := by
    intro fuel
    induction fuel with
    | zero => intro config reachable offset ordered; rfl
    | succ fuel ih =>
        intro config reachable offset ordered
        by_cases terminal : config.cut.Terminal
        · simp only [runPlan, dif_pos terminal]
        · have active : offset < graph.order.eventCount := by
            have bound := ordered.1
            have different : offset ≠ graph.order.eventCount := by
              intro same
              exact terminal (same ▸ ordered).terminal
            omega
          let event : graph.EventId := ⟨offset, active⟩
          have ready : config.cut.Ready event := ordered.ready active
          have least : ∀ other, other ∉ config.cut.completed →
              event.val ≤ other.val := by
            intro other unfinished
            have notBefore : ¬ other.val < offset := by
              simpa only [ordered.2 other] using unfinished
            exact Nat.le_of_not_gt notBefore
          have tails : ∀ (action : graph.Action event) next,
              next ∈ (config.step event ready action).support →
              graph.runPlan (graph.policyPlan left graph.canonicalScheduler) fuel next =
                graph.runPlan (graph.policyPlan right graph.canonicalScheduler) fuel next := by
            intro action next member
            apply ih next (.step reachable event ready action next member) (offset + 1)
            rw [config.step_cut event ready action next member]
            exact ordered.complete active
          cases actor : graph.actor? event with
          | none =>
              rw [runPlan_canonical_ownerless left fuel config event ready least actor,
                runPlan_canonical_ownerless right fuel config event ready least actor]
              apply FinDist.bind_congr
              exact tails _
          | some who =>
              rw [runPlan_canonical_actor left fuel config event ready least who actor,
                runPlan_canonical_actor right fuel config event ready least who actor,
                kernels config reachable offset ordered event ready rfl who actor]
              apply FinDist.bind_congr
              intro action _
              apply FinDist.bind_congr
              exact tails action
  exact continuation graph.order.eventCount (Config.initial inputs) .initial 0
    (EventOrder.Cut.empty_isPrefix graph.order)

end Vegas.EventGraph
