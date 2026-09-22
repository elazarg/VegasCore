/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Canonical
import Vegas.EventGraph.NormalizedPolicy

/-! # Normalization is invisible in canonical execution -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A canonical-prefix configuration has exactly the rank prefix before its
least unfinished event. -/
private theorem rankPrefix_history_eq (config : graph.Config)
    (ordered : RankPrefix config) (event : graph.EventId)
    (unfinished : event ∉ config.cut.completed)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    config.history.map Completion.event = graph.rankPrefix event := by
  apply ordered.2.eq_of_mem_iff
    ((List.sortedLT_finRange graph.order.eventCount).pairwise.filter _)
  intro prior
  constructor
  · intro member
    have completed := (config.history_exact prior).mp member
    have before := ordered.1 prior completed event unfinished
    simpa [rankPrefix] using before
  · intro member
    have before : prior.val < event.val := by simpa [rankPrefix] using member
    have completed : prior ∈ config.cut.completed := by
      by_contra missing
      exact (Nat.not_lt_of_ge (least prior missing)) before
    exact (config.history_exact prior).mpr completed

private theorem canonical_policyPlan_normalize_eq
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (ordered : RankPrefix config) (notTerminal : ¬ config.cut.Terminal) :
    graph.policyPlan profile graph.canonicalScheduler config notTerminal =
      graph.policyPlan (graph.normalizeProfile profile) graph.canonicalScheduler
        config notTerminal := by
  let event := config.cut.enabled.min'
    (enabled_nonempty_of_not_terminal config notTerminal)
  have ready : config.cut.Ready event :=
    (EventOrder.Cut.mem_enabled _ _).mp
      (Finset.min'_mem _ (enabled_nonempty_of_not_terminal config notTerminal))
  have least := (canonical_min_ready_is_least_unfinished config.cut notTerminal).2
  have historyEq := rankPrefix_history_eq config ordered event ready.1 least
  unfold policyPlan canonicalScheduler normalizeProfile normalizePolicy
  simp only [FinDist.pure_bind]
  split <;> rename_i actor
  · congr 1
    apply congrArg (profile _ event actor)
    apply PlayerObservation.ext graph
    · exact historyEq
    · rfl
    · rfl
  · rfl

/-- The canonical runner has the same complete configuration law before and
after completion-order normalization. -/
theorem runPlan_canonical_normalize_eq (profile : graph.BehavioralProfile) :
    ∀ fuel config,
      RankPrefix config →
      graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel config =
        graph.runPlan (graph.policyPlan (graph.normalizeProfile profile)
          graph.canonicalScheduler) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config ordered; rfl
  | succ fuel ih =>
      intro config ordered
      by_cases terminal : config.cut.Terminal
      · simp [runPlan, terminal]
      · rw [runPlan, runPlan, dite_eq_right terminal, dite_eq_right terminal,
          canonical_policyPlan_normalize_eq profile config ordered terminal]
        apply FinDist.bind_congr
        intro choice choiceMember
        apply FinDist.bind_congr
        intro next nextMember
        apply ih
        exact rankPrefix_step ordered choice.1.1 choice.1.2 choice.2
          (canonical_policyPlan_least (graph.normalizeProfile profile)
            config terminal choice choiceMember) nextMember

/-- Canonical execution itself is insensitive to policy normalization. -/
theorem runPolicies_canonical_normalize_eq (profile : graph.BehavioralProfile)
    (inputs : graph.Inputs) :
    graph.runPolicies graph.canonicalScheduler profile inputs =
      graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) inputs := by
  exact graph.runPlan_canonical_normalize_eq profile graph.order.eventCount
    (Config.initial inputs) (rankPrefix_initial inputs)

end Vegas.EventGraph
