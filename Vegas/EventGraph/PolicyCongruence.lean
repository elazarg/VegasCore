module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CanonicalStep
public import Vegas.EventGraph.SchedulerErasure

@[expose] public section

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
      ∀ (who : Player) (actor : graph.actor? event = some who)
        (active : who ∉ config.defaulted),
        left who event actor (graph.playerObserve who config) active =
          right who event actor (graph.playerObserve who config) active) :
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
        · simp only [runPlan, dite_eq_left terminal]
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
              apply bind_congr_on_support _
              exact tails _
          | some who =>
              by_cases inactive : who ∈ config.defaulted
              · rw [runPlan_canonical_defaulted left fuel config event ready least who actor
                    inactive ((graph.nodes event).failureAction who actor),
                  runPlan_canonical_defaulted right fuel config event ready least who actor
                    inactive ((graph.nodes event).failureAction who actor)]
                apply bind_congr_on_support _
                exact tails _
              · rw [runPlan_canonical_actor left fuel config event ready least who actor inactive,
                  runPlan_canonical_actor right fuel config event ready least who actor inactive,
                  kernels config reachable offset ordered event ready rfl who actor inactive]
                apply bind_congr_on_support _
                intro action _
                apply bind_congr_on_support _
                exact tails action
  exact continuation graph.order.eventCount (Config.initial inputs) .initial 0
    (EventOrder.Cut.empty_isPrefix graph.order)


/-- Keyed action laws preserve key equality through any canonical partial run. -/
theorem runPlan_canonical_map_runKey_congr (profile : graph.BehavioralProfile)
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionDistribution profile left event = actionDistribution profile right event) :
    ∀ count (left right : graph.Config), runKey left = runKey right →
      (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count left).map
        runKey =
      (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count right).map
        runKey := by
  intro count
  induction count with
  | zero => intro left right same; simpa only [runPlan, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      intro left right same
      have cut : left.cut = right.cut := congrArg Prod.fst same
      by_cases terminal : left.cut.Terminal
      · have rightTerminal : right.cut.Terminal := by rw [← cut]; exact terminal
        simp only [runPlan, dite_eq_left terminal, dite_eq_left rightTerminal, PMF.pure_map,
          same]
      · have rightNotTerminal : ¬ right.cut.Terminal := by rw [← cut]; exact terminal
        obtain ⟨event, ready, least⟩ := exists_least_ready left terminal
        have rightReady : right.cut.Ready event := by rw [← cut]; exact ready
        have rightLeast : ∀ other, right.cut.Ready other → event ≤ other := by
          rw [← cut]
          exact least
        rw [runPlan_canonical_succ profile count left terminal event ready least,
          runPlan_canonical_succ profile count right rightNotTerminal event rightReady rightLeast,
          PMF.map_bind, PMF.map_bind]
        have sameStep : (eventStep profile left event ready).map runKey =
            (eventStep profile right event rightReady).map runKey := by
          simp only [eventStep, PMF.map_bind]
          rw [keyed same event]
          apply bind_congr_on_support _
          intro action _
          exact step_map_runKey_congr same event ready rightReady action
        exact bind_eq_of_map_key_eq runKey Set.univ _ _ (fun _ _ => Set.mem_univ _)
          (fun _ _ => Set.mem_univ _) sameStep
          (fun next => (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
            count next).map runKey) (fun a _ b _ eq => ih a b eq)

end Vegas.EventGraph

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Equal kernels on a bounded rank interval give the same complete configuration law there. -/
theorem runPlan_canonical_prefix_congr
    (left right : graph.BehavioralProfile) :
    ∀ (count start : Nat) (origin : graph.Config), origin.cut.IsPrefix start →
      start + count ≤ graph.order.eventCount →
      (∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
        ∀ who actor observation active,
          left who event actor observation active = right who event actor observation active) →
      graph.runPlan (graph.policyPlan left graph.canonicalScheduler) count origin =
        graph.runPlan (graph.policyPlan right graph.canonicalScheduler) count origin := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
      intro start origin ordered bounded same
      have active : start < graph.order.eventCount := by omega
      let event : graph.EventId := ⟨start, active⟩
      have ready : origin.cut.Ready event := ordered.ready active
      have least : ∀ other, other ∉ origin.cut.completed → event.val ≤ other.val := by
        intro other unfinished
        have notBefore : ¬ other.val < start := by
          simpa only [ordered.2 other] using unfinished
        exact Nat.le_of_not_gt notBefore
      have tails (action : graph.Action event) (next : graph.Config)
          (selected : next ∈ (origin.step event ready action).support) :
          graph.runPlan (graph.policyPlan left graph.canonicalScheduler) count next =
            graph.runPlan (graph.policyPlan right graph.canonicalScheduler) count next := by
        apply ih (start + 1) next
        · rw [origin.step_cut event ready action next selected]
          exact ordered.complete active
        · omega
        · intro query lower upper who actor observation enabled
          exact same query (by omega) (by omega) who actor observation enabled
      cases actor : graph.actor? event with
      | none =>
          rw [runPlan_canonical_ownerless left count origin event ready least actor,
            runPlan_canonical_ownerless right count origin event ready least actor]
          apply bind_congr_on_support _
          exact tails _
      | some who =>
          by_cases inactive : who ∈ origin.defaulted
          · rw [runPlan_canonical_defaulted left count origin event ready least who actor inactive
                ((graph.nodes event).failureAction who actor),
              runPlan_canonical_defaulted right count origin event ready least who actor inactive
                ((graph.nodes event).failureAction who actor)]
            apply bind_congr_on_support _
            exact tails _
          · rw [runPlan_canonical_actor left count origin event ready least who actor inactive,
              runPlan_canonical_actor right count origin event ready least who actor inactive,
              same event (by rfl) (by dsimp only [event]; omega) who actor
                (graph.playerObserve who origin) inactive]
            apply bind_congr_on_support _
            intro action _
            apply bind_congr_on_support _
            exact tails action

end Vegas.EventGraph
