module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.NormalizedPolicy
public import Vegas.EventGraph.PolicyCongruence

@[expose] public section

/-! # Normalization is invisible on totally ordered graphs

When every earlier event is a dependency, each step completes the least
unfinished event, so every reachable history lists its events in rank order.
Normalizing a profile then changes no observation it acts on, and its
canonical run is unchanged.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem map_val_finRange (count : Nat) :
    (List.finRange count).map Fin.val = List.range count := by
  apply List.ext_getElem <;> simp

private theorem range_filter_lt (count bound : Nat) :
    (List.range count).filter (fun value => decide (value < bound)) =
      List.range (min count bound) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.filter_append, ih]
      by_cases below : count < bound
      · rw [min_eq_left (by omega : count ≤ bound), min_eq_left (by omega : count + 1 ≤ bound),
          List.range_succ]
        simp [below]
      · rw [min_eq_right (by omega : bound ≤ count), min_eq_right (by omega : bound ≤ count + 1)]
        simp [below]

omit [DecidableEq Player] in
/-- A list of events whose values are an initial range is in rank order. -/
theorem rankSort_of_map_val_eq_range (events : List graph.EventId) (length : Nat)
    (initial : events.map Fin.val = List.range length) :
    graph.rankSort events = events := by
  have bounded : length ≤ graph.order.eventCount := by
    by_contra over
    have inside : graph.order.eventCount ∈ List.range length := List.mem_range.mpr (by omega)
    rw [← initial] at inside
    obtain ⟨event, _, same⟩ := List.mem_map.mp inside
    have := event.isLt
    omega
  have member (event : graph.EventId) : event ∈ events ↔ event.val < length := by
    rw [← List.mem_range, ← initial, List.mem_map]
    constructor
    · intro inside; exact ⟨event, inside, rfl⟩
    · rintro ⟨other, inside, same⟩
      rwa [← Fin.ext same]
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [initial]
  unfold rankSort
  have filtered : (List.finRange graph.order.eventCount).filter (fun event => event ∈ events) =
      (List.finRange graph.order.eventCount).filter
        ((fun value => decide (value < length)) ∘ Fin.val) :=
    List.filter_congr fun event _ => by simp [member]
  rw [filtered, ← List.filter_map, map_val_finRange, range_filter_lt, min_eq_right bounded]

/-- On a totally ordered graph every reachable history lists the events `0, 1, …`. -/
theorem history_map_val_of_reachable
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event)
    {inputs : graph.Inputs} {config : graph.Config} (reach : Config.Reachable inputs config) :
    config.history.map (fun completion => completion.event.val) =
      List.range config.history.length := by
  induction reach with
  | initial => simp [Config.initial]
  | @step before _ event ready action next member ih =>
      obtain ⟨value, _, history⟩ := Config.step_completion _ event ready action next member
      have completedIff (other : graph.EventId) :
          other ∈ before.cut.completed ↔ other.val < before.history.length := by
        rw [← before.history_exact, ← List.mem_range, ← ih, List.mem_map, List.mem_map]
        constructor
        · rintro ⟨completion, inside, rfl⟩; exact ⟨completion, inside, rfl⟩
        · rintro ⟨completion, inside, same⟩; exact ⟨completion, inside, Fin.ext same⟩
      have notBefore : ¬ event.val < before.history.length :=
        fun earlier => ready.1 ((completedIff event).mpr earlier)
      have notAfter : ¬ before.history.length < event.val := by
        intro later
        let gap : graph.EventId := ⟨before.history.length, by have := event.isLt; omega⟩
        have completed := ready.2 (total gap event later)
        exact absurd ((completedIff gap).mp completed) (lt_irrefl _)
      have exact : event.val = before.history.length := by omega
      rw [history]
      simp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
        List.length_singleton, EventGraph.completion, ih, exact, List.range_succ]

/-- On a totally ordered graph every reachable history is in rank order. -/
theorem rankSort_history_of_reachable
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event)
    {inputs : graph.Inputs} {config : graph.Config} (reach : Config.Reachable inputs config) :
    graph.rankSort (config.history.map EventCompletion.event) =
      config.history.map EventCompletion.event :=
  rankSort_of_map_val_eq_range _ config.history.length (by
    rw [List.map_map]
    exact history_map_val_of_reachable total reach)

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- On a totally ordered graph normalization leaves every canonical run unchanged. -/
theorem runPolicies_canonical_normalizeProfile
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event)
    (profile : graph.BehavioralProfile) (inputs : graph.Inputs) :
    graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) inputs =
      graph.runPolicies graph.canonicalScheduler profile inputs := by
  apply runPolicies_canonical_eq_of_reachable
  intro config reach _ _ event _ _ who actor active
  exact policy_congr (profile who) event actor
    (graph.normalizeObservation_playerObserve_of_rankOrdered who config
      (rankSort_history_of_reachable total reach)) _ _

end Vegas.EventGraph
