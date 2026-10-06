/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Semantics
import Mathlib.Data.List.Sort

/-! # Canonical execution order

Choosing the least ready event executes every event in numeric order. This is
a property of one scheduler of the shared executor, not an equivalence between
arbitrary asynchronous policies.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type}
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Completed events precede every unfinished event and occur in rank order. -/
def RankPrefix (config : graph.Config) : Prop :=
  (∀ done ∈ config.cut.completed, ∀ missing, missing ∉ config.cut.completed →
    done.val < missing.val) ∧
  (config.history.map Completion.event).Pairwise fun left right => left.val < right.val

theorem rankPrefix_initial (inputs : graph.Inputs) :
    RankPrefix (Config.initial inputs) := by
  simp [RankPrefix, Config.initial, EventOrder.Cut.empty]

/-- The completions of a configuration sorted by source rank, whatever order
they completed in. -/
def Config.rankedHistory (config : graph.Config) : List graph.Completion :=
  config.history.mergeSort fun left right => decide (left.event.val ≤ right.event.val)

/-- Sorting by rank only reorders the completions. -/
theorem Config.rankedHistory_perm (config : graph.Config) :
    config.rankedHistory.Perm config.history :=
  List.mergeSort_perm _ _

/-- The ranked completions follow source rank. -/
theorem Config.rankedHistory_pairwise (config : graph.Config) :
    config.rankedHistory.Pairwise fun left right => left.event.val ≤ right.event.val := by
  have sorted := List.pairwise_mergeSort
    (le := fun left right : graph.Completion => decide (left.event.val ≤ right.event.val))
    (fun _ _ _ first second => by simp only [decide_eq_true_eq] at *; omega)
    (fun first second => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega) config.history
  exact sorted.imp fun related => of_decide_eq_true related

/-- A configuration whose completions already follow source rank is its own
ranked history. -/
theorem RankPrefix.rankedHistory_eq {config : graph.Config} (ranked : RankPrefix config) :
    config.rankedHistory = config.history := by
  have strict : config.history.Pairwise fun left right => left.event.val < right.event.val :=
    (List.pairwise_map (R := fun left right : graph.EventId => left.val < right.val)).mp
      ranked.2
  have distinct : config.history.Pairwise fun left right => left.event.val ≠ right.event.val :=
    strict.imp Nat.ne_of_lt
  have : Std.Symm fun left right : graph.Completion => left.event.val ≠ right.event.val :=
    ⟨fun _ _ different same => different same.symm⟩
  apply List.Perm.eq_of_pairwise (le := fun left right => left.event.val ≤ right.event.val)
  · intro left right leftMem rightMem below above
    by_contra different
    exact distinct.forall (config.rankedHistory_perm.subset leftMem) rightMem different
      (Nat.le_antisymm below above)
  · exact config.rankedHistory_pairwise
  · exact strict.imp Nat.le_of_lt
  · exact config.rankedHistory_perm

theorem rankPrefix_step {config next : graph.Config}
    (ordered : RankPrefix config) (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (member : next ∈ (config.step event ready action).support) : RankPrefix next := by
  constructor
  · rw [config.step_cut event ready action next member]
    intro done doneMem missing missingNotMem
    have missingBefore : missing ∉ config.cut.completed := by
      intro oldMem
      exact missingNotMem (Finset.mem_insert_of_mem oldMem)
    rw [EventOrder.Cut.mem_complete] at doneMem
    rcases doneMem with rfl | doneBefore
    · have weak := least missing missingBefore
      have different : done ≠ missing := by
        intro same
        subst missing
        exact missingNotMem (Finset.mem_insert_self _ _)
      have differentVal : done.val ≠ missing.val := fun same => different (Fin.ext same)
      omega
    · exact ordered.1 done doneBefore missing missingBefore
  · rw [config.step_history event ready action next member, List.map_append]
    simp only [List.map_cons, List.map_nil, List.pairwise_append]
    refine ⟨ordered.2, by simp, ?_⟩
    intro prior priorMem last lastMem
    have lastEq : last = event := by simpa using lastMem
    subst last
    exact ordered.1 prior ((config.history_exact prior).mp priorMem) event ready.1

private theorem runPlan_rankPrefix (plan : graph.EventPlan)
    (least : ∀ config notTerminal choice, choice ∈ (plan config notTerminal).support →
      ∀ other, other ∉ config.cut.completed → choice.1.1.val ≤ other.val) :
    ∀ fuel config next, RankPrefix config →
      next ∈ (graph.runPlan plan fuel config).support → RankPrefix next := by
  intro fuel
  induction fuel with
  | zero =>
      intro config next ordered member
      have same : next = config := by simpa [runPlan] using member
      exact same ▸ ordered
  | succ fuel ih =>
      intro config next ordered member
      by_cases terminal : config.cut.Terminal
      · have same : next = config := by simpa [runPlan, terminal] using member
        exact same ▸ ordered
      · rw [runPlan, dite_eq_right terminal, PMF.support_bind] at member
        simp only [Set.mem_iUnion] at member
        obtain ⟨choice, choiceMem, restMem⟩ := member
        rw [PMF.support_bind] at restMem
        simp only [Set.mem_iUnion] at restMem
        obtain ⟨intermediate, intermediateMem, nextMem⟩ := restMem
        exact ih intermediate next
          (rankPrefix_step ordered choice.1.1 choice.1.2 choice.2
            (least config terminal choice choiceMem) intermediateMem) nextMem

variable [DecidableEq Player]

theorem canonical_policyPlan_least (profile : graph.BehavioralProfile)
    (config : graph.Config) (notTerminal : ¬ config.cut.Terminal)
    (choice : Σ selected : {event : graph.EventId // config.cut.Ready event},
      graph.Action selected.1)
    (member : choice ∈ (graph.policyPlan profile graph.canonicalScheduler
      config notTerminal).support) :
    ∀ other, other ∉ config.cut.completed → choice.1.1.val ≤ other.val := by
  have selectedEq : choice.1.1 =
      config.cut.enabled.min' (enabled_nonempty_of_not_terminal config notTerminal) := by
    unfold policyPlan canonicalScheduler at member
    simp only [PMF.pure_bind] at member
    split at member
    · rw [PMF.support_map] at member
      obtain ⟨action, _, rfl⟩ := member
      rfl
    · have same := (PMF.mem_support_pure_iff _ _).mp member
      subst choice
      rfl
  intro other unfinished
  rw [selectedEq]
  exact (canonical_min_ready_is_least_unfinished config.cut notTerminal).2 other unfinished

/-- Every supported complete execution under the canonical scheduler has the
source-ranked chronological event list, for arbitrary behavioral player policies
and initial values. The actions and terminal values remain policy-dependent. -/
theorem runPolicies_canonical_history (profile : graph.BehavioralProfile)
    (inputs : graph.Inputs) (next : graph.Config)
    (member : next ∈ (graph.runPolicies graph.canonicalScheduler profile inputs).support) :
    next.history.map Completion.event = List.finRange graph.order.eventCount := by
  have ordered : RankPrefix next :=
    runPlan_rankPrefix (graph.policyPlan profile graph.canonicalScheduler)
      (canonical_policyPlan_least profile) graph.order.eventCount (Config.initial inputs)
      next (rankPrefix_initial inputs) member
  have terminal := graph.runPolicies_terminal graph.canonicalScheduler profile inputs next member
  apply ordered.2.eq_of_mem_iff (List.sortedLT_finRange graph.order.eventCount).pairwise
  intro event
  rw [next.history_exact, terminal]
  simp

end Vegas.EventGraph
