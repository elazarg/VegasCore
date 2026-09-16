/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPolicyTrace

/-! # Continuing from a stopped native prefix

The complete policy state retains exactly the histories used by subsequent
invocations. Selecting a prefix therefore leaves the original continuation
kernel: run the unused invocation suffix from its final snapshot. This is an
identity of the joint prefix/final-state law, not just a support decomposition.
No independence between the prefix and the continuation is assumed.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} {app : MessageApplication Principal}

/-- Number of invocations recorded after the initial snapshot. -/
def PolicyTrace.length : app.PolicyTrace → Nat
  | .finish _ => 0
  | .step _ tail => tail.length + 1

/-- Replace a trace's final snapshot by a continuation trace. -/
def PolicyTrace.append : app.PolicyTrace → app.PolicyTrace → app.PolicyTrace
  | .finish _, suffix => suffix
  | .step execution tail, suffix => .step execution (tail.append suffix)

@[simp] theorem PolicyTrace.append_last (front suffix : app.PolicyTrace) :
    (front.append suffix).last = suffix.last := by
  induction front with
  | finish => rfl
  | step _ _ ih => exact ih

@[simp] theorem PolicyTrace.append_finish_last (trace : app.PolicyTrace) :
    trace.append (.finish trace.last) = trace := by
  induction trace with
  | finish => rfl
  | step _ _ ih => simp only [append, last, ih]

@[simp] theorem PolicyTrace.append_length (front suffix : app.PolicyTrace) :
    (front.append suffix).length = front.length + suffix.length := by
  induction front with
  | finish => simp [append, length]
  | step _ _ ih => simp only [append, length, ih]; omega

/-- If the selected endpoint does not satisfy the cutoff, no earlier snapshot
did either, so the selected prefix is the complete trace. -/
theorem PolicyTrace.prefixThrough_eq_of_last_false (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool)
    (hclear : release (trace.prefixThrough release).last = false) :
    trace.prefixThrough release = trace := by
  induction trace with
  | finish => rfl
  | step execution tail ih =>
      cases hrelease : release execution with
      | true =>
          simp only [prefixThrough, hrelease, ↓reduceIte, last] at hclear
          contradiction
      | false =>
          simp only [prefixThrough, hrelease, Bool.false_eq_true, ↓reduceIte, last] at hclear ⊢
          exact congrArg (PolicyTrace.step execution) (ih hclear)

theorem PolicyTrace.prefixThrough_length_le (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool) :
    (trace.prefixThrough release).length ≤ trace.length := by
  induction trace with
  | finish => exact Nat.le_refl _
  | step execution tail ih =>
      cases hrelease : release execution <;>
        simp only [prefixThrough, hrelease, Bool.false_eq_true, ↓reduceIte, length] <;> omega

/-- Equality after stopping is equality of the original trace laws when the
right law never reaches the stopping condition. The mapped-law equality
transfers that fact to the left law as well. -/
theorem PolicyTrace.law_eq_of_prefixThrough_eq
    (left right : FinDist app.PolicyTrace) (release : app.PolicyExecution → Bool)
    (hmap : left.map (PolicyTrace.prefixThrough release) =
      right.map (PolicyTrace.prefixThrough release))
    (hclear : ∀ trace ∈ right.support,
      release (trace.prefixThrough release).last = false) :
    left = right := by
  have hleftClear : ∀ trace ∈ left.support,
      release (trace.prefixThrough release).last = false := by
    intro trace htrace
    have hmapped : trace.prefixThrough release ∈
        (left.map (PolicyTrace.prefixThrough release)).support := by
      rw [FinDist.support_map]
      exact ⟨trace, htrace, rfl⟩
    rw [hmap, FinDist.support_map] at hmapped
    obtain ⟨other, hother, heq⟩ := hmapped
    rw [← heq]
    exact hclear other hother
  have hleft : left.map (PolicyTrace.prefixThrough release) = left := by
    calc
      _ = left.map id := by
        apply FinDist.map_congr_of_eq_on_support
        intro trace htrace
        simpa only [id_eq] using trace.prefixThrough_eq_of_last_false release
          (hleftClear trace htrace)
      _ = left := FinDist.map_id left
  have hright : right.map (PolicyTrace.prefixThrough release) = right := by
    calc
      _ = right.map id := by
        apply FinDist.map_congr_of_eq_on_support
        intro trace htrace
        simpa only [id_eq] using trace.prefixThrough_eq_of_last_false release
          (hclear trace htrace)
      _ = right := FinDist.map_id right
  exact hleft.symm.trans (hmap.trans hright)

variable (app) [DecidableEq Principal]

theorem tracePolicies_length (players : Principal → app.PlayerPolicy)
    (environment : app.EnvironmentPolicy) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (trace : app.PolicyTrace)
    (htrace : trace ∈ (app.tracePolicies players environment schedule initial).support) :
    trace.length = schedule.length := by
  induction schedule generalizing initial trace with
  | nil =>
      simp only [tracePolicies, FinDist.mem_support_pure] at htrace
      subst trace
      rfl
  | cons invocation rest ih =>
      simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
        FinDist.support_map, Set.mem_image] at htrace
      obtain ⟨next, _, tail, htail, rfl⟩ := htrace
      exact congrArg (· + 1) (ih next tail htail)

/-- Exact joint law of the selected prefix and the complete execution trace.
Continuation uses the original policies and native kernels on the unused
invocation suffix. The stopped trace is reassembled with that continuation by
replacing its final snapshot. -/
theorem tracePolicies_prefix_trace_law
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    (app.tracePolicies players environment schedule initial).map
      (fun trace => (trace.prefixThrough release, trace)) =
      ((app.tracePolicies players environment schedule initial).map
        (PolicyTrace.prefixThrough release)).bind fun stopped =>
          (app.tracePolicies players environment (schedule.drop stopped.length) stopped.last).map
            (fun suffix => (stopped, stopped.append suffix)) := by
  induction schedule generalizing initial with
  | nil =>
      simp only [tracePolicies, FinDist.map_pure, PolicyTrace.prefixThrough,
        List.drop_nil, FinDist.pure_bind, PolicyTrace.append, PolicyTrace.last]
  | cons invocation rest ih =>
      rw [app.tracePolicies_prefixThrough_cons]
      cases hrelease : release initial with
      | true =>
          simp only [↓reduceIte, FinDist.pure_bind, PolicyTrace.length,
            PolicyTrace.last, List.drop_zero]
          have hpref : ∀ trace ∈ (app.tracePolicies players environment
              (invocation :: rest) initial).support,
              trace.prefixThrough release = .finish initial := by
            intro trace htrace
            simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
              FinDist.support_map, Set.mem_image] at htrace
            obtain ⟨next, _, tail, _, rfl⟩ := htrace
            simp only [PolicyTrace.prefixThrough, hrelease, ↓reduceIte]
          calc
            _ = (app.tracePolicies players environment (invocation :: rest) initial).map
                  (fun trace => (PolicyTrace.finish initial, trace)) := by
                apply FinDist.map_congr_of_eq_on_support
                intro trace htrace
                rw [hpref trace htrace]
            _ = _ := by
                rfl
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, tracePolicies,
            FinDist.map_bind, FinDist.map_comp, Function.comp_def, PolicyTrace.prefixThrough,
            hrelease, Bool.false_eq_true, ↓reduceIte, FinDist.bind_bind, FinDist.bind_map]
          apply FinDist.bind_congr
          intro next _
          have htail := congrArg (fun law => law.map
            (fun pair : app.PolicyTrace × app.PolicyTrace =>
              (PolicyTrace.step initial pair.1, PolicyTrace.step initial pair.2))) (ih next)
          simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_bind, FinDist.bind_map,
            PolicyTrace.length, PolicyTrace.last, PolicyTrace.append,
            List.drop_succ_cons] using htail

/-- Exact joint law of the selected prefix and the eventual final execution.
This is the final-state projection of `tracePolicies_prefix_trace_law`. -/
theorem tracePolicies_prefix_last_law
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    (app.tracePolicies players environment schedule initial).map
      (fun trace => (trace.prefixThrough release, trace.last)) =
      ((app.tracePolicies players environment schedule initial).map
        (PolicyTrace.prefixThrough release)).bind fun stopped =>
          (app.runPolicies players environment (schedule.drop stopped.length) stopped.last).map
            (fun final => (stopped, final)) := by
  let project : app.PolicyTrace × app.PolicyTrace → app.PolicyTrace × app.PolicyExecution :=
    fun pair => (pair.1, pair.2.last)
  calc
    _ = ((app.tracePolicies players environment schedule initial).map
          (fun trace => (trace.prefixThrough release, trace))).map project := by
        rw [FinDist.map_comp]
        rfl
    _ = (((app.tracePolicies players environment schedule initial).map
          (PolicyTrace.prefixThrough release)).bind fun stopped =>
            (app.tracePolicies players environment (schedule.drop stopped.length)
              stopped.last).map fun suffix =>
                (stopped, stopped.append suffix)).map project := by
        rw [app.tracePolicies_prefix_trace_law players environment release schedule initial]
    _ = _ := by
        rw [FinDist.map_bind]
        apply FinDist.bind_congr
        intro stopped _
        have hlast := congrArg (fun law => law.map (fun final => (stopped, final)))
          (app.tracePolicies_last players environment (schedule.drop stopped.length)
            stopped.last)
        simpa only [FinDist.map_comp, Function.comp_def, project, PolicyTrace.append_last]
          using hlast

/-- Forgetting the selected prefix in the joint law recovers the original
final-state law. This retains all dependence through the stopped state and
the private and environment histories it carries. -/
theorem runPolicies_bind_prefixThrough
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    app.runPolicies players environment schedule initial =
      ((app.tracePolicies players environment schedule initial).map
        (PolicyTrace.prefixThrough release)).bind fun stopped =>
          app.runPolicies players environment (schedule.drop stopped.length) stopped.last := by
  have h := congrArg (fun law => law.map Prod.snd)
    (app.tracePolicies_prefix_last_law players environment release schedule initial)
  have hid (law : FinDist app.PolicyExecution) : law.map (fun value => value) = law :=
    FinDist.map_id law
  simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_bind, hid,
    app.tracePolicies_last] using h

/-- Retain an auxiliary realization and continue its selected native prefix
using the original policies. The realization may contain source information;
it is never supplied as an input to the native continuation policies. -/
def couplePrefix {α : Type*}
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (source : FinDist α)
    (prefixOf : α → app.PolicyTrace) : FinDist (α × app.PolicyTrace) :=
  source.bind fun value =>
    (app.tracePolicies players environment (schedule.drop (prefixOf value).length)
      (prefixOf value).last).map fun suffix => (value, (prefixOf value).append suffix)

/-- A normalized continuation preserves the retained realization law. -/
theorem couplePrefix_fst {α : Type*}
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (source : FinDist α)
    (prefixOf : α → app.PolicyTrace) :
    (app.couplePrefix players environment schedule source prefixOf).map Prod.fst = source := by
  simp only [couplePrefix, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
    FinDist.map_const, FinDist.bind_pure]

/-- Equality of prefix laws gives the exact joint prefix/full-trace law after
continuation. Separate marginal equalities are not assumed sufficient. -/
theorem couplePrefix_prefix_native {α : Type*}
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (source : FinDist α) (prefixOf : α → app.PolicyTrace)
    (hprefix : source.map prefixOf = (app.tracePolicies players environment schedule initial).map
      (PolicyTrace.prefixThrough release)) :
    (app.couplePrefix players environment schedule source prefixOf).map
        (fun pair => (prefixOf pair.1, pair.2)) =
      (app.tracePolicies players environment schedule initial).map
        (fun trace => (trace.prefixThrough release, trace)) := by
  rw [app.tracePolicies_prefix_trace_law players environment release, ← hprefix]
  simp only [couplePrefix, FinDist.map_bind, FinDist.map_comp, Function.comp_def, FinDist.bind_map]

/-- The native marginal is the original full execution law, including any
post-cutoff behavior and its dependence on the selected prefix. -/
theorem couplePrefix_native {α : Type*}
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (source : FinDist α) (prefixOf : α → app.PolicyTrace)
    (hprefix : source.map prefixOf = (app.tracePolicies players environment schedule initial).map
      (PolicyTrace.prefixThrough release)) :
    (app.couplePrefix players environment schedule source prefixOf).map Prod.snd =
      app.tracePolicies players environment schedule initial := by
  have hlaw := congrArg (fun law => law.map Prod.snd)
    (app.couplePrefix_prefix_native players environment release schedule initial
      source prefixOf hprefix)
  simp only [FinDist.map_comp, Function.comp_def] at hlaw
  exact hlaw.trans (FinDist.map_id _)

end Interaction.MessageApplication
