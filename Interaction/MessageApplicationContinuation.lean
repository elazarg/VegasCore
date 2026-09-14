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

theorem PolicyTrace.prefixThrough_length_le (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool) :
    (trace.prefixThrough release).length ≤ trace.length := by
  induction trace with
  | finish => exact Nat.le_refl _
  | step execution tail ih =>
      cases hrelease : release execution <;>
        simp only [prefixThrough, hrelease, Bool.false_eq_true, ↓reduceIte, length] <;> omega

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

/-- Exact joint law of the selected prefix and the eventual final execution.
Continuation uses the original policies and the original native kernels on the
remaining invocation list. The cutoff may inspect any proof-facing state data;
an information-flow or incentive theorem must justify its particular use. -/
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
  induction schedule generalizing initial with
  | nil =>
      simp only [tracePolicies, FinDist.map_pure, PolicyTrace.prefixThrough,
        PolicyTrace.last, List.drop_nil, runPolicies, FinDist.pure_bind]
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
                  (fun trace => (PolicyTrace.finish initial, trace.last)) := by
                apply FinDist.map_congr_of_eq_on_support
                intro trace htrace
                rw [hpref trace htrace]
            _ = _ := by
                change (app.tracePolicies players environment (invocation :: rest) initial).map
                  ((fun final => (PolicyTrace.finish initial, final)) ∘ PolicyTrace.last) = _
                rw [← FinDist.map_comp, app.tracePolicies_last]
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, tracePolicies,
            FinDist.map_bind, FinDist.map_comp, Function.comp_def, PolicyTrace.prefixThrough,
            hrelease, Bool.false_eq_true, ↓reduceIte, PolicyTrace.last, FinDist.bind_bind,
            FinDist.bind_map]
          apply FinDist.bind_congr
          intro next _
          have htail := congrArg (fun law => law.map
            (fun pair : app.PolicyTrace × app.PolicyExecution =>
              (PolicyTrace.step initial pair.1, pair.2))) (ih next)
          simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_bind, FinDist.bind_map,
            PolicyTrace.length, PolicyTrace.last, List.drop_succ_cons] using htail

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

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.tracePolicies_prefix_last_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.tracePolicies_prefix_last_law

/-- info: 'Interaction.MessageApplication.runPolicies_bind_prefixThrough' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_bind_prefixThrough
