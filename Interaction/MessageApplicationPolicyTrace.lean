/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Full invocation traces of message-application games

Recording calls the canonical policy invocation, retaining the initial and
every post-invocation snapshot, including waits and native random transitions.
The last-snapshot law equals the uninstrumented execution law. Snapshots are
analysis data and are not supplied to policies.

A release readout selects the earliest matching snapshot, or the last if none
matches. Execution continues after the selected snapshot; neither stopping nor
conditioning is built into the runtime. The generic readout may inspect any
execution data. Information-flow theorems must separately justify its predicate.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal}

inductive PolicyTrace (app : MessageApplication Principal) where
  | finish (execution : app.PolicyExecution)
  | step (execution : app.PolicyExecution) (tail : PolicyTrace app)

variable {app : MessageApplication Principal}

def PolicyTrace.last : app.PolicyTrace → app.PolicyExecution
  | .finish execution => execution
  | .step _ tail => tail.last

def PolicyTrace.firstRelease (release : app.PolicyExecution → Bool) :
    app.PolicyTrace → app.PolicyExecution
  | .finish execution => execution
  | .step execution tail =>
      if release execution then execution else tail.firstRelease release

theorem PolicyTrace.firstRelease_false_eq_last (trace : app.PolicyTrace) :
    trace.firstRelease (fun _ => false) = trace.last := by
  induction trace with
  | finish => rfl
  | step execution tail ih => simpa [firstRelease, last] using ih

variable (app)

def tracePolicies [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy) :
    List (@Invocation Principal) → app.PolicyExecution → FinDist app.PolicyTrace
  | [], execution => FinDist.pure (.finish execution)
  | invocation :: rest, execution =>
      (app.invoke players environment execution invocation).bind fun next =>
        (tracePolicies players environment rest next).map (.step execution)

/-- Instrumentation preserves the full policy-game outcome law. -/
theorem tracePolicies_last [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution) :
    (app.tracePolicies players environment schedule execution).map PolicyTrace.last =
      app.runPolicies players environment schedule execution := by
  induction schedule generalizing execution with
  | nil => simp [tracePolicies, runPolicies, PolicyTrace.last]
  | cons invocation rest ih =>
      simp only [tracePolicies, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
        PolicyTrace.last, ih, runPolicies]

theorem tracePolicies_firstRelease_cons [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool)
    (invocation : @Invocation Principal) (rest : List (@Invocation Principal))
    (execution : app.PolicyExecution) :
    (app.tracePolicies players environment (invocation :: rest) execution).map
        (PolicyTrace.firstRelease release) =
      if release execution then FinDist.pure execution else
        (app.invoke players environment execution invocation).bind fun next =>
          (app.tracePolicies players environment rest next).map
            (PolicyTrace.firstRelease release) := by
  cases hrelease : release execution <;>
    simp [tracePolicies, PolicyTrace.firstRelease, hrelease, Function.comp_def]

/-- A selected snapshot lies on an actual invocation prefix, and the final
snapshot is supported by the remaining suffix from that same selected state.
Both segments use unchanged policies. No progress or monotonicity is assumed. -/
theorem tracePolicies_firstRelease_split [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (trace : app.PolicyTrace)
    (htrace : trace ∈ (app.tracePolicies players environment schedule execution).support) :
    ∃ front suffix, schedule = front ++ suffix ∧
      trace.firstRelease release ∈ (app.runPolicies players environment front execution).support ∧
      trace.last ∈ (app.runPolicies players environment suffix
        (trace.firstRelease release)).support := by
  induction schedule generalizing execution trace with
  | nil =>
      have heq : trace = .finish execution := by simpa [tracePolicies] using htrace
      subst trace
      exact ⟨[], [], rfl, FinDist.mem_support_pure.mpr rfl, FinDist.mem_support_pure.mpr rfl⟩
  | cons invocation rest ih =>
      have hlast : trace.last ∈
          (app.runPolicies players environment (invocation :: rest) execution).support := by
        rw [← app.tracePolicies_last, FinDist.support_map]
        exact ⟨trace, htrace, rfl⟩
      simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
        FinDist.support_map, Set.mem_image] at htrace
      obtain ⟨next, hnext, tail, htail, rfl⟩ := htrace
      cases hrelease : release execution with
      | true =>
          refine ⟨[], invocation :: rest, rfl, ?_, ?_⟩
          · simp [runPolicies, PolicyTrace.firstRelease, hrelease]
          · simpa only [PolicyTrace.firstRelease, hrelease, ↓reduceIte] using hlast
      | false =>
          obtain ⟨front, suffix, hsplit, hprefix, hsuffix⟩ := ih next tail htail
          refine ⟨invocation :: front, suffix, by simp [hsplit], ?_, ?_⟩
          · simp only [PolicyTrace.firstRelease, hrelease, Bool.false_eq_true, ↓reduceIte,
              runPolicies, FinDist.support_bind, Set.mem_iUnion]
            exact ⟨next, hnext, hprefix⟩
          · simpa only [PolicyTrace.firstRelease, hrelease, Bool.false_eq_true, ↓reduceIte,
              PolicyTrace.last] using hsuffix

/-- info: 'Interaction.MessageApplication.tracePolicies_last' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracePolicies_last

/-- info: 'Interaction.MessageApplication.tracePolicies_firstRelease_split' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracePolicies_firstRelease_split

end Interaction.MessageApplication
