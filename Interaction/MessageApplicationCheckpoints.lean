/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationContinuation

/-! # Fixed-width checkpoint readouts of native invocation traces

These projections inspect an already-recorded trace. They do not add a runtime
transition or expose trace snapshots to a policy. Checking a release predicate
at block boundaries represents a driver's early stopping exactly.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} {app : MessageApplication Principal}

/-- Skip invocation snapshots, retaining the final snapshot if the trace ends. -/
def PolicyTrace.drop : Nat → app.PolicyTrace → app.PolicyTrace
  | 0, trace => trace
  | _ + 1, .finish execution => .finish execution
  | count + 1, .step _ tail => tail.drop count

theorem PolicyTrace.drop_append_length (front tail : app.PolicyTrace) :
    (front.append tail).drop front.length = tail := by
  induction front with
  | finish => rfl
  | step execution front ih => exact ih

/-- Select the first successful check at one of the next fixed-width block
boundaries; if none succeeds, retain the trace's final execution. -/
def PolicyTrace.firstReleaseEvery (width : Nat) (release : app.PolicyExecution → Bool) :
    Nat → app.PolicyTrace → app.PolicyExecution
  | 0, trace => trace.last
  | count + 1, trace =>
      if release trace.first then trace.first
      else firstReleaseEvery width release count (trace.drop width)

theorem PolicyTrace.firstReleaseEvery_append (front tail : app.PolicyTrace)
    (width count : Nat) (release : app.PolicyExecution → Bool)
    (hwidth : 0 < width) (hlength : front.length = width) :
    (front.append tail).firstReleaseEvery width release (count + 1) =
      if release front.first then front.first
      else tail.firstReleaseEvery width release count := by
  have hfirst : (front.append tail).first = front.first := by
    cases front with
    | finish => simp only [length] at hlength; omega
    | step => rfl
  simp only [firstReleaseEvery, hfirst]
  rw [← hlength, drop_append_length]

/-- Concatenating invocation schedules concatenates the actual recorded
traces, with their shared boundary snapshot retained once. -/
theorem tracePolicies_append [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (front rest : List (@Invocation Principal)) (execution : app.PolicyExecution) :
    app.tracePolicies players environment (front ++ rest) execution =
      (app.tracePolicies players environment front execution).bind fun first =>
        (app.tracePolicies players environment rest first.last).map (first.append) := by
  induction front generalizing execution with
  | nil =>
      simp only [List.nil_append, tracePolicies, FinDist.pure_bind, PolicyTrace.last,
        PolicyTrace.append]
      change _ = FinDist.map id _
      exact (FinDist.map_id (app.tracePolicies players environment rest execution)).symm
  | cons invocation front ih =>
      simp only [List.cons_append, tracePolicies, FinDist.bind_bind, FinDist.bind_map]
      apply FinDist.bind_congr
      intro next _
      rw [ih, FinDist.map_bind]
      apply FinDist.bind_congr
      intro first _
      simp only [FinDist.map_comp, Function.comp_def, PolicyTrace.last, PolicyTrace.append]

/-- A block-boundary readout splits along the same invocation boundary as the
shared runner, retaining all native histories and observations at that point. -/
theorem tracePolicies_firstReleaseEvery_block [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (block rest : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (release : app.PolicyExecution → Bool) (count : Nat) (hblock : 0 < block.length) :
    (app.tracePolicies players environment (block ++ rest) execution).map
        (PolicyTrace.firstReleaseEvery block.length release (count + 1)) =
      if release execution then FinDist.pure execution
      else (app.runPolicies players environment block execution).bind fun next =>
        (app.tracePolicies players environment rest next).map
          (PolicyTrace.firstReleaseEvery block.length release count) := by
  rw [app.tracePolicies_append, FinDist.map_bind]
  have hreadout : ∀ first ∈ (app.tracePolicies players environment block execution).support,
      (app.tracePolicies players environment rest first.last).map
          (fun tail => (first.append tail).firstReleaseEvery block.length release (count + 1)) =
        if release execution then FinDist.pure execution
        else (app.tracePolicies players environment rest first.last).map
          (PolicyTrace.firstReleaseEvery block.length release count) := by
    intro first hfirst
    have hlength := app.tracePolicies_length players environment block execution first hfirst
    have hstart := app.tracePolicies_first players environment block execution first hfirst
    simp_rw [PolicyTrace.firstReleaseEvery_append first _ block.length count release
      hblock hlength, hstart]
    split <;> simp
  simp only [FinDist.map_comp, Function.comp_def]
  calc
    _ = (app.tracePolicies players environment block execution).bind (fun first =>
          if release execution then FinDist.pure execution
          else (app.tracePolicies players environment rest first.last).map
            (PolicyTrace.firstReleaseEvery block.length release count)) :=
        FinDist.bind_congr hreadout
    _ = _ := by
        cases release execution <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [← app.tracePolicies_last players environment block execution, FinDist.bind_map]
        · simp

/-- A block-boundary selection splits the actual run into a supported prefix
and a supported continuation from that exact snapshot. Policies are unchanged
on both sides of the split. -/
theorem tracePolicies_firstReleaseEvery_split [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (width count : Nat) (release : app.PolicyExecution → Bool) (hwidth : 0 < width)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (trace : app.PolicyTrace) (hbudget : count * width ≤ schedule.length)
    (htrace : trace ∈ (app.tracePolicies players environment schedule execution).support) :
    ∃ front suffix, schedule = front ++ suffix ∧
      trace.firstReleaseEvery width release count ∈
        (app.runPolicies players environment front execution).support ∧
      trace.last ∈ (app.runPolicies players environment suffix
        (trace.firstReleaseEvery width release count)).support := by
  have hlast : trace.last ∈ (app.runPolicies players environment schedule execution).support := by
    rw [← app.tracePolicies_last, FinDist.support_map]
    exact ⟨trace, htrace, rfl⟩
  induction count generalizing schedule execution trace with
  | zero =>
      exact ⟨schedule, [], (List.append_nil _).symm, hlast,
        FinDist.mem_support_pure.mpr rfl⟩
  | succ count ih =>
      have hfirst := app.tracePolicies_first players environment schedule execution trace htrace
      by_cases hrelease : release execution = true
      · refine ⟨[], schedule, rfl, ?_, ?_⟩
        · simp only [PolicyTrace.firstReleaseEvery, hfirst, hrelease, ↓reduceIte,
            runPolicies, FinDist.mem_support_pure]
        · simpa only [PolicyTrace.firstReleaseEvery, hfirst, hrelease, ↓reduceIte] using hlast
      · have hsize : width ≤ schedule.length := by
          rw [Nat.succ_mul] at hbudget
          omega
        have htailBudget : count * width ≤ (schedule.drop width).length := by
          rw [List.length_drop]
          rw [Nat.succ_mul] at hbudget
          omega
        rw [← List.take_append_drop width schedule, app.tracePolicies_append] at htrace
        simp only [FinDist.support_bind, Set.mem_iUnion,
          FinDist.support_map, Set.mem_image] at htrace
        obtain ⟨front, hfront, tail, htail, rfl⟩ := htrace
        have hlength : front.length = width := by
          rw [app.tracePolicies_length players environment _ execution front hfront,
            List.length_take, Nat.min_eq_left hsize]
        have hfrontFirst := app.tracePolicies_first players environment _ execution front hfront
        have hfrontLast : front.last ∈
            (app.runPolicies players environment (schedule.take width) execution).support := by
          rw [← app.tracePolicies_last, FinDist.support_map]
          exact ⟨front, hfront, rfl⟩
        obtain ⟨before, after, hsplit, hbefore, hafter⟩ :=
          ih (schedule.drop width) front.last tail htailBudget htail (by
            rw [← app.tracePolicies_last, FinDist.support_map]
            exact ⟨tail, htail, rfl⟩)
        have hread : (front.append tail).firstReleaseEvery width release (count + 1) =
            tail.firstReleaseEvery width release count := by
          rw [PolicyTrace.firstReleaseEvery_append front tail width count release hwidth hlength,
            hfrontFirst, if_neg hrelease]
        refine ⟨schedule.take width ++ before, after, ?_, ?_, ?_⟩
        · rw [List.append_assoc, ← hsplit, List.take_append_drop]
        · rw [hread, app.runPolicies_append]
          simp only [FinDist.support_bind, Set.mem_iUnion]
          exact ⟨front.last, hfrontLast, hbefore⟩
        · simpa only [PolicyTrace.append_last, hread] using hafter

end Interaction.MessageApplication
