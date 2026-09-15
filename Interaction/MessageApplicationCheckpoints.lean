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

theorem PolicyTrace.drop_length (trace : app.PolicyTrace) :
    trace.drop trace.length = .finish trace.last := by
  induction trace with
  | finish execution => rfl
  | step execution tail ih => exact ih

theorem PolicyTrace.drop_append_length (front tail : app.PolicyTrace) :
    (front.append tail).drop front.length = tail := by
  induction front with
  | finish => rfl
  | step execution front ih => exact ih

theorem PolicyTrace.drop_add (trace : app.PolicyTrace) (first second : Nat) :
    (trace.drop first).drop second = trace.drop (first + second) := by
  induction first generalizing trace with
  | zero => simp only [drop, Nat.zero_add]
  | succ first ih =>
      cases trace with
      | finish execution => cases second <;> rfl
      | step execution tail => simpa only [drop, Nat.succ_add] using ih tail

private theorem PolicyTrace.length_drop (trace : app.PolicyTrace) (count : Nat) :
    (trace.drop count).length = trace.length - count := by
  induction count generalizing trace with
  | zero => simp only [drop, Nat.sub_zero]
  | succ count ih =>
      cases trace with
      | finish execution => simp only [drop, length, Nat.zero_sub]
      | step execution tail =>
          simp only [drop, length]
          rw [ih]
          omega

private theorem PolicyTrace.drop_eq_finish_of_length_le (trace : app.PolicyTrace) (count : Nat)
    (hcount : trace.length ≤ count) :
    trace.drop count = .finish trace.last := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hcount
  rw [← trace.drop_add trace.length extra, trace.drop_length]
  cases extra <;> rfl

/-- If an indexed snapshot satisfies a release condition, the trace's first
such snapshot occurs no later than that index. -/
theorem PolicyTrace.prefixThrough_length_le_of_drop_first (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool) (index : Nat)
    (hrelease : release (trace.drop index).first = true) :
    (trace.prefixThrough release).length ≤ index := by
  induction index generalizing trace with
  | zero =>
      cases trace <;> simp_all only [drop, first, prefixThrough, length, Nat.le_refl,
        ↓reduceIte]
  | succ index ih =>
      cases trace with
      | finish execution => simp only [prefixThrough, length, Nat.zero_le]
      | step execution tail =>
          cases hfirst : release execution with
          | true => simp only [prefixThrough, hfirst, ↓reduceIte, length, Nat.zero_le]
          | false =>
              have htail := ih tail (by simpa only [drop] using hrelease)
              simpa only [prefixThrough, hfirst, Bool.false_eq_true, ↓reduceIte, length]
                using Nat.succ_le_succ htail

/-- If any indexed snapshot satisfies the predicate, the first-release
readout also satisfies it. This needs no monotonicity assumption on the
predicate or consistency assumption on the recorded snapshots. -/
theorem PolicyTrace.release_firstRelease_of_drop_first (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool) (index : Nat)
    (hrelease : release (trace.drop index).first = true) :
    release (trace.firstRelease release) = true := by
  induction index generalizing trace with
  | zero =>
      cases trace <;> simp_all only [drop, first, firstRelease, ↓reduceIte]
  | succ index ih =>
      cases trace with
      | finish execution => exact hrelease
      | step execution tail =>
          cases hfirst : release execution with
          | true => simp only [firstRelease, hfirst, ↓reduceIte]
          | false =>
              simpa only [firstRelease, hfirst, Bool.false_eq_true, ↓reduceIte] using
                ih tail hrelease

/-- The first-release readout is the snapshot immediately after its retained
invocation prefix. This also covers traces that never satisfy the predicate. -/
theorem PolicyTrace.firstRelease_eq_drop_prefixThrough_length (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool) :
    trace.firstRelease release = (trace.drop (trace.prefixThrough release).length).first := by
  induction trace with
  | finish execution => rfl
  | step execution tail ih =>
      cases hrelease : release execution <;>
        simp only [firstRelease, prefixThrough, hrelease, Bool.false_eq_true,
          ↓reduceIte, length, drop, first, ih]

/-- Every snapshot strictly before the first-release boundary fails the
predicate, even when the retained prefix is the complete trace. -/
theorem PolicyTrace.release_false_before_prefixThrough (trace : app.PolicyTrace)
    (release : app.PolicyExecution → Bool) (index : Nat)
    (hindex : index < (trace.prefixThrough release).length) :
    release (trace.drop index).first = false := by
  cases hrelease : release (trace.drop index).first with
  | false => rfl
  | true =>
      have hle := trace.prefixThrough_length_le_of_drop_first release index hrelease
      omega

/-- Every indexed checkpoint lies on the actual prefix, and its remaining
record is supported by the unchanged policies on the remaining invocation list.
Indices beyond the end retain the final snapshot. -/
theorem tracePolicies_drop_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (trace : app.PolicyTrace)
    (htrace : trace ∈ (app.tracePolicies players environment schedule execution).support)
    (count : Nat) :
    (trace.drop count).first ∈
        (app.runPolicies players environment (schedule.take count) execution).support ∧
      trace.drop count ∈ (app.tracePolicies players environment (schedule.drop count)
        (trace.drop count).first).support := by
  induction count generalizing schedule execution trace with
  | zero =>
      have hfirst := app.tracePolicies_first players environment schedule execution trace htrace
      simpa only [PolicyTrace.drop, List.take_zero, List.drop_zero, runPolicies,
        FinDist.mem_support_pure, hfirst, true_and] using htrace
  | succ count ih =>
      cases schedule with
      | nil =>
          simp only [tracePolicies, FinDist.mem_support_pure] at htrace
          subst trace
          simp [PolicyTrace.drop, PolicyTrace.first, runPolicies, tracePolicies]
      | cons invocation rest =>
          simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
            FinDist.support_map, Set.mem_image] at htrace
          obtain ⟨next, hnext, tail, htail, rfl⟩ := htrace
          obtain ⟨hprefix, hsuffix⟩ := ih rest next tail htail
          refine ⟨?_, hsuffix⟩
          simp only [PolicyTrace.drop, List.take_succ_cons, runPolicies,
            FinDist.support_bind, Set.mem_iUnion]
          exact ⟨next, hnext, hprefix⟩

/-- Any interval of indexed snapshots is an execution of the corresponding
invocation slice, retaining the policies' actual memories at its first snapshot. -/
theorem tracePolicies_between [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (trace : app.PolicyTrace)
    (htrace : trace ∈ (app.tracePolicies players environment schedule execution).support)
    (start count : Nat) :
    (trace.drop (start + count)).first ∈
      (app.runPolicies players environment ((schedule.drop start).take count)
        (trace.drop start).first).support := by
  have htail := (app.tracePolicies_drop_support players environment schedule execution trace
    htrace start).2
  simpa only [PolicyTrace.drop_add] using
    (app.tracePolicies_drop_support players environment (schedule.drop start)
      (trace.drop start).first (trace.drop start) htail count).1

/-- Adjacent checkpoints expose exactly the invocation recorded at that
position, rather than an independently chosen transition with matching endpoints. -/
theorem tracePolicies_drop_invoke [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (trace : app.PolicyTrace)
    (htrace : trace ∈ (app.tracePolicies players environment schedule execution).support)
    (index : Nat) (invocation : @Invocation Principal)
    (hcall : schedule[index]? = some invocation) :
    (trace.drop (index + 1)).first ∈
      (app.invoke players environment (trace.drop index).first invocation).support := by
  have hbetween := app.tracePolicies_between players environment schedule execution trace
    htrace index 1
  obtain ⟨hindex, hcall⟩ := List.getElem?_eq_some_iff.mp hcall
  rw [List.drop_eq_getElem_cons hindex, hcall] at hbetween
  simpa only [List.take_succ_cons, List.take_zero, runPolicies, FinDist.bind_pure] using hbetween

/-- Select the first successful check at one of the next fixed-width block
boundaries; if none succeeds, retain the trace's final execution. -/
def PolicyTrace.firstReleaseEvery (width : Nat) (release : app.PolicyExecution → Bool) :
    Nat → app.PolicyTrace → app.PolicyExecution
  | 0, trace => trace.last
  | count + 1, trace =>
      if release trace.first then trace.first
      else firstReleaseEvery width release count (trace.drop width)

private theorem PolicyTrace.firstReleaseEvery_finish (execution : app.PolicyExecution)
    (width : Nat) (release : app.PolicyExecution → Bool) (count : Nat) :
    (PolicyTrace.finish execution).firstReleaseEvery width release count = execution := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hdrop : (PolicyTrace.finish execution).drop width = .finish execution := by
        cases width <;> rfl
      rw [firstReleaseEvery]
      by_cases hrelease : release execution = true
      · simp only [first, hrelease, ↓reduceIte]
      · simp only [first, hrelease, Bool.false_eq_true, ↓reduceIte, hdrop, ih]

/-- A fixed-width release readout is an actual snapshot of the supplied trace.
When that snapshot satisfies the release condition, the trace's first release
occurred at or before its index. -/
theorem PolicyTrace.firstReleaseEvery_indexed (trace : app.PolicyTrace) (width : Nat)
    (release : app.PolicyExecution → Bool) (count : Nat) :
    ∃ index ≤ trace.length,
      trace.firstReleaseEvery width release count = (trace.drop index).first ∧
        (release (trace.firstReleaseEvery width release count) = true →
          (trace.prefixThrough release).length ≤ index) := by
  induction count generalizing trace with
  | zero =>
      refine ⟨trace.length, Nat.le_refl _, ?_, ?_⟩
      · simp only [firstReleaseEvery, drop_length, first]
      · intro hrelease
        exact trace.prefixThrough_length_le release
  | succ count ih =>
      simp only [firstReleaseEvery]
      by_cases hrelease : release trace.first = true
      · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
        · simp only [hrelease, ↓reduceIte, drop]
        · intro _
          cases trace <;> simp_all only [first, prefixThrough, length, Nat.le_refl,
            ↓reduceIte]
      · rw [if_neg hrelease]
        by_cases hwidth : width ≤ trace.length
        · obtain ⟨index, hindex, heq, _⟩ := ih (trace.drop width)
          refine ⟨width + index, ?_, ?_, ?_⟩
          · rw [PolicyTrace.length_drop] at hindex
            omega
          · rw [← trace.drop_add]
            exact heq
          · intro hselected
            apply trace.prefixThrough_length_le_of_drop_first release (width + index)
            rw [← trace.drop_add, ← heq]
            exact hselected
        · have hdrop : trace.drop width = .finish trace.last :=
            trace.drop_eq_finish_of_length_le width (by omega)
          refine ⟨trace.length, Nat.le_refl _, ?_, ?_⟩
          · rw [hdrop, PolicyTrace.firstReleaseEvery_finish, trace.drop_length]
            rfl
          · intro _
            exact trace.prefixThrough_length_le release

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
