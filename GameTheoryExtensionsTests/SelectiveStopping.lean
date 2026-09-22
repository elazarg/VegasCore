/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.SelectiveStopping

/-! # Finite regressions for information-fiber stopping bounds -/

noncomputable section

namespace GameTheoryExtensionsTests.SelectiveStopping

open GameTheory.Math.Probability

def law : FinDist (Fin 3) := FinDist.uniformFin 3

def stopped (state : Fin 3) : Bool := decide (state = 0 ∨ state = 1)

def information (state : Fin 3) : Fin 3 :=
  if state = 0 ∨ state = 1 then 0 else 1

def targetValue (state : Fin 3) : ℝ :=
  if state = 0 then 3 else if state = 1 then 0 else 1

def sourceValue (state : Fin 3) : ℝ :=
  if state = 0 then 1 else if state = 1 then 3 else 1

def margin : ℝ := 1 / 2

/-- Information value two has zero mass, so the fiber theorem requests no
comparison for it. Value one occurs only outside the stopping event. -/
theorem unsupported_stopped_fibers :
    ¬ (∃ state ∈ law.support,
        stopped state = true ∧ information state = (1 : Fin 3)) ∧
      ¬ (∃ state ∈ law.support,
        stopped state = true ∧ information state = (2 : Fin 3)) := by
  constructor <;> rintro ⟨state, _, hstopped, hinfo⟩ <;>
    fin_cases state <;> simp [stopped, information] at hstopped hinfo

/-- On the sole supported stopped fiber, gains and losses average to exactly
the source value after charging the positive margin. -/
theorem stopped_fiber_comparison (observed : Fin 3)
    (hobserved : ∃ state ∈ law.support,
      stopped state = true ∧ information state = observed) :
    law.expect (fun state =>
        if stopped state && decide (information state = observed)
        then targetValue state + margin else 0) ≤
      law.expect (fun state =>
        if stopped state && decide (information state = observed)
        then sourceValue state else 0) := by
  obtain ⟨state, _, hstopped, hinfo⟩ := hobserved
  have heq : observed = 0 := by
    fin_cases state <;> simp [stopped, information] at hstopped hinfo
    · exact hinfo.symm
    · exact hinfo.symm
  subst observed
  have htarget : (fun state : Fin 3 =>
      if stopped state && decide (information state = (0 : Fin 3))
      then targetValue state + margin else 0) =
      fun state => if state = 0 then 7 / 2 else if state = 1 then 1 / 2 else 0 := by
    funext state
    fin_cases state <;> norm_num [stopped, information, targetValue, margin]
  have hsource : (fun state : Fin 3 =>
      if stopped state && decide (information state = (0 : Fin 3))
      then sourceValue state else 0) =
      fun state => if state = 0 then 1 else if state = 1 then 3 else 0 := by
    funext state
    fin_cases state <;> norm_num [stopped, information, sourceValue]
  rw [heq]
  rw [htarget, hsource]
  unfold law
  rw [FinDist.expect_uniformFin, FinDist.expect_uniformFin]
  have hne : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Fin.sum_univ_succ, hne]

/-- The fiber condition is strictly weaker than pointwise dominance: state
zero favors the target even after charging the margin. -/
theorem pointwise_comparison_fails :
    ¬ ∀ state ∈ law.support, stopped state = true →
      targetValue state + margin ≤ sourceValue state := by
  intro h
  have hsupport : (0 : Fin 3) ∈ law.support := by
    rw [← FinDist.prob_pos_iff]
    norm_num [law]
  have hbound := h 0 hsupport (by decide)
  norm_num [targetValue, sourceValue, margin] at hbound

/-- A genuinely random stopping event with positive margin satisfies the
unconditional bound even though pointwise stopped-state comparison fails. -/
theorem randomized_positive_margin_bound :
    0 < margin ∧ 0 < (law.map stopped).prob true ∧
      law.expect targetValue + margin * (law.map stopped).prob true ≤
        law.expect sourceValue := by
  refine ⟨by norm_num [margin], ?_, ?_⟩
  · rw [FinDist.prob_map, law, FinDist.expect_uniformFin]
    norm_num [stopped, Fin.sum_univ_succ]
    exact ⟨0, by simp⟩
  · apply FinDist.stopping_information_fiber_bound law stopped information
      sourceValue targetValue margin
    · intro state _ hstate
      fin_cases state <;> simp [stopped, targetValue, sourceValue] at hstate ⊢
    · exact stopped_fiber_comparison

private def gapEvent (state : Fin 2) : Bool := decide (state = 0)

private def gapSource (state : Fin 2) : ℝ := if state = 0 then -1 else 3

private def gapTarget (state : Fin 2) : ℝ := if state = 0 then 0 else 3

/-- The event-weighted discrepancy bound can be attained: a unit improvement
on an event of probability one half raises expectation from one to three halves.
This is a finite-law regression, not a native-runtime optimality claim. -/
theorem event_gap_sharp :
    let pair := FinDist.uniformFin 2
    (pair.map gapEvent).prob true = 1 / 2 ∧
      pair.expect gapSource = 1 ∧ pair.expect gapTarget = 3 / 2 ∧
      pair.expect gapTarget ≤ pair.expect gapSource + 1 * (pair.map gapEvent).prob true := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FinDist.prob_map, FinDist.expect_uniformFin]
    norm_num [gapEvent, Fin.sum_univ_succ]
  · rw [FinDist.expect_uniformFin]
    norm_num [gapSource, Fin.sum_univ_succ]
  · rw [FinDist.expect_uniformFin]
    norm_num [gapTarget, Fin.sum_univ_succ]
  · rw [FinDist.prob_map_eq_probOf_preimage_singleton]
    apply FinDist.expect_le_add_event_gap
    · intro state _ hstate
      fin_cases state <;> simp [gapEvent, gapSource, gapTarget] at hstate ⊢
    · intro state _ hstate
      fin_cases state <;> simp [gapEvent, gapSource, gapTarget] at hstate ⊢

end GameTheoryExtensionsTests.SelectiveStopping

/-! The regression proof itself uses only the standard finite-law axioms. -/
