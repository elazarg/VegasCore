/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceGeometricTiming

/-! # Compatible rates for binding and resolution deferral

A finite family of vanishing source errors can be reindexed so that each is
negligible relative to every resolution reach mass up to the service horizon.
Binding deferral can independently vanish faster than any positive source
passage scale. The strictly increasing reindexing preserves all existing
source assessment limits.

The errors and passage scales must be supplied by their source likelihood
and incentive proofs. This rate construction asserts no belief transport or
sequential rationality.
-/

noncomputable section

namespace Vegas

open Filter

private theorem finite_errors_below_budget {Site : Type*} [Finite Site]
    (error : Site → ℕ → ℝ) (vanishes : ∀ site, Tendsto (error site) atTop (nhds 0))
    (budget : ℕ → ℝ) (positive : ∀ n, 0 < budget n) :
    ∃ index : ℕ → ℕ, StrictMono index ∧ ∀ n site, error site (index n) < budget n := by
  classical
  have eventuallySmall (n : ℕ) :
      ∃ cutoff : ℕ, ∀ k ≥ cutoff, ∀ site, error site k < budget n := by
    apply eventually_atTop.mp
    exact eventually_all.mpr fun site => (tendsto_order.mp (vanishes site)).2 _ (positive n)
  choose cutoff beyond using eventuallySmall
  let index : ℕ → ℕ := fun n => Nat.rec (cutoff 0)
    (fun k previous => max (cutoff (k + 1)) (previous + 1)) n
  have above (n : ℕ) : cutoff n ≤ index n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  refine ⟨index, strictMono_nat_of_lt_succ (fun n => ?_), fun n site =>
    beyond n (index n) (above n) site⟩
  change index n < max (cutoff (n + 1)) (index n + 1)
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

/-- A single source subsequence supports slow resolution deferral for every
vanishing error and every depth up to the horizon, together with independently
fast binding deferral relative to a positive source passage scale. -/
theorem exists_source_timing_rates {Site : Type*} [Finite Site]
    (horizon : ℕ) (error : Site → ℕ → ℝ) (nonnegative : ∀ site n, 0 ≤ error site n)
    (vanishes : ∀ site, Tendsto (error site) atTop (nhds 0))
    (passage : ℕ → ℝ) (positivePassage : ∀ n, 0 < passage n) :
    ∃ (index : ℕ → ℕ) (binding resolution : ℕ → ℝ),
      StrictMono index ∧ (∀ n, 0 < binding n) ∧ (∀ n, binding n < 1) ∧
        (∀ n, 0 < resolution n) ∧ (∀ n, resolution n < 1) ∧
        Tendsto binding atTop (nhds 0) ∧ Tendsto resolution atTop (nhds 0) ∧
        Tendsto (fun n => binding n / passage (index n)) atTop (nhds 0) ∧
        ∀ site depth, depth ≤ horizon →
          Tendsto (fun n => error site (index n) / resolution n ^ depth) atTop (nhds 0) := by
  let resolution := fun n : ℕ => 1 / ((n : ℝ) + 2)
  have resolutionPositive (n : ℕ) : 0 < resolution n := by dsimp [resolution]; positivity
  have resolutionBelow (n : ℕ) : resolution n < 1 := by
    dsimp [resolution]
    rw [div_lt_one (by positivity)]
    have nonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have resolutionVanishes : Tendsto resolution atTop (nhds 0) := by
    apply squeeze_zero (fun n => (resolutionPositive n).le)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    dsimp [resolution]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨index, increasing, small⟩ := finite_errors_below_budget error vanishes
    (fun n => resolution n ^ (horizon + 1)) (fun n => pow_pos (resolutionPositive n) _)
  obtain ⟨binding, bindingPositive, bindingBelow, bindingVanishes, bindingRelative⟩ :=
    exists_deferralWeights_faster (fun n => passage (index n))
      (fun n => positivePassage (index n))
  refine ⟨index, binding, resolution, increasing, bindingPositive, bindingBelow,
    resolutionPositive, resolutionBelow, bindingVanishes, resolutionVanishes, bindingRelative, ?_⟩
  intro site depth within
  apply squeeze_zero (fun n => div_nonneg (nonnegative site _) (pow_nonneg
    (resolutionPositive n).le _)) (fun n => ?_) resolutionVanishes
  rw [div_le_iff₀ (pow_pos (resolutionPositive n) depth)]
  calc
    error site (index n) ≤ resolution n ^ (horizon + 1) := (small n site).le
    _ ≤ resolution n ^ (depth + 1) :=
      pow_le_pow_of_le_one (resolutionPositive n).le (resolutionBelow n).le (by omega)
    _ = resolution n * resolution n ^ depth := by ring

end Vegas
