/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.EnforcementSynthesis

/-! # Exact finite sanction inference

These examples evaluate the executable checker, exercise zero-collection
rows, and apply its least-deposit guarantee to arbitrary real candidates.
-/

namespace GameTheoryExtensionsTests.EnforcementSynthesis

open GameTheory GameTheory.Enforcement GameTheory.Math.Probability

theorem empty_deposit :
    inferScalarDeposit (∅ : Finset Bool) (fun _ => 3) (fun _ => 0) = some 0 := by
  decide

def gain (row : Bool) : ℚ := if row then 3 / 2 else 5 / 2

def collection (row : Bool) : ℚ := if row then 2 / 3 else 5

theorem fractional_deposit :
    inferScalarDeposit Finset.univ gain collection = some (9 / 4) := by
  decide +kernel

theorem collection_nonnegative (row : Bool) : 0 ≤ collection row := by
  cases row <;> norm_num [collection]

theorem fractional_deposit_le_every_real_solution {deposit : ℝ}
    (nonnegative : 0 ≤ deposit)
    (deters : ∀ row, (gain row : ℝ) ≤ (collection row : ℝ) * deposit) :
    (9 / 4 : ℝ) ≤ deposit := by
  have bound := inferred_deposit_minimal Finset.univ gain collection
    (fun row _ => collection_nonnegative row) fractional_deposit nonnegative
    (fun row _ => deters row)
  norm_num at bound ⊢
  exact bound

theorem harmless_zero_collection :
    inferScalarDeposit Finset.univ (fun row : Bool => if row then -1 else 2)
      (fun row => if row then 0 else 1 / 2) = some 4 := by
  decide +kernel

theorem profitable_zero_collection :
    inferScalarDeposit Finset.univ (fun row : Bool => if row then 1 else 2)
      (fun row => if row then 0 else 1 / 2) = none := by
  decide +kernel

theorem rejected_table_has_no_real_solution :
    ¬ ∃ deposit : ℝ, ∀ row : Bool,
      ((if row then 1 else 2 : ℚ) : ℝ) ≤
        ((if row then 0 else 1 / 2 : ℚ) : ℝ) * deposit := by
  have rejected := rejected_deposit_infeasible Finset.univ
    (fun row : Bool => if row then 1 else 2)
    (fun row => if row then 0 else 1 / 2) profitable_zero_collection
  simpa only [Finset.mem_univ, forall_const] using rejected

noncomputable section

def comparison : IncentiveComparison Bool := ⟨FinDist.pure false, FinDist.pure true⟩

def base (outcome : Bool) : ℝ := if outcome then 3 / 2 else 0

/-- The executable result discharges the actual distribution comparison. -/
theorem inferred_comparison :
    comparison.Holds (sanctionedUtility base {true} (3 / 2)) := by
  have inferred : inferScalarDeposit (Finset.univ : Finset Unit)
      (fun _ => 3 / 2) (fun _ => 1) = some (3 / 2) := by decide +kernel
  have result := inferred_deposit_holds (Finset.univ : Finset Unit)
    (fun _ => 3 / 2) (fun _ => 1) (by simp) inferred
    (fun _ => comparison) base {true} (index := ())
  apply (by norm_num at result; exact result)
  · norm_num [comparison, base, FinDist.expect_pure]
  · norm_num [comparison, FinDist.probOf_singleton, FinDist.prob_pure_eq_ite]

end

end GameTheoryExtensionsTests.EnforcementSynthesis
