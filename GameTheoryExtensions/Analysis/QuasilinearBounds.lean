/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Bounds for quasi-linear payoffs with an optional terminal outcome

Valuation and transfers have separate declared bounds. An unfinished outcome
contributes zero before a possible deposit deduction, so the final interval must
include both zero and the completed-outcome interval before accounting for cash
collection. No execution model or independence assumption is needed.
-/

namespace GameTheory

/-- Separate valuation, transfer, and collectible-deposit bounds control every
completed or unfinished payoff and either audit verdict. -/
theorem optional_monetary_payoff_bounds {Outcome : Type*}
    (valuation transfer : Outcome → ℝ)
    (valuationLow valuationHigh transferLow transferHigh deposit depositBound : ℝ)
    (valuation_bounds : ∀ outcome,
      valuationLow ≤ valuation outcome ∧ valuation outcome ≤ valuationHigh)
    (transfer_bounds : ∀ outcome,
      transferLow ≤ transfer outcome ∧ transfer outcome ≤ transferHigh)
    (nonnegative : 0 ≤ deposit) (bounded : deposit ≤ depositBound)
    (output : Option Outcome) (charged : Bool) :
    min 0 (valuationLow + transferLow) - depositBound ≤
        output.elim 0 (fun outcome => valuation outcome + transfer outcome) -
          (if charged then deposit else 0) ∧
      output.elim 0 (fun outcome => valuation outcome + transfer outcome) -
          (if charged then deposit else 0) ≤ max 0 (valuationHigh + transferHigh) := by
  have base_bounds :
      min 0 (valuationLow + transferLow) ≤
          output.elim 0 (fun outcome => valuation outcome + transfer outcome) ∧
        output.elim 0 (fun outcome => valuation outcome + transfer outcome) ≤
          max 0 (valuationHigh + transferHigh) := by
    cases output with
    | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
    | some outcome =>
        exact ⟨(min_le_right _ _).trans
          (add_le_add (valuation_bounds outcome).1 (transfer_bounds outcome).1),
          (add_le_add (valuation_bounds outcome).2 (transfer_bounds outcome).2).trans
            (le_max_right _ _)⟩
  have charged_bounds : 0 ≤ (if charged then deposit else 0) ∧
      (if charged then deposit else 0) ≤ depositBound := by
    cases charged
    · simpa using And.intro (le_refl (0 : ℝ)) (nonnegative.trans bounded)
    · simpa using And.intro nonnegative bounded
  constructor <;> linarith [base_bounds.1, base_bounds.2,
    charged_bounds.1, charged_bounds.2]

end GameTheory
