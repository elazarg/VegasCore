/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.QuasilinearBounds
import GameTheoryExtensions.Analysis.QuasilinearSettlement

/-! # Unfinished outcomes and valuation-sensitive exit utility

Every completed outcome has positive valuation and a positive transfer. With a
deposit of four, the charged unfinished payoff is minus four, below every
completed payoff. A separate example holds exit cash fixed while varying the
valuation retained by the outcome.
-/

noncomputable section

namespace GameTheoryExtensionsTests.QuasilinearBounds

open GameTheory

private def valuation (outcome : Bool) : ℝ := if outcome then 5 else 3

private def transfer (outcome : Bool) : ℝ := if outcome then 11 else 7

private def payoff (output : Option Bool) (charged : Bool) : ℝ :=
  output.elim 0 (fun outcome => valuation outcome + transfer outcome) -
    (if charged then 4 else 0)

/-- Applying the generic declared-bound theorem gives the full interval,
including the charged unfinished outcome. -/
theorem payoff_bounds (output : Option Bool) (charged : Bool) :
    -4 ≤ payoff output charged ∧ payoff output charged ≤ 16 := by
  have bounds := optional_monetary_payoff_bounds valuation transfer 3 5 7 11 4 4
    (by intro outcome; cases outcome <;> norm_num [valuation])
    (by intro outcome; cases outcome <;> norm_num [transfer])
    (by norm_num) (by norm_num) output charged
  norm_num at bounds
  simpa [payoff] using bounds

/-- Both endpoints of this bound are attained, so neither can be tightened
while still covering unfinished execution and both charge verdicts. -/
theorem payoff_endpoints :
    payoff none true = -4 ∧ payoff (some true) false = 16 := by
  norm_num [payoff, valuation, transfer]

/-- The lower bound inferred from completed outcomes alone excludes an actual
unfinished payoff, even though every completed charged payoff is positive. -/
theorem completed_only_bound_excludes_unfinished :
    (∀ outcome charged, 6 ≤ payoff (some outcome) charged) ∧
      ¬ 6 ≤ payoff none true := by
  constructor
  · intro outcome charged
    cases outcome <;> cases charged <;> norm_num [payoff, valuation, transfer]
  · norm_num [payoff]

private def exitObservation (outcome : Bool) : Bool × (Unit → ℝ) :=
  (outcome, fun _ => 2)

private def exitValuation (outcome : Bool) (_who : Unit) : ℝ :=
  if outcome then 9 else 1

/-- Identical exit cash gives utilities three and eleven when the retained
outcomes have valuations one and nine. Constant cash does not determine utility. -/
theorem same_exit_cash_different_utility :
    (exitObservation false).2 = (exitObservation true).2 ∧
      monetaryUtility exitValuation (exitObservation false) () = 3 ∧
      monetaryUtility exitValuation (exitObservation true) () = 11 ∧
      monetaryUtility exitValuation (exitObservation false) () <
        monetaryUtility exitValuation (exitObservation true) () := by
  constructor
  · rfl
  · norm_num [monetaryUtility, exitObservation, exitValuation]

end GameTheoryExtensionsTests.QuasilinearBounds
