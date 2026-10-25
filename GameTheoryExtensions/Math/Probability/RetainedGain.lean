/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.Expectation
import Mathlib.Tactic.Linarith

/-! # Gain bounds from retained payoff and residual continuation value

The residual comparison removes the part of a payoff outside a retained
continuation. Averaging preserves the resulting bound under joint payoff
integrability, without finiteness of either carrier or support.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- A residual comparison bounds the gain by its retained component, with a
bounded loss on the bad event and a separate additive comparison error. -/
theorem retained_gain_le {α : Type*}
    (baseline : PMF α) (mean retained : α → ℝ) (residual : α → Bool → ℝ)
    (bad : Prop) [Decidable bad] (bound flag gain : ℝ) (choice : α) (keep : Bool)
    (nonnegative : 0 ≤ bound) (meanBound : ∀ selected, |mean selected| ≤ bound)
    (residualIntegrable : PayoffIntegrable baseline (fun selected => residual selected true))
    (retainedEq : ∀ selected, retained selected =
      if bad then 0 else mean selected - residual selected true)
    (residualFalse : ∀ selected, residual selected false = mean selected)
    (flags : gain ≤ mean choice - expect baseline mean + flag)
    (comparison : ¬ bad → residual choice keep ≤
      expect baseline (fun selected => residual selected keep)) :
    gain ≤ (if keep = true then retained choice - expect baseline retained else 0) +
      (if bad then 2 * bound else 0) + flag := by
  by_cases failed : bad
  · have zero : retained = fun _ => 0 := funext (fun selected => by
      rw [retainedEq selected, ite_eq_left failed])
    have lower := expect_abs_le_of_bounded (μ := baseline) nonnegative meanBound
    rw [zero, expect_constant]
    simp only [sub_self, ite_self, failed, ite_true]
    linarith only [flags, (abs_le.mp (meanBound choice)).2, (abs_le.mp lower).1]
  · have ordered := comparison failed
    cases keep with
    | false =>
        have clean : (fun selected => residual selected false) = mean := funext residualFalse
        rw [residualFalse, clean] at ordered
        simp only [Bool.false_eq_true, ite_false, failed, zero_add]
        linarith only [flags, ordered]
    | true =>
        have kept : retained = fun selected => mean selected - residual selected true :=
          funext (fun selected => by rw [retainedEq selected, ite_eq_right failed])
        simp only [ite_true, failed, ite_false, add_zero]
        rw [kept, expect_sub (payoffIntegrable_of_bounded baseline mean meanBound)
          residualIntegrable]
        linarith only [flags, ordered]

/-- Joint integrability lets belief and baseline averaging commute. A selected
choice outside the baseline support needs its own column integrability premise. -/
theorem expect_retained_gain_le {α β : Type*}
    (belief : PMF α) (baseline : PMF β) (gain : α → ℝ) (retained : α → β → ℝ)
    (qualified : β → ℝ) (penalty : α → ℝ) (flag : ℝ) (choice : β) (keep : Bool)
    (gainIntegrable : PayoffIntegrable belief gain)
    (penaltyIntegrable : PayoffIntegrable belief penalty)
    (choiceIntegrable : PayoffIntegrable belief (fun history => retained history choice))
    (jointIntegrable : PayoffIntegrable
      (belief.bind fun history => baseline.map fun selected => (history, selected))
      (fun pair => retained pair.1 pair.2))
    (mean : ∀ selected, qualified selected =
      expect belief (fun history => retained history selected))
    (pointwise : ∀ history, gain history ≤
      (if keep = true then retained history choice - expect baseline (retained history) else 0) +
        penalty history + flag) :
    expect belief gain ≤
      (if keep = true then qualified choice - expect baseline qualified else 0) +
        expect belief penalty + flag := by
  let payoff : α × β → ℝ := fun pair => retained pair.1 pair.2
  have exchanged :
      (belief.bind fun history => baseline.map fun selected => (history, selected)) =
        baseline.bind fun selected => belief.map fun history => (history, selected) := by
    simp only [← PMF.bind_pure_comp, Function.comp_def]
    exact PMF.bind_comm belief baseline (fun history selected => PMF.pure (history, selected))
  have reverseIntegrable : PayoffIntegrable
      (baseline.bind fun selected => belief.map fun history => (history, selected)) payoff :=
    exchanged ▸ jointIntegrable
  have forward := expect_bind_tower belief
    (fun history => baseline.map fun selected => (history, selected)) payoff jointIntegrable
  have reverse := expect_bind_tower baseline
    (fun selected => belief.map fun history => (history, selected)) payoff reverseIntegrable
  simp only [expect_map, Function.comp_def, payoff] at forward reverse
  have average : expect belief (fun history => expect baseline (retained history)) =
      expect baseline qualified := by
    rw [← forward, exchanged, reverse]
    exact expect_congr_on_support (fun selected _ => (mean selected).symm)
  have averageIntegrable :
      PayoffIntegrable belief (fun history => expect baseline (retained history)) := by
    have integrated := payoffIntegrable_bind_conditionalExpectation belief
      (fun history => baseline.map fun selected => (history, selected)) payoff jointIntegrable
    simpa only [expect_map, Function.comp_def, payoff] using integrated
  have keptIntegrable : PayoffIntegrable belief (fun history =>
      if keep = true then retained history choice - expect baseline (retained history) else 0) := by
    cases keep with
    | false => exact payoffIntegrable_zero belief
    | true => exact payoffIntegrable_sub choiceIntegrable averageIntegrable
  apply le_trans (expect_mono (fun history _ => pointwise history) gainIntegrable
    (payoffIntegrable_add (payoffIntegrable_add keptIntegrable penaltyIntegrable)
      (payoffIntegrable_constant belief flag)))
  cases keep with
  | false =>
      simp only [Bool.false_eq_true, ite_false, zero_add]
      rw [expect_add penaltyIntegrable (payoffIntegrable_constant belief flag), expect_constant]
  | true =>
      simp only [ite_true]
      rw [expect_add
          (payoffIntegrable_add (payoffIntegrable_sub choiceIntegrable averageIntegrable)
            penaltyIntegrable) (payoffIntegrable_constant belief flag),
        expect_add (payoffIntegrable_sub choiceIntegrable averageIntegrable) penaltyIntegrable,
        expect_sub choiceIntegrable averageIntegrable, expect_constant, average, ← mean choice]

end GameTheory.Math.Probability
