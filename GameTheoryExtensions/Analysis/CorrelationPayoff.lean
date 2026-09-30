/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # The payoff component affected by correlation

Two laws with the same marginals agree on all additive payoffs. Conversely,
only additive payoffs agree on every such pair of laws; two-by-two balanced
switches suffice to test this. For an arbitrary payoff, its centered interaction
component accounts for the entire expectation difference. No equilibrium or
runtime correspondence is assumed or concluded.
-/

noncomputable section

namespace GameTheory.CorrelationPayoff

open Math.Probability

variable {First Second : Type*}

/-- Remove the two marginal effects using fixed reference distributions. -/
def interaction (left : PMF First) (right : PMF Second)
    (payoff : First × Second → ℝ) (outcome : First × Second) : ℝ :=
  payoff outcome - expect right (fun second => payoff (outcome.1, second)) -
    expect left (fun first => payoff (first, outcome.2)) +
    expect left (fun first => expect right (fun second => payoff (first, second)))

/-- Every payoff is integrable against a finitely supported law. -/
private theorem integrable {α : Type*} {law : PMF α} (finite : law.support.Finite)
    (f : α → ℝ) : PayoffIntegrable law f :=
  payoffIntegrable_of_finite_support law f finite

theorem expect_additive_eq (first second : PMF (First × Second))
    (firstFinite : first.support.Finite) (secondFinite : second.support.Finite)
    (left : first.map Prod.fst = second.map Prod.fst)
    (right : first.map Prod.snd = second.map Prod.snd)
    (row : First → ℝ) (column : Second → ℝ) :
    expect first (fun outcome => row outcome.1 + column outcome.2) =
      expect second (fun outcome => row outcome.1 + column outcome.2) := by
  have rowEq := congrArg (fun law : PMF First => expect law row) left
  have columnEq := congrArg (fun law : PMF Second => expect law column) right
  simp only [expect_map, Function.comp_def] at rowEq columnEq
  rw [expect_add (integrable firstFinite _) (integrable firstFinite _),
    expect_add (integrable secondFinite _) (integrable secondFinite _), rowEq, columnEq]

/-- For unchanged marginals, only the interaction component contributes to
the expectation difference. The reference laws may be chosen independently. -/
theorem expectation_difference_eq_interaction
    (first second : PMF (First × Second))
    (firstFinite : first.support.Finite) (secondFinite : second.support.Finite)
    (left : first.map Prod.fst = second.map Prod.fst)
    (right : first.map Prod.snd = second.map Prod.snd)
    (referenceLeft : PMF First) (referenceRight : PMF Second)
    (payoff : First × Second → ℝ) :
    expect first payoff - expect second payoff =
      expect first (interaction referenceLeft referenceRight payoff) -
        expect second (interaction referenceLeft referenceRight payoff) := by
  have rowEq := congrArg (fun law : PMF First => expect law
    (fun row => expect referenceRight (fun col => payoff (row, col)))) left
  have columnEq := congrArg (fun law : PMF Second => expect law
    (fun col => expect referenceLeft (fun row => payoff (row, col)))) right
  simp only [expect_map, Function.comp_def] at rowEq columnEq
  have firstIntegrable := integrable firstFinite
  have secondIntegrable := integrable secondFinite
  unfold interaction
  simp only [expect_add, expect_sub, expect_constant, firstIntegrable, secondIntegrable]
  rw [rowEq, columnEq]
  ring

/-- A centered interaction has zero mean on each coordinate of the product
reference distribution. This gives the ordinary two-factor payoff decomposition. -/
theorem interaction_right_mean (left : PMF First) (right : PMF Second)
    (leftFinite : left.support.Finite) (rightFinite : right.support.Finite)
    (payoff : First × Second → ℝ) (row : First) :
    expect right (fun col => interaction left right payoff (row, col)) = 0 := by
  have rightIntegrable := integrable rightFinite
  simp only [interaction, expect_add, expect_sub, expect_constant, rightIntegrable]
  rw [expect_comm_of_support_finite right left rightFinite leftFinite]
  ring

theorem interaction_left_mean (left : PMF First) (right : PMF Second)
    (leftFinite : left.support.Finite)
    (payoff : First × Second → ℝ) (col : Second) :
    expect left (fun row => interaction left right payoff (row, col)) = 0 := by
  have leftIntegrable := integrable leftFinite
  simp only [interaction, expect_add, expect_sub, expect_constant, leftIntegrable]
  ring

/-- The gain or loss from the actual coupling, relative to the product
distribution with exactly the same marginals, is the mean interaction payoff. -/
theorem correlation_gain_eq_interaction (law : PMF (First × Second))
    (finite : law.support.Finite) (payoff : First × Second → ℝ) :
    expect law payoff -
        expect (bindPairLaw (law.map Prod.fst) (fun _ => (law.map Prod.snd))) payoff =
      expect law (interaction (law.map Prod.fst) (law.map Prod.snd) payoff) := by
  have leftFinite : (law.map Prod.fst).support.Finite := by
    rw [PMF.support_map]
    exact finite.image _
  have rightFinite : (law.map Prod.snd).support.Finite := by
    rw [PMF.support_map]
    exact finite.image _
  have productFinite :
      (bindPairLaw (law.map Prod.fst) (fun _ => law.map Prod.snd)).support.Finite := by
    rw [bindPairLaw, PMF.support_bind]
    exact leftFinite.biUnion fun first _ => by
      rw [PMF.support_map]
      exact rightFinite.image _
  rw [expectation_difference_eq_interaction law _ finite productFinite
    (bindPairLaw_map_fst _ _).symm
    (by rw [bindPairLaw_map_snd, PMF.bind_const])
    (law.map Prod.fst) (law.map Prod.snd)]
  have product : expect (bindPairLaw (law.map Prod.fst) fun _ => law.map Prod.snd)
      (interaction (law.map Prod.fst) (law.map Prod.snd) payoff) = 0 := by
    rw [bindPairLaw, expect_bind_tower _ _ _ (integrable productFinite _)]
    calc
      _ = expect (law.map Prod.fst) (fun _ => (0 : ℝ)) := by
        apply expect_congr_on_support
        intro first _
        rw [expect_map]
        exact interaction_right_mean _ _ leftFinite rightFinite payoff first
      _ = 0 := expect_constant _ _
  rw [product, sub_zero]

/-- All changes of correlation preserve a payoff exactly when it is a sum
of one-coordinate payoffs. The laws compared are the finitely supported ones;
no finiteness assumption on the carriers is needed. -/
theorem preserves_marginals_iff_additive [Nonempty First] [Nonempty Second]
    (payoff : First × Second → ℝ) :
    (∀ first second : PMF (First × Second),
      first.support.Finite → second.support.Finite →
      first.map Prod.fst = second.map Prod.fst →
      first.map Prod.snd = second.map Prod.snd →
      expect first payoff = expect second payoff) ↔
      ∃ row : First → ℝ, ∃ column : Second → ℝ,
        ∀ outcome, payoff outcome = row outcome.1 + column outcome.2 := by
  constructor
  · intro preserves
    let rowBase : First := Classical.ofNonempty
    let columnBase : Second := Classical.ofNonempty
    refine ⟨fun row => payoff (row, columnBase),
      fun col => payoff (rowBase, col) - payoff (rowBase, columnBase), ?_⟩
    rintro ⟨row, col⟩
    let diagonal := mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (row, col)) (PMF.pure (rowBase, columnBase))
    let crossed := mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (row, columnBase)) (PMF.pure (rowBase, col))
    have mixFinite (a b : First × Second) :
        (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure a) (PMF.pure b)).support.Finite :=
      (Set.toFinite ({a, b} : Set (First × Second))).subset fun value member => by
        by_cases first : value = a
        · exact Or.inl first
        · by_cases second : value = b
          · exact Or.inr second
          · rw [PMF.mem_support_iff, mix_apply, PMF.pure_apply, PMF.pure_apply] at member
            simp [first, second] at member
    have left : diagonal.map Prod.fst = crossed.map Prod.fst := by
      simp [diagonal, crossed, mix_map, PMF.pure_map]
    have right : diagonal.map Prod.snd = crossed.map Prod.snd := by
      simp only [diagonal, crossed, mix_map, PMF.pure_map]
      apply pmf_ext_toReal
      intro value
      simp only [mix_apply_toReal]
      ring
    have equal := preserves diagonal crossed (mixFinite _ _) (mixFinite _ _) left right
    simp only [diagonal, crossed, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _)
      (payoffIntegrable_pure _ _), expect_pure] at equal
    linarith
  · rintro ⟨row, column, representation⟩ first second firstFinite secondFinite left right
    have same : payoff = fun outcome => row outcome.1 + column outcome.2 :=
      funext representation
    rw [same]
    exact expect_additive_eq first second firstFinite secondFinite left right row column

end GameTheory.CorrelationPayoff
