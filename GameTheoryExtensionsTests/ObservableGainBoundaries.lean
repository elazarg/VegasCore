/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.ObservableGainTransport
import GameTheoryExtensions.Math.Probability.TotalVariation
import GameTheoryExtensions.Math.Probability.ObservableMoments
import Mathlib.Tactic.NormNum

/-! # Finite boundaries of gain and information transport -/

noncomputable section

namespace GameTheoryExtensionsTests.ObservableGainTransport

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

private def fair : PMF Bool :=
  mix (1 / 2 : ℝ) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

private theorem expect_fair (value : Bool → ℝ) :
    expect fair value = (value false + value true) / 2 := by
  simp only [fair, expect_mix_of_finite, expect_pure]
  ring

private def pairFair : PMF (Bool × Bool) := bindPairLaw fair (fun _ => fair)

private theorem expect_pair (value : Bool × Bool → ℝ) :
    expect pairFair value =
      (value (false, false) + value (false, true) +
        value (true, false) + value (true, true)) / 4 := by
  unfold pairFair bindPairLaw
  rw [expect_bind_of_finite]
  simp only [expect_map, expect_fair, Function.comp_def]
  ring

private theorem fair_apply (bit : Bool) : (fair bit).toReal = 1 / 2 := by
  cases bit <;> norm_num [fair, mix_apply, PMF.pure_apply]

private theorem pairFair_apply (state : Bool × Bool) : (pairFair state).toReal = 1 / 4 := by
  rw [pairFair, bindPairLaw_apply, ENNReal.toReal_mul, fair_apply, fair_apply]
  norm_num

private def sign (bit : Bool) : ℝ := if bit then 1 else -1

private def firstChannel (state : Bool × Bool) : PMF Bool := PMF.pure state.1

private theorem first_mass :
    expect pairFair (fun state => (firstChannel state true).toReal) = 1 / 2 := by
  rw [expect_pair]
  norm_num [firstChannel, PMF.pure_apply]

private theorem second_mean : expect pairFair (fun state => sign state.2) = 0 := by
  rw [expect_pair]
  norm_num [sign]

private theorem weighted_second :
    expect pairFair (fun state => (firstChannel state true).toReal * sign state.2) = 0 := by
  rw [expect_pair]
  norm_num [firstChannel, PMF.pure_apply, sign]

/-- A genuine observation changes the full hidden-state law while preserving
a nonconstant gain which takes both signs on the actual support. -/
theorem changed_posterior_same_gain :
    kernelPosterior pairFair firstChannel true ≠ pairFair ∧
      expect (kernelPosterior pairFair firstChannel true) (fun state => sign state.2) =
        expect pairFair (fun state => sign state.2) := by
  have positive : 0 < expect pairFair (fun state => (firstChannel state true).toReal) := by
    rw [first_mass]
    norm_num
  constructor
  · intro equal
    have atom := kernelPosterior_toReal_apply pairFair firstChannel true positive (false, false)
    rw [equal, pairFair_apply, first_mass] at atom
    norm_num [firstChannel, PMF.pure_apply] at atom
  · rw [expect_kernelPosterior pairFair firstChannel true positive _
      (payoffIntegrable_of_finite _ _), weighted_second, first_mass, second_mean]
    norm_num

private def branch (state : Bool × Bool) (choice : Bool) : PMF ℝ :=
  PMF.pure (if choice then sign state.2 else 0)

private theorem branch_integrable (choice : Bool) :
    PayoffIntegrable (pairFair.bind (fun state => branch state choice)) id :=
  payoffIntegrable_bind_of_finite pairFair _ id (fun _ => payoffIntegrable_pure _ _)

private theorem prior_value (choice : Bool) :
    (Context.ofBelief pairFair branch id).value choice = 0 := by
  change expect (pairFair.bind (fun state => branch state choice)) id = 0
  rw [expect_bind_tower pairFair _ _ (branch_integrable choice)]
  simp only [branch, expect_pure, id_eq]
  cases choice with
  | false => exact expect_zero _
  | true => exact second_mean

/-- The covariance producer is consumed by the existing local-optimality
predicate for an actual randomized continuation context, with both choices covered. -/
theorem conditional_context_stays_optimal :
    (Context.ofBelief (kernelPosterior pairFair firstChannel true) branch id).IsLocallyOptimal
      Set.univ false := by
  have positive : 0 < expect pairFair (fun state => (firstChannel state true).toReal) := by
    rw [first_mass]
    norm_num
  have source : (Context.ofBelief pairFair branch id).IsLocallyOptimal Set.univ false := by
    apply (Context.isLocallyOptimal_iff_of_integrable (ctx := Context.ofBelief pairFair branch id)
      (branch_integrable false)
      (fun choice _ => branch_integrable choice)).mpr
    intro choice _
    rw [prior_value, prior_value]
  apply Context.isLocallyOptimal_after_observation pairFair firstChannel true positive branch id
    Set.univ false (branch_integrable false) (fun choice _ => branch_integrable choice) source
  intro choice _
  dsimp only
  simp only [branch, expect_pure, id_eq, Bool.false_eq_true, ↓reduceIte, sub_zero]
  cases choice with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, expect_zero, le_refl]
  | true => simp only [↓reduceIte, weighted_second, second_mean, mul_zero, le_refl]

private def changedBranch (state : Bool × Bool) (choice : Bool) : PMF ℝ :=
  PMF.pure (if choice then sign state.2 + (if state.1 then 1 else 0) else 0)

private theorem changedBranch_integrable (choice : Bool) :
    PayoffIntegrable (pairFair.bind (fun state => changedBranch state choice)) id :=
  payoffIntegrable_bind_of_finite pairFair _ id (fun _ => payoffIntegrable_pure _ _)

/-- A changed continuation kernel adds a real incentive even though the original
nonconstant gain has zero likelihood covariance. The weighted continuation-error
term controls the actual two context gains and is attained in this example. -/
theorem changed_context_requires_continuation_error :
    let target := Context.ofBelief (kernelPosterior pairFair firstChannel true) changedBranch id
    let source := Context.ofBelief pairFair branch id
    |(target.value true - target.value false) - (source.value true - source.value false)| ≤ 1 ∧
      (target.value true - target.value false) - (source.value true - source.value false) = 1 := by
  intro target source
  have positive : 0 < expect pairFair (fun state => (firstChannel state true).toReal) := by
    rw [first_mass]
    norm_num
  have sourceGain : source.value true - source.value false =
      expect pairFair (fun state => sign state.2) := by
    rw [Context.ofBelief_gain_eq_expect pairFair branch id false true
      (branch_integrable true) (branch_integrable false)]
    simp only [branch, expect_pure, id_eq, ↓reduceIte, Bool.false_eq_true, sub_zero]
  have targetGain : target.value true - target.value false =
      expect (kernelPosterior pairFair firstChannel true)
        (fun state => sign state.2 + (if state.1 then 1 else 0)) := by
    rw [Context.ofBelief_gain_eq_expect _ changedBranch id false true
      (payoffIntegrable_bind_kernelPosterior pairFair firstChannel true positive _ id
        (changedBranch_integrable true))
      (payoffIntegrable_bind_kernelPosterior pairFair firstChannel true positive _ id
        (changedBranch_integrable false))]
    simp only [changedBranch, expect_pure, id_eq, ↓reduceIte, Bool.false_eq_true, sub_zero]
  rw [sourceGain, targetGain]
  have bounded := abs_expect_kernelPosterior_changed_gain_sub_expect_le pairFair firstChannel true
    positive (fun state => sign state.2)
    (fun state => sign state.2 + (if state.1 then 1 else 0))
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  constructor
  · convert bounded using 1
    rw [first_mass, second_mean, weighted_second, expect_pair]
    norm_num [firstChannel, PMF.pure_apply, sign]
  · rw [expect_kernelPosterior pairFair firstChannel true positive _
      (payoffIntegrable_of_finite _ _), first_mass, second_mean, expect_pair]
    norm_num [firstChannel, PMF.pure_apply, sign]

private def policyChannel (policy : Bool) (hidden : Bool) : PMF Bool :=
  if policy then PMF.pure hidden else fair

private theorem policy_mass (policy : Bool) :
    expect fair (fun hidden => (policyChannel policy hidden true).toReal) = 1 / 2 := by
  rw [expect_fair]
  cases policy <;> norm_num [policyChannel, fair_apply, PMF.pure_apply]

/-- Honest-play posterior preservation cannot discharge a quantifier over
other policies. Both observations in this example have positive mass. -/
theorem honest_only_is_insufficient :
    kernelPosterior fair (policyChannel false) true = fair ∧
      expect (kernelPosterior fair (policyChannel false) true) sign = 0 ∧
      expect (kernelPosterior fair (policyChannel true) true) sign = 1 := by
  have positive (policy : Bool) :
      0 < expect fair (fun hidden => (policyChannel policy hidden true).toReal) := by
    rw [policy_mass]
    norm_num
  have honest : kernelPosterior fair (policyChannel false) true = fair := by
    apply kernelPosterior_eq_of_constant_likelihood fair (policyChannel false) true
      (positive false) (1 / 2)
    intro hidden _
    simp only [policyChannel, Bool.false_eq_true, ↓reduceIte, fair_apply]
  refine ⟨honest, ?_, ?_⟩
  · rw [honest, expect_fair]
    norm_num [sign]
  · rw [expect_kernelPosterior fair (policyChannel true) true (positive true) sign
      (payoffIntegrable_of_finite _ _), policy_mass, expect_fair]
    norm_num [policyChannel, PMF.pure_apply, sign]

/-- The normalized covariance bound is attained by a literal finite channel. -/
theorem covariance_error_bound_is_sharp :
    |expect (kernelPosterior fair (policyChannel true) true) sign - expect fair sign| ≤ 1 ∧
      expect (kernelPosterior fair (policyChannel true) true) sign - expect fair sign = 1 := by
  have positive : 0 < expect fair (fun h => (policyChannel true h true).toReal) := by
    rw [policy_mass]
    norm_num
  have covariance : |expect fair (fun h => (policyChannel true h true).toReal * sign h) -
      expect fair (fun h => (policyChannel true h true).toReal) * expect fair sign| ≤ 1 / 2 := by
    simp only [expect_fair]
    norm_num [policyChannel, PMF.pure_apply, sign]
  have bounded := abs_expect_kernelPosterior_sub_expect_le fair (policyChannel true) true
    positive sign (payoffIntegrable_of_finite _ _) covariance
  constructor
  · convert bounded using 1
    rw [policy_mass]
    norm_num
  · rw [honest_only_is_insufficient.2.2, expect_fair]
    norm_num [sign]

private def scalarBasis (index hidden : Bool) : ℝ := if index then sign hidden else 1

private def scalarCoefficient (index : Bool) : ℝ := if index then 2 else 3

/-- A two-observable representation gives the exact dual weighted-error bound
for a continuation score, without requiring equality of the hidden laws. -/
theorem observable_span_error_is_sharp :
    |expect fair (fun h => 3 + 2 * sign h) -
      expect (PMF.pure true) (fun h => 3 + 2 * sign h)| ≤ 2 := by
  have representation (h : Bool) :
      3 + 2 * sign h = ∑ index, scalarCoefficient index * scalarBasis index h := by
    cases h <;> norm_num [Fintype.sum_bool, scalarCoefficient, scalarBasis, sign]
  have moments (index : Bool) :
      |expect fair (scalarBasis index) - expect (PMF.pure true) (scalarBasis index)| ≤
        if index then 1 else 0 := by
    rw [expect_fair, expect_pure]
    cases index <;> norm_num [scalarBasis, sign]
  have bounded := abs_expect_sub_le_of_observable_span fair (PMF.pure true) scalarBasis
    scalarBasis scalarCoefficient (fun _ => payoffIntegrable_of_finite _ _)
    (fun _ => payoffIntegrable_of_finite _ _) (fun h => 3 + 2 * sign h)
    (fun h => 3 + 2 * sign h) (fun h _ => representation h) (fun h _ => representation h)
    (fun index => if index then 1 else 0) moments
  convert bounded using 1
  norm_num [Fintype.sum_bool, scalarCoefficient]

private def eventLaw (rate : ℝ) (nonnegative : 0 ≤ rate) (small : rate ≤ 1)
    (payload : Bool) : PMF (Bool × Bool) :=
  mix rate nonnegative small (PMF.pure (true, payload)) (PMF.pure (false, false))

/-- Two positive rare observations can have unit conditional discrepancy
while their unconditioned laws are within an arbitrarily small error. -/
theorem rare_observation_amplifies (rate : ℝ) (positive : 0 < rate) (small : rate ≤ 1) :
    PMF.WithinTV (2 * rate) (eventLaw rate positive.le small true)
      (eventLaw rate positive.le small false) ∧
    (∀ payload, expect (eventLaw rate positive.le small payload)
      (fun state => (firstChannel state true).toReal) = rate) ∧
    expect (kernelPosterior (eventLaw rate positive.le small true) firstChannel true)
        (fun state => if state.2 then (1 : ℝ) else 0) -
      expect (kernelPosterior (eventLaw rate positive.le small false) firstChannel true)
        (fun state => if state.2 then (1 : ℝ) else 0) = 1 := by
  have near (payload : Bool) : PMF.WithinTV rate (eventLaw rate positive.le small payload)
      (PMF.pure (false, false)) := PMF.WithinTV.mix_right rate positive.le small _ _
  have mass (payload : Bool) : expect (eventLaw rate positive.le small payload)
      (fun state => (firstChannel state true).toReal) = rate := by
    rw [eventLaw, expect_mix_of_finite]
    norm_num [expect_pure, firstChannel, PMF.pure_apply]
  refine ⟨by simpa only [two_mul] using (near true).trans (near false).symm, mass, ?_⟩
  have observed (payload : Bool) :
      expect (kernelPosterior (eventLaw rate positive.le small payload) firstChannel true)
        (fun state => if state.2 then (1 : ℝ) else 0) = if payload then 1 else 0 := by
    rw [expect_kernelPosterior _ firstChannel true (by rw [mass]; exact positive) _
      (payoffIntegrable_of_finite _ _), mass, eventLaw, expect_mix_of_finite]
    cases payload <;>
      norm_num [expect_pure, firstChannel, PMF.pure_apply, ne_of_gt positive]
  rw [observed true, observed false]
  norm_num

private def terminalTest (state : Fin 3) : ℝ := if state = 2 then 1 else 0

private def next (state : Fin 3) : PMF (Fin 3) := PMF.pure (if state = 0 then 2 else 1)

/-- Agreement on terminal moments is not preserved by a continuation operator
which leaves that observable span. A closure premise is necessary for that route. -/
theorem terminal_basis_not_closed :
    expect (PMF.pure (0 : Fin 3)) terminalTest =
      expect (PMF.pure (1 : Fin 3)) terminalTest ∧
    expect ((PMF.pure (0 : Fin 3)).bind next) terminalTest = 1 ∧
    expect ((PMF.pure (1 : Fin 3)).bind next) terminalTest = 0 ∧
    ¬ ∃ a b : ℝ, ∀ state, expect (next state) terminalTest = a + b * terminalTest state := by
  refine ⟨by norm_num [expect_pure, terminalTest], ?_, ?_, ?_⟩
  · norm_num [PMF.pure_bind, next, expect_pure, terminalTest]
  · norm_num [PMF.pure_bind, next, expect_pure, terminalTest]
  · rintro ⟨a, b, closure⟩
    have first := closure 0
    have second := closure 1
    norm_num [next, expect_pure, terminalTest] at first second
    linarith

private def gainBasis (index : Bool) (state : Bool × Bool) : ℝ :=
  if index then sign state.2 else 1

private def fixedFirst (bit : Bool) : PMF (Bool × Bool) := fair.map (fun other => (bit, other))

private def hiddenFlip (state : Bool × Bool) : PMF (Bool × Bool) :=
  PMF.pure (!state.1, state.2)

private def identityMatrix (i j : Bool) : ℝ := if i = j then 1 else 0

private theorem gainBasis_bounded (index : Bool) (state : Bool × Bool) :
    |gainBasis index state| ≤ 1 := by
  cases index <;> cases second : state.2 <;> norm_num [gainBasis, sign, second]

/-- An actual common closed gain basis transports every finite continuation,
although the two kernels and the original full hidden-state laws differ. -/
theorem closed_gain_basis_transports_every_horizon :
    fixedFirst false ≠ fixedFirst true ∧
      ∀ count index,
        expect ((fun law => law.bind PMF.pure)^[count] (fixedFirst false)) (gainBasis index) =
          expect ((fun law => law.bind hiddenFlip)^[count] (fixedFirst true))
            (gainBasis index) := by
  have marginal (bit : Bool) : (fixedFirst bit).map Prod.fst = PMF.pure bit := by
    simp only [fixedFirst, PMF.map_comp, Function.comp_def]
    exact pmf_map_fun_const fair bit
  constructor
  · intro equal
    have same := congrArg (PMF.map Prod.fst) equal
    rw [marginal, marginal] at same
    have atom := congrArg (fun law : PMF Bool => law true) same
    norm_num [PMF.pure_apply] at atom
  · apply expect_iterate_eq_of_closed_observables (fixedFirst false) (fixedFirst true) PMF.pure
      hiddenFlip gainBasis gainBasis identityMatrix (fun _ => 1) (fun _ => 1)
      gainBasis_bounded gainBasis_bounded
    · intro index state
      cases index <;> simp [identityMatrix, expect_pure, gainBasis]
    · intro index state
      cases index <;> simp [identityMatrix, hiddenFlip, expect_pure, gainBasis]
    · intro index
      rw [fixedFirst, fixedFirst, expect_map, expect_map]
      rfl

end GameTheoryExtensionsTests.ObservableGainTransport
