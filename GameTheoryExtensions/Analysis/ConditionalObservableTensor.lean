/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.PrivateTranscriptWeights
import GameTheory.Math.Probability.ExpectationConditioning

/-! # Tensor certificates for conditional observable comparisons

The tensor of the two actual observation-filtered action kernels computes
products of unnormalized moments. A signed terminal observable therefore
computes the cross-product of the two conditional numerators and masses.
Observation masses need not agree; their positivity remains explicit.
-/

noncomputable section

namespace GameTheory.Protocol.PrivateStrategy

open GameTheory.Math.Probability GameTheory.Math.InvariantObservables

variable {Source Target Input Output : Type*} [Finite Source] [Finite Target]

open Classical in
/-- The tensor of two unnormalized observed action operators. Both branches
must produce the specified input, and the actual transition laws are retained. -/
def observedTensorOperator (sourceObserve : Source → Input) (targetObserve : Target → Input)
    (sourceStep : Source → Output → PMF Source) (targetStep : Target → Output → PMF Target)
    (label : Input × Output) : (Source × Target → ℝ) →ₗ[ℝ] (Source × Target → ℝ) where
  toFun value state := if sourceObserve state.1 = label.1 ∧ targetObserve state.2 = label.1 then
    expect (bindPairLaw (sourceStep state.1 label.2) (fun _ => targetStep state.2 label.2)) value
    else 0
  map_add' first second := by
    classical
    funext state
    dsimp
    split
    · exact expect_add_of_finite _ _ _
    · simp
  map_smul' scalar value := by
    classical
    funext state
    dsimp
    split
    · exact expect_const_mul
    · simp

theorem observedTensorOperator_product
    (sourceObserve : Source → Input) (targetObserve : Target → Input)
    (sourceStep : Source → Output → PMF Source) (targetStep : Target → Output → PMF Target)
    (label : Input × Output) (first : Source → ℝ) (second : Target → ℝ) :
    observedTensorOperator sourceObserve targetObserve sourceStep targetStep label
        (fun state => first state.1 * second state.2) =
      fun state => observedOperator sourceObserve sourceStep label first state.1 *
        observedOperator targetObserve targetStep label second state.2 := by
  classical
  funext state
  simp only [observedTensorOperator, observedOperator, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases sourceMatch : sourceObserve state.1 = label.1 <;>
    by_cases targetMatch : targetObserve state.2 = label.1 <;>
    simp only [sourceMatch, targetMatch, and_self, and_false, false_and,
      ↓reduceIte, mul_zero, zero_mul]
  rw [expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  simp only [expect_const_mul, expect_mul_const]

/-- Products of the actual unnormalized source/target word moments are
represented by one tensor word, with the same chronological label ordering. -/
theorem observedTensor_word_product
    (sourceObserve : Source → Input) (targetObserve : Target → Input)
    (sourceStep : Source → Output → PMF Source) (targetStep : Target → Output → PMF Target)
    (labels : List (Input × Output)) (first : Source → ℝ) (second : Target → ℝ) :
    word (observedTensorOperator sourceObserve targetObserve sourceStep targetStep) labels
        (fun state => first state.1 * second state.2) =
      fun state => word (observedOperator sourceObserve sourceStep) labels first state.1 *
        word (observedOperator targetObserve targetStep) labels second state.2 := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
      simpa only [word_cons, ih] using observedTensorOperator_product sourceObserve targetObserve
        sourceStep targetStep label
        (word (observedOperator sourceObserve sourceStep) rest first)
        (word (observedOperator targetObserve targetStep) rest second)

theorem expect_tensor_product (source : PMF Source) (target : PMF Target)
    (first : Source → ℝ) (second : Target → ℝ) :
    expect (bindPairLaw source (fun _ => target)) (fun state => first state.1 * second state.2) =
      expect source first * expect target second := by
  rw [expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  simp only [expect_const_mul, expect_mul_const]

/-- The signed tensor observable computes the exact conditional cross-product.
It does not require equality of the two observation masses. -/
theorem observedTensor_word_difference
    (sourceObserve : Source → Input) (targetObserve : Target → Input)
    (sourceStep : Source → Output → PMF Source) (targetStep : Target → Output → PMF Target)
    (source : PMF Source) (target : PMF Target)
    (first : Source → ℝ) (second : Target → ℝ) (labels : List (Input × Output)) :
    expect (bindPairLaw source (fun _ => target))
        (word (observedTensorOperator sourceObserve targetObserve sourceStep targetStep) labels
          (fun state => first state.1 - second state.2)) =
      expect source (word (observedOperator sourceObserve sourceStep) labels first) *
          expect target (word (observedOperator targetObserve targetStep) labels (fun _ => 1)) -
        expect source (word (observedOperator sourceObserve sourceStep) labels (fun _ => 1)) *
          expect target (word (observedOperator targetObserve targetStep) labels second) := by
  have splitValue : (fun state : Source × Target => first state.1 - second state.2) =
      (fun state => first state.1 * (1 : ℝ)) - (fun state => (1 : ℝ) * second state.2) := by
    funext state
    simp
  rw [splitValue, map_sub]
  change expect _ (fun state => _ - _) = _
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    observedTensor_word_product sourceObserve targetObserve sourceStep targetStep labels first
      (fun _ => 1),
    observedTensor_word_product sourceObserve targetObserve sourceStep targetStep labels
      (fun _ => 1) second,
    expect_tensor_product, expect_tensor_product]

private def expectationFunctional {State : Type*} [Finite State] (law : PMF State) :
    (State → ℝ) →ₗ[ℝ] ℝ where
  toFun := expect law
  map_add' first second := expect_add_of_finite law first second
  map_smul' _ _ := expect_const_mul

/-- A finite spanning certificate identifies the conditional observable for
every common label word with positive source and target observation mass.
The masses themselves may differ. Every supplied label operator is checked. -/
theorem observedTensor_certificate_conditional_eq {Index : Type*}
    (sourceObserve : Source → Input) (targetObserve : Target → Input)
    (sourceStep : Source → Output → PMF Source) (targetStep : Target → Output → PMF Target)
    (source : PMF Source) (target : PMF Target) (first : Source → ℝ) (second : Target → ℝ)
    (basis : Index → Source × Target → ℝ)
    (contains : (fun state => first state.1 - second state.2) ∈
      Submodule.span ℝ (Set.range basis))
    (closed : ∀ label index,
      observedTensorOperator sourceObserve targetObserve sourceStep targetStep label
        (basis index) ∈ Submodule.span ℝ (Set.range basis))
    (initial : ∀ index, expect (bindPairLaw source (fun _ => target)) (basis index) = 0)
    (labels : List (Input × Output))
    (sourcePositive : 0 <
      expect source (word (observedOperator sourceObserve sourceStep) labels (fun _ => 1)))
    (targetPositive : 0 <
      expect target (word (observedOperator targetObserve targetStep) labels (fun _ => 1))) :
    expect source (word (observedOperator sourceObserve sourceStep) labels first) /
        expect source (word (observedOperator sourceObserve sourceStep) labels (fun _ => 1)) =
      expect target (word (observedOperator targetObserve targetStep) labels second) /
        expect target (word (observedOperator targetObserve targetStep) labels (fun _ => 1)) := by
  have zero := comparison_word_eq_zero
    (observedTensorOperator sourceObserve targetObserve sourceStep targetStep) basis
    (fun _ : Unit => fun state => first state.1 - second state.2)
    (expectationFunctional (bindPairLaw source (fun _ => target)))
    (fun _ => contains) closed initial labels ()
  change expect (bindPairLaw source (fun _ => target))
    (word (observedTensorOperator sourceObserve targetObserve sourceStep targetStep) labels
      (fun state => first state.1 - second state.2)) = 0 at zero
  rw [observedTensor_word_difference] at zero
  apply (div_eq_div_iff sourcePositive.ne' targetPositive.ne').mpr
  nlinarith [zero]

/-- The tensor certificate transports the actual positive-probability Bayes
conditional expectation of a full adaptive input/output transcript. Each model
may use its own adaptive policy and have a different transcript probability. -/
theorem expect_posterior_runBehavioral_eq_of_tensor_certificate {Index : Type*}
    (sourceObserve : Source → Input) (targetObserve : Target → Input)
    (sourceStep : Source → Output → PMF Source) (targetStep : Target → Output → PMF Target)
    (source : PMF Source) (target : PMF Target)
    (sourcePolicy targetPolicy : Transcript Input Output → Input → PMF Output)
    (first : Source → ℝ) (second : Target → ℝ) (basis : Index → Source × Target → ℝ)
    (contains : (fun state => first state.1 - second state.2) ∈
      Submodule.span ℝ (Set.range basis))
    (closed : ∀ label index,
      observedTensorOperator sourceObserve targetObserve sourceStep targetStep label
        (basis index) ∈ Submodule.span ℝ (Set.range basis))
    (initial : ∀ index, expect (bindPairLaw source (fun _ => target)) (basis index) = 0)
    (labels : List (Input × Output)) (past : Transcript Input Output)
    (sourceSupported : labels.reverse ++ past ∈ (PMF.map Prod.snd
      (source.bind
        (runBehavioral sourcePolicy sourceObserve sourceStep labels.length past))).support)
    (targetSupported : labels.reverse ++ past ∈ (PMF.map Prod.snd
      (target.bind
        (runBehavioral targetPolicy targetObserve targetStep labels.length past))).support) :
    expect (fiberPosterior
        (source.bind (runBehavioral sourcePolicy sourceObserve sourceStep labels.length past))
        Prod.snd (labels.reverse ++ past)) (fun result => first result.1) =
      expect (fiberPosterior
        (target.bind (runBehavioral targetPolicy targetObserve targetStep labels.length past))
        Prod.snd (labels.reverse ++ past)) (fun result => second result.1) := by
  rw [expect_posterior_runBehavioral_transcript source sourcePolicy sourceObserve sourceStep
    labels past first sourceSupported,
    expect_posterior_runBehavioral_transcript target targetPolicy targetObserve targetStep
      labels past second targetSupported]
  exact observedTensor_certificate_conditional_eq sourceObserve targetObserve sourceStep targetStep
    source target first second basis contains closed initial labels
    (supported_transcript_factors_positive source sourcePolicy sourceObserve sourceStep labels
      past sourceSupported).2
    (supported_transcript_factors_positive target targetPolicy targetObserve targetStep labels
      past targetSupported).2

end GameTheory.Protocol.PrivateStrategy
