/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.ConditionalObservableTensor

/-! # Unequal observation masses with exact conditional payoff transport

An observed bit has a variable prior, independent of a hidden reward bit with
probability three quarters. Responses retain or flip the reward bit. A three
column tensor certificate handles every adaptive policy and every supported
complete transcript. The observable's law and probability need not agree.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ConditionalObservableTensor

open GameTheory.Protocol.PrivateStrategy GameTheory.Math.Probability
  GameTheory.Math.InvariantObservables

abbrev State := Bool × Bool

def observe (state : State) : Bool := state.1

def advance (state : State) (action : Bool) : PMF State :=
  PMF.pure (action, if action then state.2 else !state.2)

def value (state : State) : ℝ := if state.2 then 1 else 0

def prior (rate : Set.Icc (0 : ℝ) 1) : PMF State :=
  mix rate.1 rate.2.1 rate.2.2
    (mix (3 / 4) (by norm_num) (by norm_num) (PMF.pure (true, true))
      (PMF.pure (true, false)))
    (mix (3 / 4) (by norm_num) (by norm_num) (PMF.pure (false, true))
      (PMF.pure (false, false)))

def difference (state : State × State) : ℝ := value state.1 - value state.2

/-- The seed and its two observation-filtered columns close under all labels. -/
def basis : Option Bool → State × State → ℝ
  | none, state => difference state
  | some bit, state => if state.1.1 = bit ∧ state.2.1 = bit then difference state else 0

def space : Submodule ℝ (State × State → ℝ) := Submodule.span ℝ (Set.range basis)

theorem basis_mem (index : Option Bool) : basis index ∈ space :=
  Submodule.subset_span ⟨index, rfl⟩

theorem operator_basis (label : Bool × Bool) (index : Option Bool) :
    observedTensorOperator observe observe advance advance label (basis index) =
      (if index = none ∨ index = some label.2 then
        (if label.2 then (1 : ℝ) else -1) else 0) • basis (some label.1) := by
  funext state
  rcases state with ⟨⟨firstVisible, firstReward⟩, ⟨secondVisible, secondReward⟩⟩
  rcases label with ⟨input, action⟩
  cases index with
  | none => cases firstVisible <;> cases firstReward <;> cases secondVisible <;>
      cases secondReward <;> cases input <;> cases action <;>
      norm_num [observedTensorOperator, observe, advance, bindPairLaw, expect_pure,
        basis, difference, value, PMF.pure_map]
  | some bit => cases bit <;> cases firstVisible <;> cases firstReward <;> cases secondVisible <;>
      cases secondReward <;> cases input <;> cases action <;>
      norm_num [observedTensorOperator, observe, advance, bindPairLaw, expect_pure,
        basis, difference, value, PMF.pure_map]

theorem closed (label : Bool × Bool) (index : Option Bool) :
    observedTensorOperator observe observe advance advance label (basis index) ∈ space := by
  rw [operator_basis]
  exact space.smul_mem _ (basis_mem _)

theorem initial (sourceRate targetRate : Set.Icc (0 : ℝ) 1) (index : Option Bool) :
    expect (bindPairLaw (prior sourceRate) (fun _ => prior targetRate)) (basis index) = 0 := by
  rw [expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  cases index with
  | none =>
      simp [prior, expect_mix_of_finite, expect_pure, basis, difference, value]
      ring
  | some bit =>
      cases bit <;>
        simp [prior, expect_mix_of_finite, expect_pure, basis, difference, value] <;>
          ring_nf <;> simp

/-- One symbolic certificate covers independently chosen priors and policies.
In particular it applies pointwise along any common approximation parameter. -/
theorem adaptive_conditional_value_eq
    (sourceRate targetRate : Set.Icc (0 : ℝ) 1)
    (sourcePolicy targetPolicy : Transcript Bool Bool → Bool → PMF Bool)
    (labels : List (Bool × Bool)) (past : Transcript Bool Bool)
    (sourceSupported : labels.reverse ++ past ∈ (PMF.map Prod.snd
      ((prior sourceRate).bind
        (runBehavioral sourcePolicy observe advance labels.length past))).support)
    (targetSupported : labels.reverse ++ past ∈ (PMF.map Prod.snd
      ((prior targetRate).bind
        (runBehavioral targetPolicy observe advance labels.length past))).support) :
    expect (fiberPosterior ((prior sourceRate).bind
        (runBehavioral sourcePolicy observe advance labels.length past))
        Prod.snd (labels.reverse ++ past)) (fun result => value result.1) =
      expect (fiberPosterior ((prior targetRate).bind
        (runBehavioral targetPolicy observe advance labels.length past))
        Prod.snd (labels.reverse ++ past)) (fun result => value result.1) :=
  expect_posterior_runBehavioral_eq_of_tensor_certificate observe observe advance advance
    (prior sourceRate) (prior targetRate) sourcePolicy targetPolicy value value basis
    (basis_mem none) closed (initial sourceRate targetRate) labels past
    sourceSupported targetSupported

def policy (_ : Transcript Bool Bool) (_ : Bool) : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

theorem one_step_mass (rate : Set.Icc (0 : ℝ) 1) (action : Bool) :
    (((prior rate).bind (runBehavioral policy observe advance 1 [])).map Prod.snd
      [(true, action)]).toReal = rate.1 / 2 := by
  rw [← expect_transcriptScore_one]
  change expect _ (transcriptScore ([(true, action)].reverse ++ []) (fun _ => 1)) = _
  have factored := expect_initial_runBehavioral_transcriptScore (prior rate) policy observe
    advance [(true, action)] [] (fun _ => 1)
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at factored
  rw [factored]
  cases action <;>
    norm_num [transcriptFactor, policy, mix_apply_toReal, toReal_pure_apply,
      prior, expect_mix_of_finite, expect_pure, observedOperator, observe, advance] <;> ring

theorem one_step_supported (rate : Set.Icc (0 : ℝ) 1) (positive : 0 < rate.1)
    (action : Bool) :
    [(true, action)] ∈ (((prior rate).bind
      (runBehavioral policy observe advance 1 [])).map Prod.snd).support := by
  apply pmf_toReal_pos_iff.mp
  rw [one_step_mass]
  positivity

/-- The retained response has conditional reward three quarters; flipping it
has reward one quarter, even when this transcript is arbitrarily rare. -/
theorem one_step_conditional_value (rate : Set.Icc (0 : ℝ) 1) (positive : 0 < rate.1)
    (action : Bool) :
    expect (fiberPosterior ((prior rate).bind
        (runBehavioral policy observe advance 1 [])) Prod.snd [(true, action)])
        (fun result => value result.1) = if action then 3 / 4 else 1 / 4 := by
  have supported := one_step_supported rate positive action
  rw [show [(true, action)] = [(true, action)].reverse ++ [] from rfl]
  have normalized := expect_posterior_runBehavioral_transcript (prior rate) policy observe
    advance [(true, action)] [] value supported
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at normalized
  rw [normalized]
  cases action <;>
    norm_num [prior, expect_mix_of_finite, expect_pure, observedOperator, observe, advance,
      value] <;> field_simp [positive.ne']

theorem one_step_strict_preference (rate : Set.Icc (0 : ℝ) 1) (positive : 0 < rate.1) :
    expect (fiberPosterior ((prior rate).bind
        (runBehavioral policy observe advance 1 [])) Prod.snd [(true, false)])
        (fun result => value result.1) <
      expect (fiberPosterior ((prior rate).bind
        (runBehavioral policy observe advance 1 [])) Prod.snd [(true, true)])
        (fun result => value result.1) := by
  rw [one_step_conditional_value rate positive, one_step_conditional_value rate positive]
  norm_num

/-- Both models use the same approximation index, with different rare observation rates. -/
def rareRate (n : Nat) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / ((n : ℝ) + 2), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]⟩

def halfRareRate (n : Nat) : Set.Icc (0 : ℝ) 1 :=
  ⟨(rareRate n).1 / 2, by
    constructor
    · exact div_nonneg (rareRate n).2.1 (by norm_num)
    · exact (div_le_self (rareRate n).2.1 (by norm_num)).trans (rareRate n).2.2⟩

theorem rareRate_positive (n : Nat) : 0 < (rareRate n).1 := by
  dsimp only [rareRate]
  positivity

theorem halfRareRate_positive (n : Nat) : 0 < (halfRareRate n).1 :=
  div_pos (rareRate_positive n) (by norm_num)

theorem rare_source_mass (n : Nat) (action : Bool) :
    ((((prior (rareRate n)).bind (runBehavioral policy observe advance 1 [])).map Prod.snd)
      [(true, action)]).toReal = 1 / (2 * ((n : ℝ) + 2)) := by
  rw [one_step_mass]
  dsimp only [rareRate]
  rw [div_div]
  congr 1
  ring

theorem rare_target_mass (n : Nat) (action : Bool) :
    ((((prior (halfRareRate n)).bind (runBehavioral policy observe advance 1 [])).map Prod.snd)
      [(true, action)]).toReal = 1 / (4 * ((n : ℝ) + 2)) := by
  rw [one_step_mass]
  dsimp only [halfRareRate, rareRate]
  rw [div_div, div_div]
  congr 1
  ring

/-- The actual observation masses are positive and unequal at every common index. -/
theorem rare_masses_positive_unequal (n : Nat) (action : Bool) :
    let sourceMass := ((((prior (rareRate n)).bind
      (runBehavioral policy observe advance 1 [])).map Prod.snd) [(true, action)]).toReal
    let targetMass := ((((prior (halfRareRate n)).bind
      (runBehavioral policy observe advance 1 [])).map Prod.snd) [(true, action)]).toReal
    0 < targetMass ∧ targetMass < sourceMass := by
  dsimp only
  rw [one_step_mass, one_step_mass]
  change 0 < (rareRate n).1 / 2 / 2 ∧ (rareRate n).1 / 2 / 2 < (rareRate n).1 / 2
  have positive := rareRate_positive n
  constructor <;> linarith

/-- Conditional incentives survive both different normalizers along the entire rare family. -/
theorem rare_conditional_values (n : Nat) (action : Bool) :
    expect (fiberPosterior ((prior (rareRate n)).bind
        (runBehavioral policy observe advance 1 [])) Prod.snd [(true, action)])
        (fun result => value result.1) = (if action then 3 / 4 else 1 / 4) ∧
      expect (fiberPosterior ((prior (halfRareRate n)).bind
        (runBehavioral policy observe advance 1 [])) Prod.snd [(true, action)])
        (fun result => value result.1) = (if action then 3 / 4 else 1 / 4) :=
  ⟨one_step_conditional_value _ (rareRate_positive n) action,
    one_step_conditional_value _ (halfRareRate_positive n) action⟩

theorem rareRate_vanishes : Filter.Tendsto (fun n => (rareRate n).1)
    Filter.atTop (nhds 0) := by
  have shifted : Filter.Tendsto (fun n : Nat => 1 / ((n + 2 : Nat) : ℝ))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 2).2 tendsto_one_div_atTop_nhds_zero_nat
  simpa only [rareRate, Nat.cast_add, Nat.cast_ofNat] using shifted

/-- Both actual transcript probabilities vanish, while the conditional gap stays one half. -/
theorem rare_masses_vanish (action : Bool) :
    Filter.Tendsto (fun n => ((((prior (rareRate n)).bind
        (runBehavioral policy observe advance 1 [])).map Prod.snd) [(true, action)]).toReal)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ((((prior (halfRareRate n)).bind
        (runBehavioral policy observe advance 1 [])).map Prod.snd) [(true, action)]).toReal)
        Filter.atTop (nhds 0) := by
  constructor
  · simpa only [one_step_mass, zero_div] using rareRate_vanishes.div_const 2
  · simpa only [one_step_mass, halfRareRate, zero_div] using
      (rareRate_vanishes.div_const 2).div_const 2

end GameTheoryExtensionsTests.ConditionalObservableTensor
