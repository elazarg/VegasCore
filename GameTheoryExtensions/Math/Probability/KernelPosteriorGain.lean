/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.ExpectationContraction

/-! # Observation likelihoods and expected gains

A posterior is produced by an actual observation channel. Positive observed
mass gives a normalized likelihood density, transfers integrability, and
expresses each change of expected gain by its likelihood covariance.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

/-- Draw a hidden state, draw an observation from its channel, and retain the
hidden state conditioned on that observation. Null observations use the existing
unconditioned fallback of `fiberPosterior`. -/
def kernelPosterior {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal) : PMF State :=
  (fiberPosterior ((bindPairLaw prior channel).map Prod.swap) Prod.fst observed).map Prod.snd

private theorem joint_marginal {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) :
    ((bindPairLaw prior channel).map Prod.swap).map Prod.fst = prior.bind channel := by
  rw [PMF.map_comp]
  exact bindPairLaw_map_snd prior channel

private theorem joint_apply {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal) (state : State) :
    ((bindPairLaw prior channel).map Prod.swap) (observed, state) =
      prior state * channel state observed := by
  change ((bindPairLaw prior channel).map Prod.swap) (Prod.swap (state, observed)) = _
  rw [pmf_map_apply_of_injective _ Prod.swap_injective]
  exact bindPairLaw_apply prior channel state observed

/-- A supported channel observation tilts every original state weight by its
own likelihood, divided by the observation's actual prior mass. -/
theorem kernelPosterior_toReal_apply {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal)) (state : State) :
    (kernelPosterior prior channel observed state).toReal =
      (prior state).toReal * (channel state observed).toReal /
        expect prior (fun state => (channel state observed).toReal) := by
  have present : observed ∈ (prior.bind channel).support := by
    apply (PMF.mem_support_iff _ _).mpr
    intro zero
    have mass := toReal_bind_apply prior channel observed
    rw [zero, ENNReal.toReal_zero] at mass
    linarith
  rw [kernelPosterior, fiberPosterior_map_snd_apply _ observed
    (by simpa only [joint_marginal] using present), ENNReal.toReal_mul, ENNReal.toReal_inv,
    joint_apply, ENNReal.toReal_mul, joint_marginal, toReal_bind_apply, div_eq_mul_inv]

/-- Multiplication by the observation mass makes the posterior no larger than
the original prior, because every channel likelihood is at most one. -/
theorem kernelPosterior_weight_le {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal)) (state : State) :
    expect prior (fun state => (channel state observed).toReal) *
        (kernelPosterior prior channel observed state).toReal ≤ (prior state).toReal := by
  rw [kernelPosterior_toReal_apply prior channel observed positive]
  have scaled : expect prior (fun state => (channel state observed).toReal) *
      ((prior state).toReal * (channel state observed).toReal /
        expect prior (fun state => (channel state observed).toReal)) =
      (prior state).toReal * (channel state observed).toReal := by
    field_simp
  rw [scaled]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pmf_toReal_apply_le_one _ _)

/-- An integrable prior payoff remains integrable after a positive-probability
channel observation. No finiteness of the hidden carrier is required. -/
theorem payoffIntegrable_kernelPosterior {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (gain : State → ℝ) (integrable : PayoffIntegrable prior gain) :
    PayoffIntegrable (kernelPosterior prior channel observed) gain :=
  payoffIntegrable_of_scaled_weight_le _ prior gain _ positive
    (kernelPosterior_weight_le prior channel observed positive) integrable

/-- Multiplication by an observation likelihood preserves absolute
integrability, because a likelihood is between zero and one. -/
theorem payoffIntegrable_kernelLikelihood_mul {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal) (gain : State → ℝ)
    (integrable : PayoffIntegrable prior gain) :
    PayoffIntegrable prior (fun state => (channel state observed).toReal * gain state) := by
  apply Summable.of_nonneg_of_le
    (fun state => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)) ?_ integrable
  intro state
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_left (abs_nonneg _) (pmf_toReal_apply_le_one _ _)

/-- Integrability of a continuation under the prior survives a positive
observation before that continuation is run. -/
theorem payoffIntegrable_bind_kernelPosterior {State Signal Outcome : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (continuation : State → PMF Outcome) (payoff : Outcome → ℝ)
    (integrable : PayoffIntegrable (prior.bind continuation) payoff) :
    PayoffIntegrable ((kernelPosterior prior channel observed).bind continuation) payoff := by
  apply payoffIntegrable_of_scaled_weight_le _ (prior.bind continuation) payoff _ positive ?_
    integrable
  intro outcome
  simpa only [mul_one] using bind_supported_domination
    (kernelPosterior prior channel observed) prior continuation continuation
    (expect prior (fun state => (channel state observed).toReal)) 1 positive.le
    (kernelPosterior_weight_le prior channel observed positive)
    (fun _ _ _ => by simp only [one_mul, le_refl]) outcome

/-- The posterior expectation is the prior likelihood-weighted expectation,
with the same explicit positive normalizer as the actual observation. -/
theorem expect_kernelPosterior {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (gain : State → ℝ) (integrable : PayoffIntegrable prior gain) :
    expect (kernelPosterior prior channel observed) gain =
      expect prior (fun state => (channel state observed).toReal * gain state) /
        expect prior (fun state => (channel state observed).toReal) := by
  have weighted := payoffIntegrable_kernelLikelihood_mul prior channel observed gain integrable
  unfold expect
  simp_rw [kernelPosterior_toReal_apply prior channel observed positive]
  calc
    (∑' state, (prior state).toReal * (channel state observed).toReal /
        expect prior (fun state => (channel state observed).toReal) * gain state) =
        ∑' state, ((prior state).toReal * ((channel state observed).toReal * gain state)) *
          (expect prior (fun state => (channel state observed).toReal))⁻¹ := by
      apply tsum_congr
      intro state
      ring
    _ = _ := by
      rw [weighted.summable.tsum_mul_right]
      rfl

/-- The change in an integrable gain is its covariance with the observation
likelihood, divided by the actual observation mass. -/
theorem expect_kernelPosterior_sub_expect {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (gain : State → ℝ) (integrable : PayoffIntegrable prior gain) :
    expect (kernelPosterior prior channel observed) gain - expect prior gain =
      (expect prior (fun state => (channel state observed).toReal * gain state) -
        expect prior (fun state => (channel state observed).toReal) * expect prior gain) /
      expect prior (fun state => (channel state observed).toReal) := by
  rw [expect_kernelPosterior prior channel observed positive gain integrable]
  field_simp

/-- Nonpositive likelihood covariance suffices to preserve a nonpositive
expected gain, even when the full posterior changes. -/
theorem expect_kernelPosterior_nonpos {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (gain : State → ℝ) (integrable : PayoffIntegrable prior gain)
    (source : expect prior gain ≤ 0)
    (covariance : expect prior (fun state => (channel state observed).toReal * gain state) ≤
      expect prior (fun state => (channel state observed).toReal) * expect prior gain) :
    expect (kernelPosterior prior channel observed) gain ≤ 0 := by
  rw [expect_kernelPosterior prior channel observed positive gain integrable]
  exact div_nonpos_of_nonpos_of_nonneg
    (covariance.trans (mul_nonpos_of_nonneg_of_nonpos positive.le source)) positive.le

/-- A covariance estimate costs its relative error after conditioning. No
uniform lower bound on the observation mass is silently assumed. -/
theorem abs_expect_kernelPosterior_sub_expect_le {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (gain : State → ℝ) (integrable : PayoffIntegrable prior gain) {error : ℝ}
    (covariance : |expect prior (fun state => (channel state observed).toReal * gain state) -
      expect prior (fun state => (channel state observed).toReal) * expect prior gain| ≤ error) :
    |expect (kernelPosterior prior channel observed) gain - expect prior gain| ≤
      error / expect prior (fun state => (channel state observed).toReal) := by
  rw [expect_kernelPosterior_sub_expect prior channel observed positive gain integrable,
    abs_div, abs_of_pos positive]
  exact div_le_div_of_nonneg_right covariance positive.le

/-- If conditioning also changes the continuation gain, its likelihood-weighted
mean error is charged separately from the covariance of the original gain.
Both gains must be integrable under the prior; posterior integration is derived. -/
theorem abs_expect_kernelPosterior_changed_gain_sub_expect_le {State Signal : Type*}
    (prior : PMF State) (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (sourceGain targetGain : State → ℝ)
    (sourceIntegrable : PayoffIntegrable prior sourceGain)
    (targetIntegrable : PayoffIntegrable prior targetGain) :
    |expect (kernelPosterior prior channel observed) targetGain - expect prior sourceGain| ≤
      expect prior (fun state =>
        (channel state observed).toReal * |targetGain state - sourceGain state|) /
          expect prior (fun state => (channel state observed).toReal) +
      |expect prior (fun state => (channel state observed).toReal * sourceGain state) -
        expect prior (fun state => (channel state observed).toReal) * expect prior sourceGain| /
          expect prior (fun state => (channel state observed).toReal) := by
  have sourcePosterior :=
    payoffIntegrable_kernelPosterior prior channel observed positive sourceGain sourceIntegrable
  have targetPosterior :=
    payoffIntegrable_kernelPosterior prior channel observed positive targetGain targetIntegrable
  have errorIntegrable :
      PayoffIntegrable prior (fun state => |targetGain state - sourceGain state|) := by
    simpa only [PayoffIntegrable, abs_abs] using
      payoffIntegrable_sub targetIntegrable sourceIntegrable
  have continuationError := abs_expect_sub_le_expect_abs_sub
    (kernelPosterior prior channel observed) targetGain sourceGain targetPosterior sourcePosterior
  rw [expect_kernelPosterior prior channel observed positive _ errorIntegrable] at continuationError
  have covariance := expect_kernelPosterior_sub_expect prior channel observed positive
    sourceGain sourceIntegrable
  calc
    |expect (kernelPosterior prior channel observed) targetGain - expect prior sourceGain| ≤
        |expect (kernelPosterior prior channel observed) targetGain -
          expect (kernelPosterior prior channel observed) sourceGain| +
        |expect (kernelPosterior prior channel observed) sourceGain - expect prior sourceGain| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add continuationError (by rw [covariance, abs_div, abs_of_pos positive])

/-- Exact preservation of the whole hidden-state posterior is equivalent to
constant observation likelihood on the supported hidden states. -/
theorem kernelPosterior_eq_iff {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal)) :
    kernelPosterior prior channel observed = prior ↔
      ∀ state ∈ prior.support, (channel state observed).toReal =
        expect prior (fun state => (channel state observed).toReal) := by
  constructor
  · intro equal state supported
    have atom := kernelPosterior_toReal_apply prior channel observed positive state
    rw [equal] at atom
    have weightPositive : 0 < (prior state).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (prior.apply_ne_top state)
    have scaled := (eq_div_iff (ne_of_gt positive)).mp atom
    exact (mul_left_cancel₀ (ne_of_gt weightPositive) scaled).symm
  · intro constant
    apply pmf_ext_toReal
    intro state
    rw [kernelPosterior_toReal_apply prior channel observed positive]
    by_cases supported : state ∈ prior.support
    · rw [constant state supported]
      exact mul_div_cancel_right₀ _ (ne_of_gt positive)
    · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, ENNReal.toReal_zero, zero_mul, zero_div]

/-- An operational likelihood which is constant only on the prior support
already gives exact posterior preservation. Off-support channel behavior is irrelevant. -/
theorem kernelPosterior_eq_of_constant_likelihood {State Signal : Type*} (prior : PMF State)
    (channel : State → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun state => (channel state observed).toReal))
    (constant : ℝ)
    (likelihood : ∀ state ∈ prior.support, (channel state observed).toReal = constant) :
    kernelPosterior prior channel observed = prior := by
  apply (kernelPosterior_eq_iff prior channel observed positive).mpr
  have mass : expect prior (fun state => (channel state observed).toReal) = constant :=
    (expect_congr_on_support likelihood).trans (expect_constant prior constant)
  intro state supported
  exact (likelihood state supported).trans mass.symm

end GameTheory.Math.Probability
