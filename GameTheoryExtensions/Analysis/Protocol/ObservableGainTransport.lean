/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.KernelPosteriorGain
import GameTheory.Protocol.Context

/-! # Observable continuation gains under an actual observation channel

The branch kernels and allowed alternatives stay fixed. Conditioning changes
only the hidden-state law. Likelihood covariance controls the actual gain of
each allowed choice; it need not preserve the entire hidden-state posterior.
-/

noncomputable section

namespace GameTheory.Protocol.Context

open GameTheory.Math.Probability

/-- A continuation gain is the belief expectation of its hidden-state gains.
Both continuation integrals are explicit, with no finite-carrier premise. -/
theorem ofBelief_gain_eq_expect {Hidden Choice Outcome : Type*}
    (belief : PMF Hidden) (branch : Hidden → Choice → PMF Outcome) (payoff : Outcome → ℝ)
    (incumbent alternative : Choice)
    (alternativeIntegrable : PayoffIntegrable (belief.bind (fun h => branch h alternative)) payoff)
    (incumbentIntegrable : PayoffIntegrable (belief.bind (fun h => branch h incumbent)) payoff) :
    (ofBelief belief branch payoff).value alternative -
        (ofBelief belief branch payoff).value incumbent =
      expect belief (fun h => expect (branch h alternative) payoff -
        expect (branch h incumbent) payoff) := by
  change expect (belief.bind (fun h => branch h alternative)) payoff -
    expect (belief.bind (fun h => branch h incumbent)) payoff = _
  rw [expect_bind_tower belief _ _ alternativeIntegrable,
    expect_bind_tower belief _ _ incumbentIntegrable,
    expect_sub (payoffIntegrable_bind_conditionalExpectation belief _ _ alternativeIntegrable)
      (payoffIntegrable_bind_conditionalExpectation belief _ _ incumbentIntegrable)]

/-- The actual conditional continuation gain differs from its prior gain by
exactly its covariance with the channel likelihood divided by observed mass. -/
theorem ofBelief_gain_after_observation {Hidden Choice Outcome Signal : Type*}
    (prior : PMF Hidden) (channel : Hidden → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun h => (channel h observed).toReal))
    (branch : Hidden → Choice → PMF Outcome) (payoff : Outcome → ℝ)
    (incumbent alternative : Choice)
    (alternativeIntegrable : PayoffIntegrable (prior.bind (fun h => branch h alternative)) payoff)
    (incumbentIntegrable : PayoffIntegrable (prior.bind (fun h => branch h incumbent)) payoff) :
    let gain := fun h => expect (branch h alternative) payoff - expect (branch h incumbent) payoff
    (ofBelief (kernelPosterior prior channel observed) branch payoff).value alternative -
        (ofBelief (kernelPosterior prior channel observed) branch payoff).value incumbent =
      (ofBelief prior branch payoff).value alternative -
        (ofBelief prior branch payoff).value incumbent +
      (expect prior (fun h => (channel h observed).toReal * gain h) -
        expect prior (fun h => (channel h observed).toReal) * expect prior gain) /
          expect prior (fun h => (channel h observed).toReal) := by
  intro gain
  have integrable : PayoffIntegrable prior gain :=
    payoffIntegrable_sub
      (payoffIntegrable_bind_conditionalExpectation prior _ _ alternativeIntegrable)
      (payoffIntegrable_bind_conditionalExpectation prior _ _ incumbentIntegrable)
  rw [ofBelief_gain_eq_expect prior branch payoff incumbent alternative alternativeIntegrable
    incumbentIntegrable,
    ofBelief_gain_eq_expect (kernelPosterior prior channel observed) branch payoff incumbent
      alternative
      (payoffIntegrable_bind_kernelPosterior prior channel observed positive _ _
        alternativeIntegrable)
      (payoffIntegrable_bind_kernelPosterior prior channel observed positive _ _
        incumbentIntegrable)]
  have identity := expect_kernelPosterior_sub_expect prior channel observed positive gain integrable
  linarith only [identity]

/-- Nonpositive covariance for every allowed alternative preserves actual
local optimality. `Choice` may itself be a whole information-local policy;
no maximization separately at hidden states is permitted. This is a conditional
context result, not a construction of consistent beliefs or an initialized joint law. -/
theorem isLocallyOptimal_after_observation {Hidden Choice Outcome Signal : Type*}
    (prior : PMF Hidden) (channel : Hidden → PMF Signal) (observed : Signal)
    (positive : 0 < expect prior (fun h => (channel h observed).toReal))
    (branch : Hidden → Choice → PMF Outcome) (payoff : Outcome → ℝ)
    (allowed : Set Choice) (incumbent : Choice)
    (incumbentIntegrable : PayoffIntegrable (prior.bind (fun h => branch h incumbent)) payoff)
    (alternativesIntegrable : ∀ alternative ∈ allowed,
      PayoffIntegrable (prior.bind (fun h => branch h alternative)) payoff)
    (sourceOptimal : (ofBelief prior branch payoff).IsLocallyOptimal allowed incumbent)
    (covariance : ∀ alternative ∈ allowed,
      let gain := fun h => expect (branch h alternative) payoff - expect (branch h incumbent) payoff
      expect prior (fun h => (channel h observed).toReal * gain h) ≤
        expect prior (fun h => (channel h observed).toReal) * expect prior gain) :
    (ofBelief (kernelPosterior prior channel observed) branch payoff).IsLocallyOptimal allowed
      incumbent := by
  have targetIncumbent :
      (ofBelief (kernelPosterior prior channel observed) branch payoff).IntegrableAt incumbent :=
    payoffIntegrable_bind_kernelPosterior prior channel observed positive
      (fun h => branch h incumbent) payoff incumbentIntegrable
  have targetAlternative : ∀ alternative ∈ allowed,
      (ofBelief (kernelPosterior prior channel observed) branch payoff).IntegrableAt alternative :=
    fun alternative member => payoffIntegrable_bind_kernelPosterior prior channel observed positive
      (fun h => branch h alternative) payoff (alternativesIntegrable alternative member)
  apply (isLocallyOptimal_iff_of_integrable
    (ctx := ofBelief (kernelPosterior prior channel observed) branch payoff)
    targetIncumbent targetAlternative).mpr
  intro alternative member
  have source := (isLocallyOptimal_iff_of_integrable (ctx := ofBelief prior branch payoff)
    incumbentIntegrable alternativesIntegrable).mp sourceOptimal alternative member
  have integrable := payoffIntegrable_sub
    (payoffIntegrable_bind_conditionalExpectation prior _ _
      (alternativesIntegrable alternative member))
    (payoffIntegrable_bind_conditionalExpectation prior _ _ incumbentIntegrable)
  have priorGain : expect prior (fun h => expect (branch h alternative) payoff -
      expect (branch h incumbent) payoff) ≤ 0 := by
    rw [← ofBelief_gain_eq_expect prior branch payoff incumbent alternative
      (alternativesIntegrable alternative member) incumbentIntegrable]
    exact sub_nonpos.mpr source
  have conditionalGain := expect_kernelPosterior_nonpos prior channel observed positive _
    integrable priorGain (covariance alternative member)
  rw [← ofBelief_gain_eq_expect (kernelPosterior prior channel observed) branch payoff incumbent
    alternative (targetAlternative alternative member) targetIncumbent] at conditionalGain
  exact sub_nonpos.mp conditionalGain

end GameTheory.Protocol.Context
