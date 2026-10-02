/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.SourceEquilibrium
import Vegas.Examples.SelectiveAssociation.InitialRationality
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Sequential-equilibrium separation for accepted named evidence

The actual source program, equipped with stage-local source actions, arbitrary
finite claims, current named evidence and authentic certificate forwarding, has a sequential
equilibrium giving Alice payoff zero. In the corresponding bounded native
game, every sequentially rational assessment gives Alice at least one half.
Thus no native sequential equilibrium has this source equilibrium's initialized
public-result law, irrespective of how a translator chooses strategies or
beliefs. The native opportunity is certification before acceptance followed
by selective association with an accepted binding.

This separates the stated source interface and native service. It does not
classify every possible intermediate source language of pending proposals.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-- Public publications, with the same failure defaults as the source readout.
The initial evaluator reaches concrete terminal controls, so the default at
`none` does not affect the initialized law. -/
def nativePublicResult (state : nativeApp.ProtocolState) : Results :=
  state.elim ⟨.failure, .failure, .failure⟩
    (fun control => nativeResults control.execution.application.config)

theorem native_public_law_value (profile : Profile nativeModel.behavioralSignature) :
    expect ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
      (fun history => nativePublicResult history.state))
        (fun result => utility result alice) =
        expect (nativeModel.runBehavioral profile (2 * nativeHorizon + 1))
          (fun history => nativeUtility alice history.state) := by
  change expect ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
    (fun history => history.state.elim ⟨.failure, .failure, .failure⟩
      (fun control => nativeResults control.execution.application.config)))
        (fun result => utility result alice) = _
  rw [native_initial_result_law, expect_map, native_initial_value]
  rfl

/-- The obstruction already applies to sequential rationality. Allowing a
different consistent belief system or a different profile translation cannot
recover this initialized public-result law. -/
theorem native_rational_public_law_ne_source (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (source : (NamedSource.model Claim).BehavioralAssessment)
    (sourceStrategy : source.strategy = NamedSource.profile Claim defaultClaim)
    (target : nativeModel.BehavioralAssessment)
    (rational : target.IsSequentiallyRationalFor fun who site =>
        target.truncatedContinuationContext site (fun history => nativeUtility who
            history.state) (2 * nativeHorizon + 1)) :
    (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
        (fun history => nativePublicResult history.state) ≠
      ((NamedSource.model Claim).runBehavioral source.strategy (2 * NamedSource.horizon + 1)).map
        (fun history => NamedSource.protocolResults history.state) := by
  let players := nativeMenu.decodeProfile (PMF.pure nativeInitial)
    nativeHorizon nativeScheduler target.strategy
  refine nativeModel.initial_law_ne_of_induced_information target
    (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)
    rational alice nativeInitialSite native_initial_history_value nativeAliceBehavior
    (nativeUtility_continuation_integrable target nativeInitialSite _)
    (fun history => nativePublicResult history.state) (fun result => utility result alice)
    native_public_law_value (PMF.uniformOfFintype Bool) (Set.toFinite _) (fun _ => ())
    (fun bit guess => correctness (.success bit) guess)
    (fun _ => PMF.pure (.success false))
    (fun _ => nativeCarolGuessLaw (nativeAliceProfile players)) fair_guess_reference_optimal
    (fun _ => DecisionExperiment.ResponseIntegrable.of_finite _ _ _)
    (nativeDeviationOutcomes players) (fun bit result => correctness (.success bit) result.carol)
    1 (fun _ _ => ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _⟩) ?_ ?_ ?_ _ ?_
  · rw [native_initial_value, native_decode_alice_deviation]
    have value := congrArg (fun law : PMF Results =>
      expect law (fun result => utility result alice)) (native_deviation_outcome_law players)
    rw [expect_map] at value
    exact value
  · intro bit _ result supported
    obtain ⟨aliceSuccess, bobSuccess⟩ := native_deviation_publications target rational
      bit result supported
    rw [utility_alice, aliceSuccess, bobSuccess]
    simp
  · intro bit _
    exact native_deviation_carol_bound players bit
  · rw [fair_guess_reference_value, expect_map, sourceStrategy]
    change expect ((NamedSource.model Claim).runBehavioral (NamedSource.profile Claim defaultClaim)
      (2 * NamedSource.horizon + 1)) (NamedSource.payoff alice) < 1 - 1 / 2
    rw [NamedSource.prescribed_initial_alice_payoff Claim defaultClaim]
    norm_num

/-- There is a genuine source sequential equilibrium whose public-result law
is different from that of every native sequential equilibrium. No restriction
on a proposed strategy translator is part of this impossibility statement. -/
theorem exists_source_equilibrium_no_native_outcome_match (Claim : Type) [Fintype Claim]
    (defaultClaim : Claim) :
    ∃ source : (NamedSource.model Claim).BehavioralAssessment,
      source.IsSequentialEquilibriumFor
        ((NamedSource.menu Claim).decisionInformationAntichain (PMF.pure NamedSource.initial)
          NamedSource.horizon (NamedSource.scheduler Claim))
        (fun who site => source.truncatedContinuationContext site (NamedSource.payoff who)
          (2 * NamedSource.horizon + 1)) ∧
      ∀ target : nativeModel.BehavioralAssessment,
        target.IsSequentialEquilibriumFor
          (nativeMenu.decisionInformationAntichain (PMF.pure nativeInitial)
            nativeHorizon nativeScheduler)
          (fun who site => target.truncatedContinuationContext site
            (fun history => nativeUtility who history.state) (2 * nativeHorizon + 1)) →
        (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
            (fun history => nativePublicResult history.state) ≠
          ((NamedSource.model Claim).runBehavioral source.strategy
            (2 * NamedSource.horizon + 1)).map
              (fun history => NamedSource.protocolResults history.state) := by
  obtain ⟨source, strategy, equilibrium, _law⟩ :=
    NamedSource.exists_sequentialEquilibrium Claim defaultClaim
  exact ⟨source, equilibrium, fun target targetEquilibrium =>
    native_rational_public_law_ne_source Claim defaultClaim source strategy target
      targetEquilibrium.1⟩

end Vegas.Examples.SelectiveAssociation
