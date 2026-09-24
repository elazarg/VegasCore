/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceEquilibrium
import VegasTests.SelectiveAssociationInitialRationality

/-! # Sequential-equilibrium separation for accepted named evidence

The actual source program, equipped with stage-local source actions, arbitrary
finite claims, current named evidence and known replays, has a sequential
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

namespace VegasTests.SelectiveAssociation

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-- Public publications, with the same failure defaults as the source readout.
The initial evaluator reaches concrete terminal controls, so the default at
`none` does not affect the initialized law. -/
def nativePublicResult (state : nativeApp.ProtocolState) : Results :=
  state.elim ⟨.failure, .failure, .failure⟩
    (fun control => nativeResults control.execution.application.config)

theorem native_public_law_value (profile : Profile nativeModel.behavioralSignature) :
    ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
      (fun history => nativePublicResult history.state)).expect
        (fun result => utility result alice) =
        (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).expect
          (fun history => nativeUtility alice history.state) := by
  change ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
    (fun history => history.state.elim ⟨.failure, .failure, .failure⟩
      (fun control => nativeResults control.execution.application.config))).expect
        (fun result => utility result alice) = _
  rw [native_initial_result_law, FinDist.expect_map, native_initial_value]

/-- The obstruction already applies to sequential rationality. Allowing a
different consistent belief system or a different profile translation cannot
recover this initialized public-result law. -/
theorem native_rational_public_law_ne_source (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (source : (NamedSource.model Claim).BehavioralAssessment)
    (sourceStrategy : source.strategy = NamedSource.profile Claim defaultClaim)
    (target : nativeModel.BehavioralAssessment)
    (rational : target.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)) :
    (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
        (fun history => nativePublicResult history.state) ≠
      ((NamedSource.model Claim).runBehavioral source.strategy (2 * NamedSource.horizon + 1)).map
        (fun history => NamedSource.protocolResults history.state) := by
  intro sameLaw
  have gain := native_sequential_initial_bound target rational
  have sameValue := congrArg (fun law : FinDist Results =>
    law.expect (fun result => utility result alice)) sameLaw
  rw [native_public_law_value, FinDist.expect_map, sourceStrategy] at sameValue
  change (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).expect
    (fun history => nativeUtility alice history.state) =
      ((NamedSource.model Claim).runBehavioral (NamedSource.profile Claim defaultClaim)
        (2 * NamedSource.horizon + 1)).expect (NamedSource.payoff alice) at sameValue
  rw [NamedSource.prescribed_initial_alice_payoff Claim defaultClaim] at sameValue
  linarith

/-- There is a genuine source sequential equilibrium whose public-result law
is different from that of every native sequential equilibrium. No restriction
on a proposed strategy translator is part of this impossibility statement. -/
theorem exists_source_equilibrium_no_native_outcome_match (Claim : Type) [Fintype Claim]
    (defaultClaim : Claim) :
    ∃ source : (NamedSource.model Claim).BehavioralAssessment,
      source.IsSequentialEquilibriumFor
        ((NamedSource.menu Claim).decisionInformationAntichain (FinDist.pure NamedSource.initial)
          NamedSource.horizon (NamedSource.scheduler Claim))
        (fun who site => source.continuationContext site (NamedSource.payoff who)
          (2 * NamedSource.horizon + 1)) ∧
      ∀ target : nativeModel.BehavioralAssessment,
        target.IsSequentialEquilibriumFor
          (nativeMenu.decisionInformationAntichain (FinDist.pure nativeInitial)
            nativeHorizon nativeScheduler)
          (fun who site => target.continuationContext site
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

end VegasTests.SelectiveAssociation
