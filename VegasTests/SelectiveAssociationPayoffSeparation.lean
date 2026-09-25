/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSeparation
import VegasTests.SelectiveAssociationSettlement

/-! # Sequential-equilibrium separation when utility is the returned payoff

The counterexample has one fixed, program-declared payoff vector. Alice's
source equilibrium has expected returned payoff zero; every sequentially
rational native assessment has expected returned payoff at least one half.
The native readout evaluates the actual compiled settlement expressions.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def nativePayoutLaw
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (profile : Profile (serviceModel observation).behavioralSignature) : FinDist ℝ :=
  ((serviceApp observation).runRounds (serviceScheduler observation)
    ((serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation) profile)
      nativeHorizon nativeRoot).map (fun final => nativeAlicePayout final.application.config)

def sourcePayoutLaw {Claim : Type} [Fintype Claim]
    (profile : Profile (NamedSource.model Claim).behavioralSignature) : FinDist ℝ :=
  ((NamedSource.model Claim).runBehavioral profile (2 * NamedSource.horizon + 1)).map
    (fun history => returnedPayoff (NamedSource.protocolResults history.state) alice)

theorem native_payout_expectation
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (profile : Profile (serviceModel observation).behavioralSignature) :
    (nativePayoutLaw profile).expect id =
      ((serviceModel observation).runBehavioral profile (2 * nativeHorizon + 1)).expect
        (fun history => nativeUtility alice history.state) := by
  rw [native_initial_value]
  unfold nativePayoutLaw
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro final supported
  apply nativeAlicePayout_eq_utility
  apply native_plan_complete _ final
  rwa [native_prefix_rounds _ nativePlan [] (by simp)] at supported

theorem source_payout_expectation {Claim : Type} [Fintype Claim]
    (profile : Profile (NamedSource.model Claim).behavioralSignature) :
    (sourcePayoutLaw profile).expect id =
      ((NamedSource.model Claim).runBehavioral profile (2 * NamedSource.horizon + 1)).expect
        (NamedSource.payoff alice) := by
  unfold sourcePayoutLaw
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _
  exact returnedPayoff_eq_utility _ _

theorem native_sequential_payout_bound (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)) :
    1 / 2 ≤ (nativePayoutLaw assessment.strategy).expect id := by
  rw [native_payout_expectation]
  exact native_sequential_initial_bound assessment rational

theorem source_equilibrium_payout_zero (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    (sourcePayoutLaw (NamedSource.profile Claim defaultClaim)).expect id = 0 := by
  rw [source_payout_expectation, NamedSource.prescribed_initial_alice_payoff]

/-- Even Alice's returned-payoff law cannot be preserved. The payoff function
is fixed in the program, and no restriction is placed on the translator. -/
theorem exists_source_equilibrium_no_native_payout_match (Claim : Type) [Fintype Claim]
    (defaultClaim : Claim) :
    ∃ source : (NamedSource.model Claim).BehavioralAssessment,
      source.IsSequentialEquilibriumFor
        ((NamedSource.menu Claim).decisionInformationAntichain (FinDist.pure NamedSource.initial)
          NamedSource.horizon (NamedSource.scheduler Claim))
        (fun who site => source.continuationContext site (NamedSource.payoff who)
          (2 * NamedSource.horizon + 1)) ∧
      (sourcePayoutLaw source.strategy).expect id = 0 ∧
      ∀ target : nativeModel.BehavioralAssessment,
        target.IsSequentiallyRationalWithin
          (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1) →
        sourcePayoutLaw source.strategy ≠ nativePayoutLaw target.strategy := by
  obtain ⟨source, strategy, equilibrium, _law⟩ :=
    NamedSource.exists_sequentialEquilibrium Claim defaultClaim
  have zero : (sourcePayoutLaw source.strategy).expect id = 0 := by
    rw [strategy, source_equilibrium_payout_zero]
  refine ⟨source, equilibrium, zero, fun target rational sameLaw => ?_⟩
  have gain := native_sequential_payout_bound target rational
  rw [← sameLaw, zero] at gain
  norm_num at gain

end VegasTests.SelectiveAssociation
