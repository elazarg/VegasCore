/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.Separation
import Vegas.Examples.SelectiveAssociation.Settlement
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential-equilibrium separation when utility is the returned payoff

The counterexample has one fixed, program-declared payoff vector. Alice's
source equilibrium has expected returned payoff zero; every sequentially
rational native assessment has expected returned payoff at least one half.
The native readout evaluates the actual compiled settlement expressions.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def nativePayoutLaw
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (profile : Profile (serviceModel observation).behavioralSignature) : PMF ℝ :=
  ((serviceApp observation).runRounds (serviceScheduler observation)
    ((serviceMenu observation).decodeProfile (PMF.pure nativeInitial) nativeHorizon
      (serviceScheduler observation) profile)
      nativeHorizon nativeRoot).map (fun final => nativeAlicePayout final.application.config)

def sourcePayoutLaw {Claim : Type} [Fintype Claim]
    (profile : Profile (NamedSource.model Claim).behavioralSignature) : PMF ℝ :=
  ((NamedSource.model Claim).runBehavioral profile (2 * NamedSource.horizon + 1)).map
    (fun history => returnedPayoff (NamedSource.protocolResults history.state) alice)

theorem native_payout_expectation
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (profile : Profile (serviceModel observation).behavioralSignature) :
    expect (nativePayoutLaw profile) id =
      expect ((serviceModel observation).runBehavioral profile (2 * nativeHorizon + 1))
        (fun history => nativeUtility alice history.state) := by
  rw [native_initial_value]
  unfold nativePayoutLaw
  rw [expect_map]
  apply expect_congr_on_support
  intro final supported
  apply nativeAlicePayout_eq_utility
  apply native_plan_complete _ final
  rwa [native_prefix_rounds _ nativePlan [] (by simp)] at supported

theorem source_payout_expectation {Claim : Type} [Fintype Claim]
    (profile : Profile (NamedSource.model Claim).behavioralSignature) :
    expect (sourcePayoutLaw profile) id =
      expect ((NamedSource.model Claim).runBehavioral profile (2 * NamedSource.horizon + 1))
        (NamedSource.payoff alice) := by
  unfold sourcePayoutLaw
  rw [expect_map]
  apply expect_congr_on_support
  intro history _
  exact returnedPayoff_eq_utility _ _

theorem native_sequential_payout_bound (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (fun history => nativeUtility who
            history.state) (2 * nativeHorizon + 1)) :
    1 / 2 ≤ expect (nativePayoutLaw assessment.strategy) id := by
  rw [native_payout_expectation]
  exact native_sequential_initial_bound assessment rational

theorem source_equilibrium_payout_zero (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    expect (sourcePayoutLaw (NamedSource.profile Claim defaultClaim)) id = 0 := by
  rw [source_payout_expectation, NamedSource.prescribed_initial_alice_payoff]

/-- Every history of the named-source protocol ends within its calendar bound. -/
theorem NamedSource.terminates (Claim : Type) [Fintype Claim] :
    (NamedSource.arena Claim).WellFoundedHistories :=
  ((NamedSource.menu Claim).bounded _ _ _).wellFoundedHistories

/-- Every history of the native runtime ends within its fuel. -/
theorem nativeTerminates : nativeArena.WellFoundedHistories :=
  (nativeMenu.bounded _ _ _).wellFoundedHistories

/-- Even Alice's returned-payoff law cannot be preserved. The payoff function
is fixed in the program, and no restriction is placed on the translator. Both
the source equilibrium and native rationality are of complete (terminal) play. -/
theorem exists_source_equilibrium_no_native_payout_match (Claim : Type) [Fintype Claim]
    (defaultClaim : Claim) :
    ∃ source : (NamedSource.model Claim).BehavioralAssessment,
      source.IsSequentialEquilibrium
        ((NamedSource.menu Claim).decisionInformationAntichain (PMF.pure NamedSource.initial)
          NamedSource.horizon (NamedSource.scheduler Claim))
        (NamedSource.terminates Claim) NamedSource.payoff ∧
      expect (sourcePayoutLaw source.strategy) id = 0 ∧
      ∀ target : nativeModel.BehavioralAssessment,
        target.IsSequentiallyRational nativeTerminates
            (fun who history => nativeUtility who history.state) →
        sourcePayoutLaw source.strategy ≠ nativePayoutLaw target.strategy := by
  obtain ⟨source, strategy, equilibrium, _law⟩ :=
    NamedSource.exists_sequentialEquilibrium Claim defaultClaim
  have zero : expect (sourcePayoutLaw source.strategy) id = 0 := by
    rw [strategy, source_equilibrium_payout_zero]
  refine ⟨source, (source.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    (NamedSource.terminates Claim) ((NamedSource.menu Claim).bounded _ _ _) _).mpr equilibrium,
    zero, fun target rational sameLaw => ?_⟩
  have gain := native_sequential_payout_bound target
    ((target.isSequentiallyRational_iff_truncated_of_bounded nativeTerminates
      (nativeMenu.bounded _ _ _) _).mp rational)
  rw [← sameLaw, zero] at gain
  norm_num at gain

end Vegas.Examples.SelectiveAssociation
