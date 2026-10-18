/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingBobQuietChoice
import Vegas.Examples.CommitSeedSignallingInitialDeviation

/-! # Private timing information prevents preservation in the signalling runtime -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice setup)

/-- Alice earns at least one quarter in every native sequential equilibrium.
The bound is for the initialized runtime and its actual assessed continuation. -/
theorem native_equilibrium_alice_payoff_quarter
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    (1 / 4 : ℝ) ≤ expect (nativeHistoryLaw assessment.strategy) (rawPayoff alice) := by
  have positive := aliceFirst_fixedLate_context_quarter_of_bobQuiet_wait assessment equilibrium
    (bobQuiet_counted_decoded_wait assessment equilibrium)
  have integrable (alternative : rawModel.BehavioralPolicy alice) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate
      aliceFirstSite (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final) alternative
  have compare := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy alice)) (fun alternative _ => integrable alternative)).mp
    (equilibrium.1 alice aliceFirstSite)
  have upper := compare (fixedLateContinuation alice) (Set.mem_univ _)
  change (1 / 4 : ℝ) ≤ expect
    (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
      rawProtocol.initHistory) (rawPayoff alice)
  rw [initialized_value_eq_aliceFirst_context]
  exact positive.trans upper

/-- Every native sequential equilibrium changes the joint law of every honest
source profile. Alice's source payoff is zero, while every native equilibrium
gives her strictly positive expected payoff. -/
theorem no_preserving_sequentialEquilibrium
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    sourceJointLaw source ≠ nativeJointLaw assessment.strategy := by
  intro preserves
  have positive := native_equilibrium_alice_payoff_quarter assessment equilibrium
  have zero := preservation_implies_zero_payoff source assessment.strategy preserves alice
  linarith

/-- One fixed honest source sequential equilibrium has no preserving native
sequential equilibrium for the installed asynchronous runtime. This fixture
uses exclusion loss one and reward three, rather than a forfeit above the
entire payoff range. -/
theorem exists_honest_sequentialEquilibrium_without_native_preservation :
    ∃ source : setup.intendedModel.BehavioralAssessment,
      source.IsSequentialEquilibrium honest_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories honestPayoff ∧
      ∀ assessment : rawModel.BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionInformationAntichain initial horizon scheduler)
          canonicalCertificate rawPayoff →
        sourceJointLaw source.strategy ≠ nativeJointLaw assessment.strategy := by
  obtain ⟨source, equilibrium⟩ := exists_honest_sequentialEquilibrium
  exact ⟨source, equilibrium, fun assessment nativeEquilibrium =>
    no_preserving_sequentialEquilibrium source.strategy assessment nativeEquilibrium⟩

end Vegas.Examples.CommitSeedSignalling
