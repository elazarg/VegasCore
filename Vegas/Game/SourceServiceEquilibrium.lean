/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAvailableOpening
import Vegas.Game.SourceServiceSampleComparison
import Vegas.Game.SourceServiceForeignDisclosure
import Vegas.Game.SourceServiceSiteKind
import Vegas.Game.SourceServiceTimedLaw
import Vegas.Game.RevealServiceRosterTiming
import Vegas.Game.ServiceRosterClock
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Sequential equilibrium of the full-language service

Every sequential equilibrium of the source information model has a sequential
equilibrium of the permitted native service model with the same law of typed
source terminal states. The native equilibrium is a limit of the timed
approximants `Vegas.TimedApproximant.ofSource` of
one fully supported Bayes sequence of the source equilibrium, with the roster
timing law at weight one half. Each native decision site is compared with
original source deviations according to its kind
(`Vegas.DecisionSiteKind`): most kinds have zero
gain, an unsent binding is simulated exactly, and a disclosure with an
available opening gains at most twice the source gain error.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- Every sequential equilibrium of the source information model has a
sequential equilibrium of the permitted native service model whose law of
typed source terminal states is the source law. -/
theorem exists_native_sequentialEquilibrium
    (utility : Option (State L service.setup.program.terminalCtx) → Player → ℝ)
    (source : service.sourceModel.BehavioralAssessment)
    [∀ who (site : service.sourceModel.InformationSite who),
      Fintype (service.sourceModel.InformationHistory who site.1)]
    (equilibrium : source.IsSequentialEquilibriumFor
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))
      (fun who site => source.continuationContext site
        (fun final => utility (service.setup.protocolReadout final.state) who)
        (instructionCount service.setup.program + 1))) :
    ∃ target : service.model.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (service.menu.decisionInformationAntichain (initialLaw service.setup)
          service.planLength service.scheduler)
        (fun who site => target.continuationContext site
          (fun final => utility (service.readout final) who) service.fuel) ∧
      (service.model.runBehavioral target.strategy service.fuel).map service.readout =
        (service.sourceModel.runBehavioral source.strategy
            (instructionCount service.setup.program + 1)).map
              (fun final => service.setup.protocolReadout final.state) := by
  classical
  let admission := CommitmentInterface.values service.setup.program
  let sourceModel := service.setup.informationModel admission
  obtain ⟨witness, approximates, _⟩ := equilibrium.2
  let _ : Finite (service.setup.executionProtocol admission).History :=
    (approximates 0).1.finite_history (service.setup.protocol_bounded admission)
  obtain ⟨sourceSequence, full, sourceBayes, converges, _⟩ :=
    sourceService_consistent_supported_sequence service.setup service.bounds service.values
      source (service.setup.decision_antichain admission) equilibrium.2
  have sourceMixed : (sourceSequence 0).IsFullyMixed := fun who site => full 0 who site.1
  -- The timing law and the native approximants.
  let half : ℝ := 1 / 2
  have halfNonnegative : 0 ≤ half := by norm_num [half]
  have halfBounded : half ≤ 1 := by norm_num [half]
  let timing := rosterTiming service.setup service.rosters service.opportunities half
    halfNonnegative halfBounded
  have timingFull (event : (graph service.setup).EventId) (who : Player)
      (owned : (graph service.setup).actor? event = some who) :
      FullSupport (timing event who owned) :=
    rosterTiming_fullSupport service.setup service.rosters service.opportunities half
      halfNonnegative halfBounded (by norm_num [half]) event who owned
  let approx (n : Nat) := TimedApproximant.ofSource service timing timingFull
    (sourceSequence n).strategy (full n)
  -- One vanishing bound on every original source gain, for all players.
  let sourceObserve := fun final : (service.setup.executionProtocol admission).History =>
    service.setup.protocolReadout final.state
  choose errors nonnegative vanishes bounds using fun who =>
    converges.exists_uniform_policy_gain_bound (sourceSequence 0) sourceMixed who
      (fun history => utility (sourceObserve history) who)
      (instructionCount service.setup.program + 1) (equilibrium.1 who)
  have sourceGain (n : Nat) (who : Player) (deviation : sourceModel.AssessmentDeviation who) :
      let comparison := sourceModel.assessmentComparison sourceObserve
        (instructionCount service.setup.program + 1) (sourceSequence n) who deviation
      expect comparison.alternative (utility · who) -
        expect comparison.prescribed (utility · who) ≤ errors who n := by
    simpa only [InformationModel.assessmentComparison, expect_map, Context.value,
      InformationModel.BehavioralAssessment.continuationContext] using
        bounds who n deviation.1 deviation.2
  let comparisonError (n : Nat) : ℝ := 2 * ∑ who, errors who n
  have errorNonnegative (n : Nat) : 0 ≤ comparisonError n :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun who _ => nonnegative who n)
  have errorVanishes : Tendsto comparisonError atTop (nhds 0) := by
    have total : Tendsto (fun n => ∑ who, errors who n) atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum Finset.univ (fun who _ => vanishes who)
    simpa only [mul_zero] using total.const_mul 2
  have localComparisons (n : Nat) (who : Player) (site : service.model.InformationSite who)
      (law : PMF (service.model.Choice who site.1)) :
      let comparison := service.model.assessmentComparison service.readout service.fuel
        (approx n).assessment who (site, ((approx n).assessment.strategy who).withLaw site.1 law)
      expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n ∨
        ∃ mixture : PMF (sourceModel.AssessmentDeviation who),
          expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who) ≤
            expect mixture (fun deviation =>
              let sourceComparison := sourceModel.assessmentComparison sourceObserve
                (instructionCount service.setup.program + 1) (sourceSequence n) who deviation
              expect sourceComparison.alternative (utility · who) -
                expect sourceComparison.prescribed (utility · who)) + comparisonError n := by
    intro comparison
    have zeroGain (same : comparison.alternative = comparison.prescribed) :
        expect comparison.alternative (utility · who) -
          expect comparison.prescribed (utility · who) ≤ comparisonError n := by
      rw [same, sub_self]
      exact errorNonnegative n
    obtain ⟨past, view, event, observed, granted, kind⟩ := service.exists_siteKind who site
    cases kind with
    | chance actorless =>
        exact Or.inl (zeroGain ((approx n).sample_comparison_eq who site past view observed
          actorless granted law))
    | foreignBinding owner payload foreign outputEq =>
        exact Or.inl (zeroGain ((approx n).foreign_binding_comparison_eq who site past view
          observed foreign outputEq granted law))
    | foreignDisclosure owner payload foreign owned outputEq =>
        exact Or.inl (zeroGain ((approx n).foreign_disclosure_comparison_eq who site past view
          observed foreign owned outputEq granted law))
    | recordedBinding payload outputEq recorded =>
        exact Or.inl (zeroGain ((approx n).recorded_comparison_eq who site past view observed
          outputEq granted recorded law))
    | unsentBinding payload outputEq unsent =>
        obtain ⟨mixture, prescribedEq, alternativeEq⟩ :=
          TimedApproximant.unsent_binding_comparisons service timing timingFull
            (sourceSequence n) (full n) (sourceBayes n) (approx n) rfl who site past view
            observed outputEq granted unsent law
        have gain := expect_sub_eq_of_eq_bind mixture _ _ _ _ prescribedEq alternativeEq
          (utility · who)
        exact Or.inr ⟨mixture, gain.le.trans (le_add_of_nonneg_right (errorNonnegative n))⟩
    | recordedDisclosure payload owned outputEq recorded =>
        exact Or.inl (zeroGain ((approx n).recorded_disclosure_comparison_eq who site past view
          observed owned outputEq granted recorded law))
    | absentOpening payload owned outputEq unsent absent =>
        exact Or.inl (zeroGain ((approx n).absent_opening_comparison_eq who site past view
          observed owned outputEq granted unsent absent law))
    | availableOpening payload owned outputEq unsent candidate raw available =>
        have bound := TimedApproximant.available_opening_gain_le service timing timingFull
          (sourceSequence n) (full n) (sourceBayes n) (approx n) rfl who site past view observed
          outputEq owned granted unsent candidate raw available (utility · who) (errors who n)
          (sourceGain n who) half (by norm_num [half])
          (fun count inside => by
            have passed := rosterTiming_prefix_le service.setup service.rosters
              service.opportunities half halfNonnegative halfBounded event who owned count inside
            norm_num [half] at passed ⊢
            linarith)
          law
        have single : errors who n ≤ ∑ player, errors player n :=
          Finset.single_le_sum (fun player _ => nonnegative player n) (Finset.mem_univ who)
        refine Or.inl (bound.trans ?_)
        change errors who n / (1 / 2) ≤ 2 * ∑ player, errors player n
        rw [div_div_eq_mul_div, div_one, mul_comm]
        linarith
  have initialized (n : Nat) :
      (service.model.runBehavioral (approx n).assessment.strategy service.fuel).map
          service.readout =
        (sourceModel.runBehavioral (sourceSequence n).strategy
          (instructionCount service.setup.program + 1)).map sourceObserve := by
    rw [TimedApproximant.ofSource_strategy]
    exact sourceServiceTimedProfile_protocol_law service.setup service.leaks service.bounds
      service.values service.initialValues service.capacity service.rosters
      service.opportunities.binding timing timingFull service.network (sourceSequence n).strategy
  obtain ⟨target, targetEquilibrium, law, _⟩ :=
    ContinuationSimulation.exists_sequentialEquilibrium_limit_of_local_comparisons sourceObserve
      service.readout (instructionCount service.setup.program + 1) service.fuel
      (service.menu.bounded (initialLaw service.setup) service.planLength service.scheduler)
      (service.menu.decisionRecall (initialLaw service.setup) service.planLength
        service.scheduler)
      (roster_menu_common_depth service.setup service.leaks service.rosters service.network
        service.menu)
      utility source sourceSequence sourceMixed converges equilibrium.1
      (fun n => (approx n).assessment) (fun n => (approx n).mixed)
      (fun n => TimedApproximant.ofSource_bayes service timing timingFull
        (sourceSequence n).strategy (full n))
      comparisonError errorVanishes localComparisons initialized
  exact ⟨target, targetEquilibrium, law⟩

end SourceServiceSpec

end Vegas
