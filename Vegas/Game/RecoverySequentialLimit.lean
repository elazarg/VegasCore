/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryInitializedProjection

/-! # Recovery equilibrium limits from the original common completion witness -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
  [Finite setup.intendedProtocol.History]
  [(application setup leaks).FiniteNature (initialLaw setup)
    (nativeScheduler (runtime setup) leaks scheduler)]
  [Fintype ((Recovery.onePacketMenu (runtime setup) leaks bounds).protocol
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).History]
  [∀ who, DecidableEq ((model setup leaks bounds
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) horizon scheduler).InfoState who)]

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler

/-- Pure-choice comparisons complete the same actual recovery witness. The
initialized joint law is derived from its original weights and recovery service;
no additional completion or replacement assessment is selected. -/
theorem sequentialEquilibrium_of_local_comparisons {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (source : setup.intendedModel.BehavioralAssessment)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (sourceRational : source.IsSequentiallyRationalFor fun who site =>
      source.truncatedContinuationContext site
        (fun final => (intendedReadoutExclusion setup parameter utility excludedPayoff final).2 who)
        (instructionCount setup.program + 1))
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0))
    (weights : ℕ → ∀ p, PMF
      (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (fallback : ∀ who, (R).Policy who)
    (sequence : ℕ → (R).BehavioralAssessment)
    (assembled : ∀ n, (sequence n).strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sourceSequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (limit : (R).BehavioralAssessment) (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
    (consistent : limit.IsSequentiallyConsistent
      ((menu).decisionRecall Initial horizon scheduler).decisionInformationAntichain)
    (freeOptimal : ∀ who (site : (R).InformationSite who),
      FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
      ∀ law : PMF ((R).Choice who site.1),
        (limit.continuationContext ((menu).bounded Initial horizon scheduler).wellFoundedHistories
          site (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state
            who)).value ((limit.strategy who).withLaw site.1 law) ≤
        (limit.continuationContext ((menu).bounded Initial horizon scheduler).wellFoundedHistories
          site (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state
            who)).value (limit.strategy who))
    (comparisonError : ℕ → ℝ) (errorVanishes : Tendsto comparisonError atTop (nhds 0))
    (comparisons : ∀ n who (site : (R).InformationSite who),
      ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
      ∀ choice : (R).Choice who site.1,
        localGain (2 * horizon + 1) (fun final => final.state)
            (recoveryExclusionBase parameter utility excludedPayoff) (sequence n) site
            (PMF.pure choice) ≤ comparisonError n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                (recoveryExclusionBase parameter utility excludedPayoff) (sequence n) site
                (PMF.pure choice) ≤
              expect mixture (fun deviation =>
                let compared := setup.intendedModel.assessmentComparisonWith
                  (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
                  (intendedReadoutExclusion setup parameter utility excludedPayoff)
                  (sourceSequence n) who deviation
                expect compared.alternative (fun outcome => outcome.2 who) -
                  expect compared.prescribed (fun outcome => outcome.2 who)) + comparisonError n) :
    limit.IsSequentialEquilibriumFor
        ((menu).decisionRecall Initial horizon scheduler).decisionInformationAntichain
        (fun who site => limit.truncatedContinuationContext site
          (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state who)
          (2 * horizon + 1)) ∧
      ((R).runBehavioral limit.strategy (2 * horizon + 1)).map (fun final =>
        (sourceReadout setup leaks (protocolState (runtime setup) leaks final.state),
          recoveryExclusionBase parameter utility excludedPayoff final.state)) =
        (setup.intendedModel.runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  let sourceObserve := intendedReadoutExclusion setup parameter utility excludedPayoff
  let targetObserve := fun final : (RP).History =>
    (sourceReadout setup leaks (protocolState (runtime setup) leaks final.state),
      recoveryExclusionBase parameter utility excludedPayoff final.state)
  let payoff := fun outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
    fun who => outcome.2 who
  choose sourceError sourceNonnegative sourceVanishes sourceBound using fun who =>
    sourceConverges.exists_uniform_policy_gain_bound who
      (fun final => payoff (sourceObserve final) who) (instructionCount setup.program + 1)
        (sourceRational who)
  let totalSourceError := fun n => ∑ who, sourceError who n
  have totalNonnegative : ∀ n, 0 ≤ totalSourceError n :=
    fun n => Finset.sum_nonneg fun who _ => sourceNonnegative who n
  have totalVanishes : Tendsto totalSourceError atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun who _ => sourceVanishes who)
  have sourceLe : ∀ n who, sourceError who n ≤ totalSourceError n :=
    fun n who => Finset.single_le_sum (fun other _ => sourceNonnegative other n)
      (Finset.mem_univ who)
  have mixtureBound (n : ℕ) (who : Player)
      (mixture : PMF (setup.intendedModel.AssessmentDeviation who)) :
      expect mixture (fun deviation =>
        let compared := setup.intendedModel.assessmentComparisonWith
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1)) sourceObserve
            (sourceSequence n) who deviation
        expect compared.alternative (payoff · who) -
          expect compared.prescribed (payoff · who)) ≤ totalSourceError n := by
    obtain ⟨largest, largestBound⟩ :=
      (Set.finite_range fun final : setup.intendedProtocol.History =>
        |payoff (sourceObserve final) who|).bddAbove
    have bounded : ∀ final : setup.intendedProtocol.History,
        |payoff (sourceObserve final) who| ≤ largest :=
      fun final => largestBound ⟨final, rfl⟩
    have largestNonnegative : 0 ≤ largest :=
      (abs_nonneg _).trans (bounded setup.intendedProtocol.initHistory)
    have gainBounded (deviation : setup.intendedModel.AssessmentDeviation who) :
        |expect (setup.intendedModel.assessmentComparisonWith
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              sourceObserve (sourceSequence n) who deviation).alternative (payoff · who) -
          expect (setup.intendedModel.assessmentComparisonWith
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              sourceObserve (sourceSequence n) who deviation).prescribed (payoff · who)| ≤
            2 * largest := by
      simp only [assessmentComparisonWith, expect_map, Function.comp_def]
      have first := expect_abs_le_of_bounded
        (μ := setup.intendedModel.assessmentLawWith
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
          (sourceSequence n) deviation.1 deviation.2) largestNonnegative bounded
      have second := expect_abs_le_of_bounded
        (μ := setup.intendedModel.assessmentLawWith
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
          (sourceSequence n) deviation.1 ((sourceSequence n).strategy who))
        largestNonnegative bounded
      exact (abs_sub _ _).trans (by linarith)
    apply (expect_le_const mixture _
      (payoffIntegrable_of_bounded mixture _ (C := 2 * largest) gainBounded)
      (sourceError who n) ?_).trans
        (sourceLe n who)
    intro deviation _supported
    simp only [assessmentComparisonWith, expect_map]
    exact sourceBound who n deviation.1 deviation.2
  have gainEq (n : ℕ) (who : Player) (site : (R).InformationSite who)
      (law : PMF ((R).Choice who site.1)) :
      localGain (2 * horizon + 1) targetObserve payoff (sequence n) site law =
        localGain (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (sequence n) site law := by
    simp only [localGain, assessmentComparisonWith, expect_map, targetObserve, payoff,
      Function.comp_def]
  have choicesBound (n : ℕ) (who : Player) (site : (R).InformationSite who)
      (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
      (choice : (R).Choice who site.1) :
      localGain (2 * horizon + 1) targetObserve payoff (sequence n) site (PMF.pure choice) ≤
        comparisonError n + totalSourceError n := by
    rw [gainEq]
    rcases comparisons n who site notFree choice with harmless | ⟨mixture, sourced⟩
    · exact harmless.trans (le_add_of_nonneg_right (totalNonnegative n))
    · have bounded := mixtureBound n who mixture
      dsimp only [sourceObserve, payoff] at bounded
      exact sourced.trans (by
        simpa only [add_comm] using add_le_add_right bounded (comparisonError n))
  have allLawsBound (n : ℕ) (who : Player) (site : (R).InformationSite who)
      (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
      (law : PMF ((R).Choice who site.1)) :
      localGain (2 * horizon + 1) targetObserve payoff (sequence n) site law ≤
        comparisonError n + totalSourceError n := by
    let : Finite ((R).Choice who site.1) :=
      (R).finite_choice_of_played ((R).site_mem_playedInformation site)
    have affine := localGain_bind (2 * horizon + 1) targetObserve payoff (sequence n) site
      ((menu).bounded Initial horizon scheduler)
      ((menu).decisionRecall Initial horizon scheduler).actsOnceWhereItMatters law PMF.pure
    rw [PMF.bind_pure] at affine
    rw [affine]
    exact expect_le_const law _ (payoffIntegrable_of_finite _ _)
      (comparisonError n + totalSourceError n)
      (fun choice _ => choicesBound n who site notFree choice)
  obtain ⟨lawError, lawVanishes, initialized⟩ :=
    recovery_initialized_lawApproximation (setup := setup) (leaks := leaks) (bounds := bounds)
      (horizon := horizon) (scheduler := scheduler) (wellFormed := wellFormed) (covers := covers)
      (capacity := capacity) (sequence := sourceSequence) (scale := scale) (positive := positive)
      (le_one := le_one) (weights := weights) (fallback := fallback) (opportunity := opportunity)
      (inclusion := inclusion) (timely := timely) (completes := completes) (parameter := parameter)
      (utility := utility) (excludedPayoff := excludedPayoff)
      (strategies := fun n => (sequence n).strategy) (allAssembled := assembled)
      (vanishing := vanishes)
  apply sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve targetObserve
    (instructionCount setup.program + 1) (2 * horizon + 1)
    ((menu).bounded Initial horizon scheduler) ((menu).decisionRecall Initial horizon scheduler)
    payoff source sourceSequence sourceConverges sourceRational sequence
    (fun _ site => ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (fun n => comparisonError n + totalSourceError n)
    (by simpa only [zero_add] using errorVanishes.add totalVanishes)
    (fun n who site notFree law => Or.inl (allLawsBound n who site notFree law))
    lawError lawVanishes initialized limit index increasing converges consistent
  intro who site free law
  rw [← limit.continuationContext_eq_truncated_of_bounded
    ((menu).bounded Initial horizon scheduler).wellFoundedHistories
      ((menu).bounded Initial horizon scheduler)]
  exact freeOptimal who site (not_not.mp free) law

end Vegas.RecoveryOnePacket

end
