/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoverySelectedEquilibrium
import Vegas.Game.CommitRecoveryReference
import GameTheory.Protocol.RestrictionExecution

/-! # A source equilibrium with its original pooled construction witness

Independent omission, accepted-failure and domain-floor rates are fixed before
completion. The entire selected sequence and its shared domain laws remain
available, on the same strict subsequence that supplies the equilibrium limit.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- Arbitrary positive rates below the original honest reach scale produce
an actual pooled source construction whose SAME limit is sequentially rational
and preserves the honest initialized history law. -/
theorem exists_commitRecovery_sequentialEquilibrium_construction
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    [Fintype setup.commitRecoveryProtocol.History]
    (wellFormed : setup.WellFormed)
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceLimit : setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (source n).IsFullyMixed)
    (sourceBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.intendedModel (source n) setup.intended_decision_antichain)
    (sourceConverges : InformationModel.BehavioralAssessmentConvergesPointwise source sourceLimit)
    (reach : ℕ → ℝ) (reachPositive : ∀ n, 0 < reach n)
    (reachBound : ∀ n who (site : setup.intendedModel.InformationSite who), reach n ≤
      (setup.intendedModel.informationMass (source n).strategy who site).toReal)
    (omission bad floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badPositive : ∀ n, 0 < bad n) (badSmall : ∀ n, bad n < 1)
    (floorPositive : ∀ n, 0 < floor n) (floorSmall : ∀ n, floor n < 1)
    (omissionRate : ∀ n, omission n ≤ relativeTremble reach n)
    (badRate : ∀ n, bad n ≤ relativeTremble reach n)
    (floorRate : ∀ n, floor n ≤ relativeTremble reach n)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (equilibrium : sourceLimit.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who history => (setup.protocolReadout history.state).elim 0
        (fun terminal => utility terminal who))) :
    ∃ (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
        PMF (setup.CommitRecoveryPoolPart finite pool))
      (target : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
      (limit : setup.commitRecoveryModel.BehavioralAssessment) (index : ℕ → ℕ),
      (∀ n, (target n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        setup.commitRecoveryModel (target n) setup.commitRecoveryModel_decisionAntichain) ∧
      StrictMono index ∧
      InformationModel.BehavioralAssessmentConvergesPointwise
        (fun n => target (index n)) limit ∧
      (∀ n who (history : setup.commitRecoveryProtocol.History)
          (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
        (target n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
          setup.commitRecoveryNormalizedTrembledProfile
            (omission n) (omissionPositive n).le (omissionSmall n).le
            (bad n) (badPositive n).le (badSmall n).le
            (setup.commitRecoveryPooledDomainLaw finite
              (floor n) (floorPositive n).le (floorSmall n).le
              (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
              (weights n)) who (setup.commitRecoveryModel.infoOf who history.trace)) ∧
      (∀ n alternative pool,
        ∑ agent ∈ Finset.univ.filter
            (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
          setup.commitRecoveryComponentGain finite (target n)
            (omission n) (omissionPositive n).le (omissionSmall n).le
            (bad n) (badPositive n).le (badSmall n).le
            (floor n) (floorPositive n).le (floorSmall n).le
            (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
            alternative utility excludedPayoff agent ≤ 0) ∧
      (∀ n fuel,
        setup.commitRecoveryModel.runMixed
          (fun who => (setup.commitRecoveryFlagPlan finite who
            (omission n) (omissionPositive n).le (omissionSmall n).le
            (bad n) (badPositive n).le (badSmall n).le
            (setup.commitRecoveryPooledDomainLaw finite
              (floor n) (floorPositive n).le (floorSmall n).le
              (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
              (weights n) who)).map (setup.commitRecoveryNormalizedFlagPolicy finite who)) fuel =
          setup.commitRecoveryModel.runBehavioral (target n).strategy fuel) ∧
      limit.IsSequentialEquilibrium setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        (setup.commitRecoveryPayoff utility excludedPayoff) ∧
      (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
        sourceLimit.strategy limit.strategy ∧
      (∀ fuel, (setup.intendedModel.runBehavioral sourceLimit.strategy fuel).map
          (setup.commitRecoveryLiftHistory wellFormed) =
        setup.commitRecoveryModel.runBehavioral limit.strategy fuel) ∧
      (∀ fuel, (setup.intendedModel.runBehavioral sourceLimit.strategy fuel).map
          (fun history => (setup.protocolReadout history.state,
            fun who => (setup.protocolReadout history.state).elim 0
              (fun terminal => utility terminal who))) =
        (setup.commitRecoveryModel.runBehavioral limit.strategy fuel).map
          (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history))) := by
  classical
  let pins n := setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy
  let fallback (who : Player) : setup.commitRecoveryModel.Policy who := fun info =>
    ((setup.commitRecoveryReference finite).strategy who info).support_nonempty.choose
  obtain ⟨weights, target, limit, index, _assembled, mixed, bayes, increasing,
      converges, _consistent, gains, prescribed, runner⟩ :=
    setup.exists_consistent_commitRecovery_normalized_pool finite
      omission bad floor omissionPositive omissionSmall badPositive badSmall
      floorPositive floorSmall pins fallback (setup.commitRecoveryPayoff utility excludedPayoff)
  have honestConverges : InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => source (index n)) sourceLimit :=
    ⟨fun who site action => (sourceConverges.1 who site action).comp increasing.tendsto_atTop,
      fun who site history => (sourceConverges.2 who site history).comp increasing.tendsto_atTop⟩
  have subRate (n : ℕ) : relativeTremble reach (index n) ≤
      relativeTremble (fun n => reach (index n)) n := by
    unfold relativeTremble
    apply div_le_div_of_nonneg_left
      (le_min (reachPositive (index n)).le zero_le_one) (by positivity)
    have indexBound : n ≤ index n := increasing.id_le n
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right indexBound 1) 1
  have proof := setup.commitRecovery_normalized_pooled_limit_sequentialEquilibrium
    finite wellFormed (fun n => source (index n)) (fun n => target (index n))
    (fun n => sourceMixed (index n)) (fun n => sourceBayes (index n))
    (fun n => mixed (index n)) (fun n => bayes (index n)) sourceLimit limit
    honestConverges converges
    (fun n => omission (index n)) (fun n => bad (index n)) (fun n => floor (index n))
    (fun n => omissionPositive (index n)) (fun n => omissionSmall (index n))
    (fun n => (badPositive (index n)).le) (fun n => badSmall (index n))
    (fun n => (floorPositive (index n)).le) (fun n => floorSmall (index n))
    (fun n => weights (index n)) (fun n => prescribed (index n))
    (fun n => reach (index n)) (fun n => reachPositive (index n))
    (fun n who site => reachBound (index n) who site)
    (fun n => (omissionRate (index n)).trans (subRate n))
    (fun n => (badRate (index n)).trans (subRate n))
    (fun n => (floorRate (index n)).trans (subRate n))
    utility excludedPayoff (fun n alternative pool => gains (index n) alternative pool)
    below equilibrium
  exact ⟨weights, target, limit, index, mixed, bayes, increasing, converges,
    prescribed, gains, runner, proof.1, proof.2.1,
    fun fuel => (setup.commitRecoveryRestriction wellFormed).initialized_law
      sourceLimit.strategy limit.strategy proof.2.1 fuel, proof.2.2⟩

end Vegas.SourceProgram.Setup
