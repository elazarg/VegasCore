/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryCommitLimit
import Vegas.Game.CommitRecoveryHonestLimit
import Vegas.Game.CommitRecoveryNoncommitLimit
import GameTheory.Analysis.Protocol.SequentialOneShot

/-! # Sequential rationality of the same selected recovery source limit

The actual normalized pooled construction, honest preservation and original
terminal comparisons give every raw one-shot incentive in the SAME limit.
Perfect recall yields source sequential equilibrium; the original honest
initialized joint law is retained by that same assessment.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The SAME source limit is sequentially consistent and rational against
all original continuation deviations, and retains the given honest joint
law. No individual extended-game incentive premise is supplied. -/
theorem commitRecovery_normalized_pooled_limit_sequentialEquilibrium
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    [Fintype setup.commitRecoveryProtocol.History]
    (wellFormed : setup.WellFormed)
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    (target : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (source n).IsFullyMixed)
    (sourceBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.intendedModel (source n) setup.intended_decision_antichain)
    (targetMixed : ∀ n, (target n).IsFullyMixed)
    (targetBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (target n) setup.commitRecoveryModel_decisionAntichain)
    (sourceLimit : setup.intendedModel.BehavioralAssessment)
    (targetLimit : setup.commitRecoveryModel.BehavioralAssessment)
    (sourceConverges : InformationModel.BehavioralAssessmentConvergesPointwise source sourceLimit)
    (targetConverges : InformationModel.BehavioralAssessmentConvergesPointwise target targetLimit)
    (omission bad floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badSmall : ∀ n, bad n < 1)
    (floorNonnegative : ∀ n, 0 ≤ floor n) (floorSmall : ∀ n, floor n < 1)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (target n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badNonnegative n) (badSmall n).le
          (setup.commitRecoveryPooledDomainLaw finite
            (floor n) (floorNonnegative n) (floorSmall n).le
            (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
            (weights n)) who (setup.commitRecoveryModel.infoOf who history.trace))
    (reach : ℕ → ℝ) (reachPositive : ∀ n, 0 < reach n)
    (reachBound : ∀ n who (site : setup.intendedModel.InformationSite who), reach n ≤
      (setup.intendedModel.informationMass (source n).strategy who site).toReal)
    (omissionRate : ∀ n, omission n ≤ relativeTremble reach n)
    (badRate : ∀ n, bad n ≤ relativeTremble reach n)
    (floorRate : ∀ n, floor n ≤ relativeTremble reach n)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
        setup.commitRecoveryComponentGain finite (target n)
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badNonnegative n) (badSmall n).le
          (floor n) (floorNonnegative n) (floorSmall n).le
          (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
          alternative utility excludedPayoff agent ≤ 0)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (equilibrium : sourceLimit.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who history => (setup.protocolReadout history.state).elim 0
        (fun terminal => utility terminal who))) :
    targetLimit.IsSequentialEquilibrium setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (setup.commitRecoveryPayoff utility excludedPayoff) ∧
    (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
      sourceLimit.strategy targetLimit.strategy ∧
    (∀ fuel, (setup.intendedModel.runBehavioral sourceLimit.strategy fuel).map
        (fun history => (setup.protocolReadout history.state,
          fun who => (setup.protocolReadout history.state).elim 0
            (fun terminal => utility terminal who))) =
      (setup.commitRecoveryModel.runBehavioral targetLimit.strategy fuel).map
        (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
          fun who => setup.commitRecoveryPayoff utility excludedPayoff who history))) := by
  classical
  have honestProof := setup.commitRecovery_normalized_honest_limit finite wellFormed source target
    sourceMixed sourceBayes targetMixed targetBayes sourceLimit targetLimit sourceConverges
    targetConverges omission bad floor omissionPositive omissionSmall badNonnegative badSmall
    floorNonnegative floorSmall weights prescribed reach reachPositive reachBound
    omissionRate badRate floorRate utility excludedPayoff (fun terminal _who => below terminal)
    equilibrium
  have rateLimit := relativeTremble_tendsto reach reachPositive
  have omissionLimit := squeeze_zero (fun n => (omissionPositive n).le) omissionRate rateLimit
  have badLimit := squeeze_zero badNonnegative badRate rateLimit
  have floorLimit := squeeze_zero floorNonnegative floorRate rateLimit
  have localOptimal (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
      (law : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
      (targetLimit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((targetLimit.strategy focal).withLaw site.1 law) ≤
        (targetLimit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
          site (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
            (targetLimit.strategy focal) := by
    by_cases committing : site.1.1.1.1.elim false
        (ProtocolView.atCommit focal setup.program) = true
    · exact setup.commitRecovery_pooled_commitment_limit_localOptimal finite omission bad floor
        (fun n => (omissionPositive n).le) (fun n => (omissionSmall n).le)
        badNonnegative (fun n => (badSmall n).le) floorNonnegative
        (fun n => (floorSmall n).le) wellFormed (fun n => (source n).strategy)
        omissionLimit badLimit floorLimit target targetLimit targetConverges targetMixed
        targetBayes weights prescribed utility excludedPayoff pooled honestProof.2.2.1
        focal site committing below law
    · have notCommit : site.1.1.1.1.elim false
          (ProtocolView.atCommit focal setup.program) = false := by
        cases flag : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program)
        · rfl
        · exact (committing flag).elim
      exact setup.commitRecovery_normalized_noncommit_limit_localOptimal target targetLimit
        targetConverges omission bad (fun n => (omissionPositive n).le)
        (fun n => (omissionSmall n).le) badNonnegative (fun n => (badSmall n).le)
        (fun n => setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
          (floorSmall n).le
          (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy) (weights n))
        prescribed omissionLimit utility excludedPayoff below focal site notCommit law
  have decisionRecall := setup.commitRecoveryModel.decisionRecall_of_perfectRecall
    setup.commitRecoveryModel_perfectRecall
  have consistent := targetConverges.isSequentiallyConsistent
    setup.commitRecoveryModel_decisionAntichain targetMixed targetBayes
  refine ⟨?_, honestProof.1, honestProof.2.2.2⟩
  exact (InformationModel.BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal
    setup.commitRecoveryModel decisionRecall targetLimit
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    (setup.commitRecoveryPayoff utility excludedPayoff)).mpr ⟨consistent, localOptimal⟩

end Vegas.SourceProgram.Setup
