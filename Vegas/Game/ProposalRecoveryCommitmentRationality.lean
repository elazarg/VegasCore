/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPooledRawLimit
import Vegas.Game.ProposalRecoveryPinnedLimit
import Vegas.Game.ProposalRecoveryFailedLimit

/-! # All original commitment-site incentives of the selected source limit

Actual honest pins, free ordinary pools and genuinely known-failed fibers
exhaust every original commitment decision. The same source limit is locally
optimal against every raw current law at all of them.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  [Fintype setup.proposalRecoveryProtocol.History]
  (omission bad delivery floor : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliveryBounded : ∀ n, delivery n ≤ 1)
  (floorNonnegative : ∀ n, 0 ≤ floor n) (floorBounded : ∀ n, floor n ≤ 1)
  (wellFormed : setup.WellFormed)
  (honest : ℕ → ∀ who, setup.intendedModel.BehavioralPolicy who)
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (deliveryVanishes : Tendsto delivery atTop (nhds 0))
  (floorVanishes : Tendsto floor atTop (nhds 0))

include omissionVanishes badVanishes deliveryVanishes floorVanishes

open Classical in
/-- Every original commitment information site has a full raw local best
response at the SAME selected source limit. The pin witness, ordinary versus
failed classification, attachment indifference and free domain optimum are
derived from the actual construction and original continuation laws. -/
theorem proposalRecovery_pooled_commitment_limit_localOptimal
    (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
    (limit : setup.proposalRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel (sequence n) setup.proposalRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
          (setup.proposalRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (setup.proposalRecoveryHonestPoolPins wellFormed (honest n))
            (weights n)) who
              (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.proposalRecoveryAgentPool agent = pool),
        setup.proposalRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
          (floor n) (floorNonnegative n) (floorBounded n)
          (setup.proposalRecoveryHonestPoolPins wellFormed (honest n))
          alternative utility excludedPayoff agent ≤ 0)
    (honestOptimal : ∀ who (source : setup.intendedModel.InformationSite who)
      (localLaw : PMF (setup.proposalRecoveryModel.Choice who
        ((setup.proposalRecoveryRestriction wellFormed).site who source).1)),
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        ((setup.proposalRecoveryRestriction wellFormed).site who source)
        (setup.proposalRecoveryPayoff utility excludedPayoff who)).value
          ((limit.strategy who).withLaw
            ((setup.proposalRecoveryRestriction wellFormed).site who source).1 localLaw) ≤
        (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          ((setup.proposalRecoveryRestriction wellFormed).site who source)
          (setup.proposalRecoveryPayoff utility excludedPayoff who)).value (limit.strategy who))
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let pins := fun n => setup.proposalRecoveryHonestPoolPins wellFormed (honest n)
  let oldInfo := setup.proposalRecoveryEraseInfo focal site.1
  have oldCommit : oldInfo.1.1.1.elim false
      (ProtocolView.atCommit focal setup.program) = true := committing
  by_cases ordinary : oldInfo.1.1.2.1 = setup.commitRecoverySavedExclusions focal oldInfo
  · obtain ⟨⟨⟨state, trace⟩, observed⟩, _running, _offered⟩ := site.property
    have clock := setup.commitRecovery_atCommit_info focal (setup.proposalRecoveryEraseTrace trace)
    rw [← setup.proposalRecoveryEraseInfo_observed, observed] at clock
    change site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = _ at clock
    have firstCommit := clock.symm.trans committing
    cases state with
    | none => cases firstCommit
    | some first =>
        obtain ⟨prior, kept, rank⟩ := setup.commitRecovery_attempt_entry first
          (setup.proposalRecoveryEraseTrace trace) firstCommit
        have read := setup.commitRecoverySavedExclusions_of_entry focal first
          (setup.proposalRecoveryEraseTrace trace) prior kept rank
        have signal : (setup.commitRecoveryModel.infoOf focal
            (setup.proposalRecoveryEraseTrace trace)).1.1 =
            (setup.commitRecoveryPrivate focal (some first),
              setup.commitRecoveryPublic (some first)) := by
          change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf focal _).1.1 = _
          rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
        have unchanged : first.excluded = first.entryExcluded := by
          change (setup.proposalRecoveryEraseInfo focal site.1).1.1.2.1 =
            setup.commitRecoverySavedExclusions focal
              (setup.proposalRecoveryEraseInfo focal site.1) at ordinary
          rw [← observed, setup.proposalRecoveryEraseInfo_observed, signal, read] at ordinary
          exact ordinary
        let pool := setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site)
        by_cases pinned : pins 0 pool = none
        · have unpinned (n : ℕ) : pins n pool = none :=
            (setup.proposalRecoveryHonestPoolPins_absent_iff wellFormed
              (honest 0) (honest n) pool).mp pinned
          exact setup.proposalRecovery_pooled_ordinary_limit_localOptimal finite
            omission bad delivery floor omissionNonnegative omissionBounded
              badNonnegative badBounded
            deliveryNonnegative deliveryBounded floorNonnegative floorBounded pins
            omissionVanishes badVanishes deliveryVanishes floorVanishes
            sequence limit converges mixed bayes weights prescribed utility excludedPayoff pooled
            focal site first trace observed firstCommit unchanged unpinned below law
        · exact setup.proposalRecovery_limit_pinned_localOptimal finite wellFormed sequence limit
            converges mixed bayes
            (fun n who key => setup.proposalRecoveryComponentTrembledLaw who key
              (omission n) (omissionNonnegative n) (omissionBounded n)
              (bad n) (badNonnegative n) (badBounded n)
              (delivery n) (deliveryNonnegative n) (deliveryBounded n)
              (setup.proposalRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
                (floorBounded n) (pins n) (weights n) who key))
            prescribed utility excludedPayoff honestOptimal (honest 0) focal site
            first trace observed unchanged pinned law
  · have failed : ∀ history : setup.proposalRecoveryModel.InformationHistory focal site.1,
        ∃ current, history.1.state = some current ∧
          ProtocolState.atCommit setup.program current.point = true ∧ current.NewFailure := by
      intro history
      rcases history with ⟨⟨state, trace⟩, observed⟩
      have currentCommit := committing
      have clock := setup.commitRecovery_atCommit_info focal
        (setup.proposalRecoveryEraseTrace trace)
      rw [← setup.proposalRecoveryEraseInfo_observed, observed] at clock
      change site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = _ at clock
      rw [clock] at currentCommit
      cases state with
      | none => cases currentCommit
      | some current =>
          obtain ⟨prior, kept, rank⟩ := setup.commitRecovery_attempt_entry current
            (setup.proposalRecoveryEraseTrace trace) currentCommit
          have read := setup.commitRecoverySavedExclusions_of_entry focal current
            (setup.proposalRecoveryEraseTrace trace) prior kept rank
          have signal : (setup.commitRecoveryModel.infoOf focal
              (setup.proposalRecoveryEraseTrace trace)).1.1 =
              (setup.commitRecoveryPrivate focal (some current),
                setup.commitRecoveryPublic (some current)) := by
            change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf focal _).1.1 = _
            rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
          have different : current.excluded ≠ current.entryExcluded := by
            have actual := ordinary
            change (setup.proposalRecoveryEraseInfo focal site.1).1.1.2.1 ≠
              setup.commitRecoverySavedExclusions focal
                (setup.proposalRecoveryEraseInfo focal site.1) at actual
            rw [← observed, setup.proposalRecoveryEraseInfo_observed, signal, read] at actual
            exact actual
          refine ⟨current, rfl, currentCommit, ?_⟩
          apply Finset.sdiff_nonempty.mpr
          intro included
          exact different (Finset.Subset.antisymm included current.entered)
    exact setup.proposalRecovery_normalized_failed_limit_localOptimal sequence limit converges
      omission bad delivery omissionNonnegative omissionBounded badNonnegative badBounded
      deliveryNonnegative deliveryBounded
      (fun n => setup.proposalRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
        (floorBounded n) (pins n) (weights n)) prescribed omissionVanishes
      utility excludedPayoff below focal site committing failed law

end Vegas.SourceProgram.Setup
