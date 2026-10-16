/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPooledRawLimit
import Vegas.Game.CommitRecoveryPinnedLimit

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

private theorem honest_pin_absent_iff (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (first second : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (pool : setup.CommitRecoveryValuePool finite) :
    setup.commitRecoveryHonestPoolPins finite wellFormed first pool = none ↔
      setup.commitRecoveryHonestPoolPins finite wellFormed second pool = none := by
  classical
  unfold commitRecoveryHonestPoolPins
  split_ifs <;> simp

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  [Fintype setup.commitRecoveryProtocol.History]
  (omission bad floor : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (floorNonnegative : ∀ n, 0 ≤ floor n) (floorBounded : ∀ n, floor n ≤ 1)
  (wellFormed : setup.WellFormed)
  (honest : ℕ → ∀ who, setup.intendedModel.BehavioralPolicy who)
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (floorVanishes : Tendsto floor atTop (nhds 0))

include omissionVanishes badVanishes floorVanishes

open Classical in
/-- Every original commitment information site has a full raw local best
response at the SAME selected source limit. The pin witness, ordinary versus
failed classification, attachment indifference and free domain optimum are
derived from the actual construction and original continuation laws. -/
theorem commitRecovery_pooled_commitment_limit_localOptimal
    (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (limit : setup.commitRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (setup.commitRecoveryHonestPoolPins finite wellFormed (honest n))
            (weights n)) who
              (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
        setup.commitRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (floor n) (floorNonnegative n) (floorBounded n)
          (setup.commitRecoveryHonestPoolPins finite wellFormed (honest n))
          alternative utility excludedPayoff agent ≤ 0)
    (honestOptimal : ∀ who (source : setup.intendedModel.InformationSite who)
      (localLaw : PMF (setup.commitRecoveryModel.Choice who
        ((setup.commitRecoveryRestriction wellFormed).site who source).1)),
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        ((setup.commitRecoveryRestriction wellFormed).site who source)
        (setup.commitRecoveryPayoff utility excludedPayoff who)).value
          ((limit.strategy who).withLaw
            ((setup.commitRecoveryRestriction wellFormed).site who source).1 localLaw) ≤
        (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
          ((setup.commitRecoveryRestriction wellFormed).site who source)
          (setup.commitRecoveryPayoff utility excludedPayoff who)).value (limit.strategy who))
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (law : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let pins := fun n => setup.commitRecoveryHonestPoolPins finite wellFormed (honest n)
  by_cases ordinary : site.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal site.1
  · let pool := setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt site)
    by_cases pinned : pins 0 pool = none
    · have unpinned (n : ℕ) : pins n pool = none :=
        (setup.honest_pin_absent_iff finite wellFormed (honest 0) (honest n) pool).mp pinned
      exact setup.commitRecovery_pooled_ordinary_limit_localOptimal finite
        omission bad floor omissionNonnegative omissionBounded badNonnegative badBounded
        floorNonnegative floorBounded pins omissionVanishes badVanishes floorVanishes
        sequence limit converges mixed bayes weights prescribed utility excludedPayoff
        pooled focal site committing ordinary unpinned below law
    · exact setup.commitRecovery_normalized_limit_pinned_localOptimal finite wellFormed
        sequence limit converges mixed bayes omission bad omissionNonnegative omissionBounded
        badNonnegative badBounded
        (fun n => setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
          (floorBounded n) (pins n) (weights n)) prescribed utility excludedPayoff
        honestOptimal (honest 0) focal site committing ordinary pinned law
  · have failed : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
        ∃ current, history.1.state = some current ∧
          ProtocolState.atCommit setup.program current.point = true ∧ current.NewFailure := by
      intro history
      have active := InformationModel.InformationSite.active setup.commitRecoveryModel site history
      rcases history with ⟨⟨state, trace⟩, observed⟩
      have currentCommit := committing
      rw [← observed, setup.commitRecovery_atCommit_info] at currentCommit
      cases state with
      | none => cases currentCommit
      | some current =>
          obtain ⟨prior, kept, rank⟩ := setup.commitRecovery_attempt_entry
            current trace currentCommit
          have entryRead := setup.commitRecoverySavedExclusions_of_entry focal current trace
            prior kept rank
          have currentSignal : (setup.commitRecoveryModel.infoOf focal trace).1.1 =
              (setup.commitRecoveryPrivate focal (some current),
                setup.commitRecoveryPublic (some current)) := by
            change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf focal trace).1.1 = _
            rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
          have different : current.excluded ≠ current.entryExcluded := by
            have actual := ordinary
            rw [← observed, currentSignal, entryRead] at actual
            exact actual
          refine ⟨current, rfl, currentCommit, ?_⟩
          apply Finset.sdiff_nonempty.mpr
          intro included
          exact different (Finset.Subset.antisymm included current.entered)
    exact setup.commitRecovery_normalized_failed_limit_localOptimal sequence limit converges
      omission bad omissionNonnegative omissionBounded badNonnegative badBounded
      (fun n => setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
        (floorBounded n) (pins n) (weights n)) prescribed omissionVanishes
      utility excludedPayoff below focal site committing failed law

end Vegas.SourceProgram.Setup
