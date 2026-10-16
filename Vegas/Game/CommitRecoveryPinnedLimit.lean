/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryOrdinaryLimitCopies
import Vegas.Game.CommitRecoveryHonestPoolWitness

/-! # Honest-pinned ordinary incentives of the original source limit

The actual pin selects a genuine intended decision witness. Ordinary copies
share its erased information, so the checked honest-limit raw incentives
transfer through the original assessment limit without an assumed decoder.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The ACTUAL honest pin and the already established honest-limit incentives
give every raw local comparison at an ordinary pinned source site. The honest
decision witness and its source-information equality are derived, not inputs. -/
theorem commitRecovery_normalized_limit_pinned_localOptimal
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    [Fintype setup.commitRecoveryProtocol.History] (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (limit : setup.commitRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain)
    (omission bad : ℕ → ℝ)
    (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
    (values : ℕ → (who : Player) → (info : setup.commitRecoveryModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n) (values n) who
            (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (honestOptimal : ∀ who (site : setup.intendedModel.InformationSite who)
      (law : PMF (setup.commitRecoveryModel.Choice who
        ((setup.commitRecoveryRestriction wellFormed).site who site).1)),
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        ((setup.commitRecoveryRestriction wellFormed).site who site)
        (setup.commitRecoveryPayoff utility excludedPayoff who)).value
          ((limit.strategy who).withLaw
            ((setup.commitRecoveryRestriction wellFormed).site who site).1 law) ≤
        (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
          ((setup.commitRecoveryRestriction wellFormed).site who site)
          (setup.commitRecoveryPayoff utility excludedPayoff who)).value (limit.strategy who))
    (origin : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (focal : Player) (ordinary : setup.commitRecoveryModel.InformationSite focal)
    (committing : ordinary.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (unchanged : ordinary.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal ordinary.1)
    (pinned : setup.commitRecoveryHonestPoolPins finite wellFormed origin
      (setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt ordinary)) ≠ none)
    (law : PMF (setup.commitRecoveryModel.Choice focal ordinary.1)) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories ordinary
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw ordinary.1 law) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories ordinary
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  obtain ⟨honest, same⟩ := setup.commitRecoveryHonestPoolPins_ordinary_witness
    finite wellFormed origin focal ordinary committing unchanged pinned
  exact setup.commitRecovery_normalized_limit_localOptimal_of_erased_copy
    sequence limit converges mixed bayes omission bad omissionNonnegative omissionBounded
    badNonnegative badBounded values prescribed utility excludedPayoff focal ordinary
    ((setup.commitRecoveryRestriction wellFormed).site focal honest) same
    (honestOptimal focal honest) law

end Vegas.SourceProgram.Setup
