/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPinnedWitness
import Vegas.Game.ProposalRecoveryLimitCopies

/-! # Selected-site incentives at every ordinary pinned enriched information fiber -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
theorem proposalRecovery_limit_pinned_localOptimal
    (finite : setup.program.FiniteBindingTypes)
    [Fintype setup.proposalRecoveryProtocol.History] (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
    (limit : setup.proposalRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel (sequence n) setup.proposalRecoveryModel_decisionAntichain)
    (prescription : ℕ → (who : Player) → setup.ProposalRecoveryPrescription who)
    (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryPrescribedProfile (prescription n) who
          (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (honestOptimal : ∀ who (source : setup.intendedModel.InformationSite who)
      (law : PMF (setup.proposalRecoveryModel.Choice who
        (((setup.proposalRecoveryRestriction wellFormed).site who source).1))),
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        ((setup.proposalRecoveryRestriction wellFormed).site who source)
        (setup.proposalRecoveryPayoff utility excludedPayoff who)).value
          ((limit.strategy who).withLaw
            (((setup.proposalRecoveryRestriction wellFormed).site who source).1) law) ≤
        (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          ((setup.proposalRecoveryRestriction wellFormed).site who source)
          (setup.proposalRecoveryPayoff utility excludedPayoff who)).value (limit.strategy who))
    (origin : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (first : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some first))
    (atSite : setup.proposalRecoveryModel.infoOf focal trace = site.1)
    (unchanged : first.excluded = first.entryExcluded)
    (pinned : setup.proposalRecoveryHonestPoolPins wellFormed origin
      (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site)) ≠ none)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw site.1 law) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  obtain ⟨honest, semantic, archive⟩ := setup.proposalRecoveryHonestPoolPins_ordinary_witness
    wellFormed origin focal site first trace atSite unchanged pinned
  exact setup.proposalRecovery_normalized_limit_localOptimal_of_erased_copy finite
    sequence limit converges mixed bayes prescription prescribed utility excludedPayoff
    focal site ((setup.proposalRecoveryRestriction wellFormed).site focal honest)
    semantic archive (honestOptimal focal honest) law

end Vegas.SourceProgram.Setup
