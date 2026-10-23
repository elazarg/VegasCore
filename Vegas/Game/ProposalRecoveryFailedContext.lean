/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryFailedLocalLaw
import Vegas.Game.ProposalRecoveryGains

/-! # Actual assessed conditional gains in already failed enriched attempts -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
  (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
    PMF (setup.CommitRecoveryValueChoice who key.1))

local notation "baseline" => setup.proposalRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values

open Classical in
/-- Integrating the original assessment belief preserves the failed-window
image equality. No Bayes relation to an ordinary representative is assumed. -/
theorem proposalRecovery_normalized_failed_belief_terminal_eq
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        baseline who (setup.proposalRecoveryModel.infoOf who history.trace))
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (failed : ∀ history : setup.proposalRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧ first.NewFailure)
    (leftLaw rightLaw : PMF (setup.proposalRecoveryModel.Choice focal site.1))
    (marginals : leftLaw.map
        (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic))) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic)))) :
    ((assessment.belief focal site).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
          assessment.strategy focal ((assessment.strategy focal).withLaw site.1 leftLaw))
          history.1).map setup.proposalRecoveryErasedHistory =
      ((assessment.belief focal site).bind fun history =>
        setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
            assessment.strategy focal ((assessment.strategy focal).withLaw site.1 rightLaw))
            history.1).map setup.proposalRecoveryErasedHistory := by
  classical
  have actual := setup.proposalRecovery_local_terminal_prescribed assessment
    (fun who key => setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values who key))
    prescribed certificate focal site.1
  simp only [PMF.map_bind]
  apply bind_congr_on_support
  intro history _supported
  rw [actual leftLaw history.1, actual rightLaw history.1]
  obtain ⟨first, state, committing, newFailure⟩ := failed history
  rcases history with ⟨⟨current, trace⟩, atSite⟩
  dsimp only at state atSite
  subst current
  exact setup.proposalRecoveryNormalizedTrembledProfile_failed_local_terminal_eq omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values certificate focal first trace committing
    newFailure site.1 atSite leftLaw rightLaw marginals

open Classical in
/-- The entire current action-value vector is constant on laws with the
same omission marginal at a known-failed actual information site. -/
theorem proposalRecovery_normalized_failed_conditional_value_eq
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        baseline who (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (failed : ∀ history : setup.proposalRecoveryModel.InformationHistory focal site.1,
      ∃ first, history.1.state = some first ∧
        ProtocolState.atCommit setup.program first.point = true ∧ first.NewFailure)
    (leftLaw rightLaw : PMF (setup.proposalRecoveryModel.Choice focal site.1))
    (marginals : leftLaw.map
        (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic))) =
      rightLaw.map (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic)))) :
    (assessment.continuationContext certificate site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw site.1 leftLaw) =
      (assessment.continuationContext certificate site
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((assessment.strategy focal).withLaw site.1 rightLaw) := by
  have image := setup.proposalRecovery_normalized_failed_belief_terminal_eq omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values assessment prescribed certificate
    focal site failed leftLaw rightLaw marginals
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  simpa only [Function.comp_def, ← setup.proposalRecoveryPayoff_eq_image] using
    expect_observed_law_eq _ _ setup.proposalRecoveryErasedHistory
      setup.proposalRecoveryErasedHistory
      (setup.proposalRecoveryImagePayoff utility excludedPayoff focal) image

end Vegas.SourceProgram.Setup
