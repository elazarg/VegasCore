/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryLocalLaw
import Vegas.Game.ProposalRecoveryPayoff

/-! # Conditional action values in the actual enriched source assessment -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem actual_bayes
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel assessment setup.proposalRecoveryModel_decisionAntichain)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who) :
    assessment.belief who site =
      setup.proposalRecoveryModel.bayesBelief assessment.strategy who site
      (setup.proposalRecoveryModel_decisionAntichain who site)
      (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
        assessment.strategy mixed who site) := by
  ext history
  rw [setup.proposalRecoveryModel.bayesBelief_apply]
  exact bayes who site
    (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
      assessment.strategy mixed who site) history

open Classical in
theorem proposalRecovery_local_terminal_prescribed
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryPrescribedProfile prescription who
          (setup.proposalRecoveryModel.infoOf who history.trace))
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.proposalRecoveryModel.InfoState focal)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site))
    (history : setup.proposalRecoveryProtocol.History) :
    setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
        assessment.strategy focal ((assessment.strategy focal).withLaw site law)) history =
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
          (setup.proposalRecoveryPrescribedProfile prescription) focal
          ((setup.proposalRecoveryPrescribedProfile prescription focal).withLaw site law))
            history := by
  apply setup.proposalRecoveryModel.runBehavioralTerminalFrom_congr certificate history
  intro later _ running who
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same, Profile.update_same]
    by_cases here : setup.proposalRecoveryModel.infoOf focal later.trace = site
    · subst site
      exact (InformationModel.BehavioralPolicy.withLaw_self _ _ _).trans
        (InformationModel.BehavioralPolicy.withLaw_self _ _ _).symm
    · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here,
        InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here]
      exact prescribed focal later running
  · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]
    exact prescribed who later running

open Classical in
/-- The original assessment's conditional action values agree on actual
full erased-information/archive copies. Beliefs, every chance factor, and
whole continuations through recovery are derived from the original game. -/
theorem proposalRecovery_conditional_value_eq
    (finite : setup.program.FiniteBindingTypes)
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel assessment setup.proposalRecoveryModel_decisionAntichain)
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryPrescribedProfile prescription who
          (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1)
    (law : PMF (setup.ProposalRecoveryComponentChoice focal
      (setup.proposalRecoveryQuery focal source.1))) :
    let query := setup.proposalRecoveryQuery focal source.1
    let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
      prescription focal
        (setup.proposalRecoveryPrescriptionWithLaw focal (prescription focal) query law)
    let changed := setup.proposalRecoveryPrescribedProfile updated
    (assessment.continuationContext certificate source
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw source.1 (changed focal source.1)) =
      (assessment.continuationContext certificate target
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((assessment.strategy focal).withLaw target.1 (changed focal target.1)) := by
  classical
  dsimp only
  let query := setup.proposalRecoveryQuery focal source.1
  let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
    prescription focal
      (setup.proposalRecoveryPrescriptionWithLaw focal (prescription focal) query law)
  let baseline := setup.proposalRecoveryPrescribedProfile prescription
  let changed := setup.proposalRecoveryPrescribedProfile updated
  have compareAt (site : setup.proposalRecoveryModel.InformationSite focal)
      (current : PMF (setup.proposalRecoveryModel.Choice focal site.1)) :
      ((assessment.belief focal site).bind fun history =>
        setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
            assessment.strategy focal
            ((assessment.strategy focal).withLaw site.1 current)) history.1).map
              setup.proposalRecoveryErasedHistory =
        ((setup.proposalRecoveryModel.bayesBelief assessment.strategy focal site
          (setup.proposalRecoveryModel_decisionAntichain focal site)
          (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
            assessment.strategy mixed focal site)).bind fun history =>
          setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
            (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
              baseline focal ((baseline focal).withLaw site.1 current)) history.1).map
                setup.proposalRecoveryErasedHistory := by
    rw [setup.actual_bayes assessment mixed bayes focal site]
    apply congrArg (PMF.map _)
    apply congrArg (PMF.bind _)
    funext history
    exact setup.proposalRecovery_local_terminal_prescribed
      assessment prescription prescribed certificate
      focal site.1 current history.1
  have shared := setup.proposalRecovery_bayes_local_terminal_eq finite assessment.strategy mixed
    prescription certificate focal target source semantic archive law
  dsimp only at shared
  have observed := (compareAt source (changed focal source.1)).trans
    (shared.trans (compareAt target (changed focal target.1)).symm)
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  simpa only [Function.comp_def, ← setup.proposalRecoveryPayoff_eq_image] using
    expect_observed_law_eq _ _ setup.proposalRecoveryErasedHistory
      setup.proposalRecoveryErasedHistory
      (setup.proposalRecoveryImagePayoff utility excludedPayoff focal) observed

open Classical in
/-- The actual assessed baseline value is shared by ordinary erased copies,
with no assumption on their positive reach in a limiting assessment. -/
theorem proposalRecovery_baseline_value_eq
    (finite : setup.program.FiniteBindingTypes)
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel assessment setup.proposalRecoveryModel_decisionAntichain)
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryPrescribedProfile prescription who
          (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1) :
    (assessment.continuationContext certificate source
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        (assessment.strategy focal) =
      (assessment.continuationContext certificate target
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (assessment.strategy focal) := by
  classical
  have atSite (site : setup.proposalRecoveryModel.InformationSite focal) :
      assessment.strategy focal site.1 =
        setup.proposalRecoveryPrescribedProfile prescription focal site.1 := by
    obtain ⟨history, running, _active⟩ := site.2
    have selected := prescribed focal history.1 running
    rw [history.2] at selected
    exact selected
  have shared := setup.proposalRecovery_conditional_value_eq finite assessment mixed bayes
    prescription prescribed utility excludedPayoff certificate focal target source semantic archive
    (prescription focal (setup.proposalRecoveryQuery focal source.1))
  dsimp only at shared
  simp only [setup.proposalRecoveryPrescriptionWithLaw_eq_self, Profile.update_eq_self] at shared
  rw [← atSite source, ← atSite target] at shared
  simpa only [InformationModel.BehavioralPolicy.withLaw_eq_self] using shared

open Classical in
/-- Conditional deviation gains agree at ordinary full-information copies.
This is the action-vector comparison used by component completion. -/
theorem proposalRecovery_conditional_gain_eq
    (finite : setup.program.FiniteBindingTypes)
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel assessment setup.proposalRecoveryModel_decisionAntichain)
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryPrescribedProfile prescription who
          (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1)
    (law : PMF (setup.ProposalRecoveryComponentChoice focal
      (setup.proposalRecoveryQuery focal source.1))) :
    let query := setup.proposalRecoveryQuery focal source.1
    let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
      prescription focal
        (setup.proposalRecoveryPrescriptionWithLaw focal (prescription focal) query law)
    let changed := setup.proposalRecoveryPrescribedProfile updated
    (assessment.continuationContext certificate source
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw source.1 (changed focal source.1)) -
      (assessment.continuationContext certificate source
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (assessment.strategy focal) =
      (assessment.continuationContext certificate target
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((assessment.strategy focal).withLaw target.1 (changed focal target.1)) -
        (assessment.continuationContext certificate target
          (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
            (assessment.strategy focal) := by
  exact congrArg₂ (fun alternative baseline : ℝ => alternative - baseline)
    (setup.proposalRecovery_conditional_value_eq finite assessment mixed bayes prescription
      prescribed utility excludedPayoff certificate focal target source semantic archive law)
    (setup.proposalRecovery_baseline_value_eq finite assessment mixed bayes prescription
      prescribed utility excludedPayoff certificate focal target source semantic archive)

end Vegas.SourceProgram.Setup
