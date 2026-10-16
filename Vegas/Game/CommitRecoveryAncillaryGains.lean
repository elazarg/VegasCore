/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNormalizedLocalLaw

/-! # Conditional values at the actual normalized source assessment

Full mixing, Bayes' rule and the constructed genuine-history prescription
identify the original assessment's continuation values. No equality of
conditional gains or individual optimality is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem actual_bayes
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel assessment setup.commitRecoveryModel_decisionAntichain)
    (who : Player) (site : setup.commitRecoveryModel.InformationSite who) :
    assessment.belief who site = setup.commitRecoveryModel.bayesBelief assessment.strategy who site
      (setup.commitRecoveryModel_decisionAntichain who site)
      (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
        assessment.strategy mixed who site) := by
  ext history
  rw [setup.commitRecoveryModel.bayesBelief_apply]
  exact bayes who site
    (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
      assessment.strategy mixed who site) history

open Classical in
private theorem local_terminal_prescribed
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNoMissErasedProfile profile who
          (setup.commitRecoveryModel.infoOf who history.trace))
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (site : setup.commitRecoveryModel.InfoState focal)
    (law : PMF (setup.commitRecoveryModel.Choice focal site))
    (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
        assessment.strategy focal
        ((assessment.strategy focal).withLaw site law)) history =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
          (setup.commitRecoveryNoMissErasedProfile profile) focal
          ((setup.commitRecoveryNoMissErasedProfile profile focal).withLaw site law)) history := by
  apply setup.commitRecoveryModel.runBehavioralTerminalFrom_congr certificate history
  intro later _ running who
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same, Profile.update_same]
    by_cases here : setup.commitRecoveryModel.infoOf focal later.trace = site
    · subst site
      exact (InformationModel.BehavioralPolicy.withLaw_self _ _ _).trans
        (InformationModel.BehavioralPolicy.withLaw_self _ _ _).symm
    · rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here,
        InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ here]
      exact prescribed focal later running
  · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]
    exact prescribed who later running

open Classical in
/-- Corresponding current component interventions at ordinary erased copies
have equal conditional continuation values in the ACTUAL original assessment.
The assumptions are exactly its full mixing, Bayes and genuine-history
prescription facts; no desired value identity or rationality enters. -/
theorem commitRecovery_normalized_conditional_value_eq
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel assessment setup.commitRecoveryModel_decisionAntichain)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNoMissErasedProfile profile who
          (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1)
    (law : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal source.1)))) :
    let query := setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal source.1)
    let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      profile focal ((profile focal).withLaw query law)
    let changed := setup.commitRecoveryNoMissErasedProfile updated
    (assessment.continuationContext certificate source
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw source.1 (changed focal source.1)) =
      (assessment.continuationContext certificate target
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((assessment.strategy focal).withLaw target.1 (changed focal target.1)) := by
  classical
  dsimp only
  let query := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal source.1)
  let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
    profile focal ((profile focal).withLaw query law)
  let changed := setup.commitRecoveryNoMissErasedProfile updated
  let read := fun history : setup.commitRecoveryProtocol.History =>
    (setup.protocolReadout (setup.commitRecoverySourceState history.state),
      fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)
  have compareAt (site : setup.commitRecoveryModel.InformationSite focal)
      (current : PMF (setup.commitRecoveryModel.Choice focal site.1)) :
      ((assessment.belief focal site).bind fun history =>
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
            assessment.strategy focal
            ((assessment.strategy focal).withLaw site.1 current)) history.1).map read =
        ((setup.commitRecoveryModel.bayesBelief assessment.strategy focal site
          (setup.commitRecoveryModel_decisionAntichain focal site)
          (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
            assessment.strategy mixed focal site)).bind fun history =>
          setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
            (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
              (setup.commitRecoveryNoMissErasedProfile profile) focal
              ((setup.commitRecoveryNoMissErasedProfile profile focal).withLaw
                site.1 current)) history.1).map read := by
    rw [setup.actual_bayes assessment mixed bayes focal site]
    apply congrArg (PMF.map read)
    apply congrArg (PMF.bind _)
    funext history
    exact setup.local_terminal_prescribed assessment profile prescribed certificate
      focal site.1 current history.1
  have shared := setup.commitRecoveryNoMissErasedProfile_bayes_local_terminal_joint_eq
    assessment.strategy mixed profile utility excludedPayoff certificate focal
      target source same law
  dsimp only at shared
  have observed := (compareAt source (changed focal source.1)).trans
    (shared.trans (compareAt target (changed focal target.1)).symm)
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  exact expect_observed_law_eq _ _ read read (fun result => result.2 focal) observed


open Classical in
/-- The actual assessed baseline value is the same at ordinary erased copies,
using its original Bayes beliefs and actual prescribed future strategy. -/
theorem commitRecovery_normalized_baseline_value_eq
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel assessment setup.commitRecoveryModel_decisionAntichain)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNoMissErasedProfile profile who
          (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    (assessment.continuationContext certificate source
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        (assessment.strategy focal) =
      (assessment.continuationContext certificate target
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (assessment.strategy focal) := by
  classical
  let read := fun history : setup.commitRecoveryProtocol.History =>
    (setup.protocolReadout (setup.commitRecoverySourceState history.state),
      fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)
  have compareAt (site : setup.commitRecoveryModel.InformationSite focal) :
      ((assessment.belief focal site).bind fun history =>
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          assessment.strategy history.1).map read =
        ((setup.commitRecoveryModel.bayesBelief assessment.strategy focal site
          (setup.commitRecoveryModel_decisionAntichain focal site)
          (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
            assessment.strategy mixed focal site)).bind fun history =>
          setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
            (setup.commitRecoveryNoMissErasedProfile profile) history.1).map read := by
    rw [setup.actual_bayes assessment mixed bayes focal site]
    apply congrArg (PMF.map read)
    apply congrArg (PMF.bind _)
    funext history
    apply setup.commitRecoveryModel.runBehavioralTerminalFrom_congr certificate history.1
    intro later _ running who
    exact prescribed who later running
  have shared := setup.commitRecoveryNoMissErasedProfile_bayes_terminal_joint_eq
    assessment.strategy mixed profile utility excludedPayoff certificate focal target source same
  have observed := (compareAt source).trans (shared.trans (compareAt target).symm)
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value,
    Profile.update_eq_self]
  exact expect_observed_law_eq _ _ read read (fun result => result.2 focal) observed

open Classical in
/-- Exact conditional gains in the original fully mixed Bayes assessment agree
at ordinary erased copies. This is the local-gain expression appearing in the
actual source pooled-completion inequality. -/
theorem commitRecovery_normalized_conditional_gain_eq
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel assessment setup.commitRecoveryModel_decisionAntichain)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNoMissErasedProfile profile who
          (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1)
    (law : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal source.1)))) :
    let query := setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal source.1)
    let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      profile focal ((profile focal).withLaw query law)
    let changed := setup.commitRecoveryNoMissErasedProfile updated
    (assessment.continuationContext certificate source
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((assessment.strategy focal).withLaw source.1 (changed focal source.1)) -
      (assessment.continuationContext certificate source
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (assessment.strategy focal) =
      (assessment.continuationContext certificate target
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((assessment.strategy focal).withLaw target.1 (changed focal target.1)) -
        (assessment.continuationContext certificate target
          (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
            (assessment.strategy focal) := by
  exact congrArg₂ (fun alternative baseline : ℝ => alternative - baseline)
    (setup.commitRecovery_normalized_conditional_value_eq assessment mixed bayes profile
      prescribed utility excludedPayoff certificate focal target source same law)
    (setup.commitRecovery_normalized_baseline_value_eq assessment mixed bayes profile
      prescribed utility excludedPayoff certificate focal target source same)

end Vegas.SourceProgram.Setup
