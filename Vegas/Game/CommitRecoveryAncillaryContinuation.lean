/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryAncillaryBayes
import Vegas.Game.CommitRecoveryNoMissContinuation

/-! # Original source continuation laws after ancillary Bayes cancellation

The actual information-fiber exchange preserves both semantic checkpoints
and every erased query. Existing original stopped and terminal runners
therefore give the same laws under the selected source prescription.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Actual Bayes beliefs at erased-equivalent source sites give the same
stopped erased-history law under any selected no-new-miss/erased prescription.
The source runner, all original chance laws and actual reset branches remain. -/
theorem commitRecoveryNoMissErasedProfile_bayes_stopped_eq
    (beliefProfile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.commitRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (stopped : (setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who)) → Prop)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    ((setup.commitRecoveryModel.bayesBelief beliefProfile focal source
        (setup.commitRecoveryModel_decisionAntichain focal source)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralUntil certificate
        (setup.commitRecoveryNoMissErasedProfile profile)
        (stopped ∘ setup.commitRecoveryErasedHistory) history.1).map
          setup.commitRecoveryErasedHistory =
      ((setup.commitRecoveryModel.bayesBelief beliefProfile focal target
        (setup.commitRecoveryModel_decisionAntichain focal target)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralUntil certificate
        (setup.commitRecoveryNoMissErasedProfile profile)
        (stopped ∘ setup.commitRecoveryErasedHistory) history.1).map
          setup.commitRecoveryErasedHistory := by
  obtain ⟨exchange, exchangeSpec, bayes⟩ :=
    setup.commitRecovery_bayes_eq_of_erasedInformation_eq beliefProfile mixed focal
      target source same
  rw [PMF.map_bind, PMF.map_bind]
  have rewritten := congrArg (fun law => law.bind fun history :
      setup.commitRecoveryModel.InformationHistory focal target.1 =>
        (setup.commitRecoveryModel.runBehavioralUntil certificate
          (setup.commitRecoveryNoMissErasedProfile profile)
          (stopped ∘ setup.commitRecoveryErasedHistory) history.1).map
            setup.commitRecoveryErasedHistory) bayes
  rw [PMF.bind_map] at rewritten
  rw [← rewritten]
  apply congrArg (PMF.bind _)
  funext history
  exact setup.commitRecovery_runUntil_erased_eq
    (setup.commitRecoveryNoMissErasedProfile profile)
    (setup.commitRecoveryErasedProfile_congr (setup.commitRecoveryNoMissProfile profile))
    certificate stopped history.1 (exchange history).1 (exchangeSpec history).2.2.symm

/-- The SAME actual belief exchange gives the complete terminal typed readout
and all-player payoff law. No source belief, reset-payoff or terminal-law
identity is an input. Future play is the actual constructed erased prescription. -/
theorem commitRecoveryNoMissErasedProfile_bayes_terminal_joint_eq
    (beliefProfile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.commitRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    ((setup.commitRecoveryModel.bayesBelief beliefProfile focal source
        (setup.commitRecoveryModel_decisionAntichain focal source)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) history.1).map
          (fun history =>
            (setup.protocolReadout (setup.commitRecoverySourceState history.state),
              fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) =
      ((setup.commitRecoveryModel.bayesBelief beliefProfile focal target
        (setup.commitRecoveryModel_decisionAntichain focal target)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) history.1).map
          (fun history =>
            (setup.protocolReadout (setup.commitRecoverySourceState history.state),
              fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  obtain ⟨exchange, exchangeSpec, bayes⟩ :=
    setup.commitRecovery_bayes_eq_of_erasedInformation_eq beliefProfile mixed focal
      target source same
  rw [PMF.map_bind, PMF.map_bind]
  have rewritten := congrArg (fun law => law.bind fun history :
      setup.commitRecoveryModel.InformationHistory focal target.1 =>
        (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          (setup.commitRecoveryNoMissErasedProfile profile) history.1).map
            (fun history =>
              (setup.protocolReadout (setup.commitRecoverySourceState history.state),
                fun who => setup.commitRecoveryPayoff utility excludedPayoff who history))) bayes
  rw [PMF.bind_map] at rewritten
  rw [← rewritten]
  apply congrArg (PMF.bind _)
  funext history
  exact setup.commitRecoveryErasedProfile_terminal_joint_eq
    (setup.commitRecoveryNoMissProfile profile) utility excludedPayoff certificate history.1
    (exchange history).1 (exchangeSpec history).2.2.symm

/-- Keep an observable Boolean at the actual stopped attempt boundary and
then run the SAME original source terminal continuation. This preserves its
JOINT law with every terminal readout/payoff, rather than only unconditional
payoff. The identification of a particular raw-flag event with `marked` is
separate from this source-law statement. -/
theorem commitRecoveryNoMissErasedProfile_bayes_stopped_terminal_joint_eq
    (beliefProfile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.commitRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (stopped : (setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who)) → Prop)
    (marked : (setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who)) → Bool)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    ((setup.commitRecoveryModel.bayesBelief beliefProfile focal source
        (setup.commitRecoveryModel_decisionAntichain focal source)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralUntil certificate
        (setup.commitRecoveryNoMissErasedProfile profile)
        (stopped ∘ setup.commitRecoveryErasedHistory) history.1).bind (fun boundary =>
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) boundary).map (fun history =>
          (marked (setup.commitRecoveryErasedHistory boundary),
            (setup.protocolReadout (setup.commitRecoverySourceState history.state),
              fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)))) =
      ((setup.commitRecoveryModel.bayesBelief beliefProfile focal target
        (setup.commitRecoveryModel_decisionAntichain focal target)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralUntil certificate
        (setup.commitRecoveryNoMissErasedProfile profile)
        (stopped ∘ setup.commitRecoveryErasedHistory) history.1).bind (fun boundary =>
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) boundary).map (fun history =>
          (marked (setup.commitRecoveryErasedHistory boundary),
            (setup.protocolReadout (setup.commitRecoverySourceState history.state),
              fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)))) := by
  apply bind_eq_of_map_eq _ _ setup.commitRecoveryErasedHistory setup.commitRecoveryErasedHistory
    (setup.commitRecoveryNoMissErasedProfile_bayes_stopped_eq beliefProfile mixed profile
      certificate stopped focal target source same)
  intro first _ second _ sameBoundary
  have terminal := setup.commitRecoveryErasedProfile_terminal_joint_eq
    (setup.commitRecoveryNoMissProfile profile) utility excludedPayoff certificate
      first second sameBoundary
  have projected := congrArg (PMF.map (fun result =>
    (marked (setup.commitRecoveryErasedHistory first), result))) terminal
  simpa only [PMF.map_comp, Function.comp_def, sameBoundary,
    commitRecoveryNoMissErasedProfile] using projected

end Vegas.SourceProgram.Setup
