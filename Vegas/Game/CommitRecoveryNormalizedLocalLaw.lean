/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryAncillaryContinuation

/-! # A shared source-coordinate change is the actual local intervention

The normalized source query preserves the original logical clock. Changing
one such coordinate therefore affects only the present action when play
starts there; every later source query reads the unchanged prescription.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem original_clock (who : Player) (history : setup.commitRecoveryProtocol.History) :
    (setup.commitRecoveryModel.infoOf who history.trace).1.2.length = history.trace.length := by
  have clock := setup.commitRecoveryErasedModel_word_length who history.trace
  rw [setup.commitRecoveryErasedModel_infoOf] at clock
  simpa only [commitRecoveryErasedInformation, List.length_map] using clock

open Classical in
/-- Changing the constructed prescription at its CURRENT normalized query
is precisely an ordinary one-site law intervention on the ORIGINAL source
terminal runner. Logical-clock nonrecurrence is derived from actual source
histories; no unread-coordinate or future-policy equality is assumed. -/
theorem commitRecoveryNoMissErasedProfile_terminal_local_law
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (history : setup.commitRecoveryProtocol.History)
    (query : setup.commitRecoveryModel.InfoState focal)
    (atQuery : setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal
        (setup.commitRecoveryModel.infoOf focal history.trace)) = query)
    (law : PMF (setup.commitRecoveryModel.Choice focal query)) :
    let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      profile focal ((profile focal).withLaw query law)
    let baseline := setup.commitRecoveryNoMissErasedProfile profile
    let changed := setup.commitRecoveryNoMissErasedProfile updated
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed history =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal history.trace)
            (changed focal (setup.commitRecoveryModel.infoOf focal history.trace)))) history := by
  classical
  dsimp only
  let key := fun info : setup.commitRecoveryModel.InfoState focal =>
    setup.commitRecoveryErasedInformation focal (setup.commitRecoveryNoMissInformation focal info)
  let current := setup.commitRecoveryModel.infoOf focal history.trace
  let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
    profile focal ((profile focal).withLaw query law)
  let baseline := setup.commitRecoveryNoMissErasedProfile profile
  let changed := setup.commitRecoveryNoMissErasedProfile updated
  change setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed history =
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw current (changed focal current))) history
  apply setup.commitRecoveryModel.runBehavioralTerminalFrom_congr certificate history
  intro later reached _ who
  obtain ⟨fuel, path⟩ := reached
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same]
    by_cases sameLength : history.trace.length = later.trace.length
    · have equal := path.eq_of_trace_length_eq sameLength
      subst later
      exact (InformationModel.BehavioralPolicy.withLaw_self _ _ _).symm
    · have keyDifferent : key (setup.commitRecoveryModel.infoOf focal later.trace) ≠ query := by
        intro equal
        have lengths := congrArg (fun info => info.1.2.length) (equal.trans atQuery.symm)
        simp only [key, setup.commitRecoveryNoMissInformation_erased_word_length,
          setup.original_clock] at lengths
        exact sameLength lengths.symm
      have different : setup.commitRecoveryModel.infoOf focal later.trace ≠ current :=
        fun equal => keyDifferent ((congrArg key equal).trans atQuery)
      rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ different]
      apply pmf_map_injective Subtype.val_injective
      rw [setup.commitRecoveryNoMissErasedProfile_raw,
        setup.commitRecoveryNoMissErasedProfile_raw]
      change ((updated focal (key (setup.commitRecoveryModel.infoOf focal later.trace))).map
        Subtype.val) = _
      dsimp only [updated]
      rw [Profile.update_same,
        InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ keyDifferent]
  · rw [Profile.update_of_ne _ _ own]
    apply pmf_map_injective Subtype.val_injective
    rw [setup.commitRecoveryNoMissErasedProfile_raw,
      setup.commitRecoveryNoMissErasedProfile_raw]
    simp only [updated, Profile.update_of_ne _ _ own]

open Classical in
/-- Ordinary source copies have the same full terminal outcome law under
corresponding ACTUAL local law deviations. The shared-coordinate intervention
is converted to each original site's `withLaw` continuation, so this is a
conditional-incentive statement on the original game, not on an auxiliary runner. -/
theorem commitRecoveryNoMissErasedProfile_bayes_local_terminal_joint_eq
    (beliefProfile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.commitRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
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
    let baseline := setup.commitRecoveryNoMissErasedProfile profile
    let changed := setup.commitRecoveryNoMissErasedProfile updated
    ((setup.commitRecoveryModel.bayesBelief beliefProfile focal source
        (setup.commitRecoveryModel_decisionAntichain focal source)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw source.1 (changed focal source.1))) history.1).map
          (fun history =>
            (setup.protocolReadout (setup.commitRecoverySourceState history.state),
              fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) =
      ((setup.commitRecoveryModel.bayesBelief beliefProfile focal target
        (setup.commitRecoveryModel_decisionAntichain focal target)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw target.1 (changed focal target.1))) history.1).map
          (fun history =>
            (setup.protocolReadout (setup.commitRecoverySourceState history.state),
              fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  classical
  dsimp only
  let query := setup.commitRecoveryErasedInformation focal
    (setup.commitRecoveryNoMissInformation focal source.1)
  let updated := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
    profile focal ((profile focal).withLaw query law)
  let baseline := setup.commitRecoveryNoMissErasedProfile profile
  let changed := setup.commitRecoveryNoMissErasedProfile updated
  have targetQuery : setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryNoMissInformation focal target.1) = query := by
    dsimp only [query]
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, same]
  have sourceRun (history : setup.commitRecoveryModel.InformationHistory focal source.1) :
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed history.1 =
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
            ((baseline focal).withLaw source.1 (changed focal source.1))) history.1 := by
    have localLaw := setup.commitRecoveryNoMissErasedProfile_terminal_local_law profile
      certificate focal history.1 query (by rw [history.2]) law
    change setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed history.1 =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal history.1.trace)
            (changed focal (setup.commitRecoveryModel.infoOf focal history.1.trace)))) history.1
      at localLaw
    rw [history.2] at localLaw
    exact localLaw
  have targetRun (history : setup.commitRecoveryModel.InformationHistory focal target.1) :
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed history.1 =
        setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
            ((baseline focal).withLaw target.1 (changed focal target.1))) history.1 := by
    have localLaw := setup.commitRecoveryNoMissErasedProfile_terminal_local_law profile
      certificate focal history.1 query (by rw [history.2]; exact targetQuery) law
    change setup.commitRecoveryModel.runBehavioralTerminalFrom certificate changed history.1 =
      setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw (setup.commitRecoveryModel.infoOf focal history.1.trace)
            (changed focal (setup.commitRecoveryModel.infoOf focal history.1.trace)))) history.1
      at localLaw
    rw [history.2] at localLaw
    exact localLaw
  have shared := setup.commitRecoveryNoMissErasedProfile_bayes_terminal_joint_eq beliefProfile
    mixed updated utility excludedPayoff certificate focal target source same
  convert shared using 1
  · apply congrArg (PMF.map _)
    apply congrArg (PMF.bind _)
    funext history
    exact (sourceRun history).symm
  · apply congrArg (PMF.map _)
    apply congrArg (PMF.bind _)
    funext history
    exact (targetRun history).symm

end Vegas.SourceProgram.Setup
