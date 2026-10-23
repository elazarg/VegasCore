/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPrescription
import Vegas.Game.ProposalRecoveryBayesContinuation
import Vegas.Source.ProposalRecoveryQueryAntichain

/-! # Common component interventions are actual local source deviations -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- Logical depth prevents the current common coordinate from recurring.
Consequently a component change gives the actual one-site law intervention,
including all future source failure, exclusion and retry branches. -/
theorem proposalRecoveryPrescribedProfile_terminal_local_law
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (history : setup.proposalRecoveryProtocol.History)
    (query : setup.ProposalRecoveryComponent focal)
    (atQuery : setup.proposalRecoveryQuery focal
      (setup.proposalRecoveryModel.infoOf focal history.trace) = query)
    (law : PMF (setup.ProposalRecoveryComponentChoice focal query)) :
    let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
      prescription focal
        (setup.proposalRecoveryPrescriptionWithLaw focal (prescription focal) query law)
    let baseline := setup.proposalRecoveryPrescribedProfile prescription
    let changed := setup.proposalRecoveryPrescribedProfile updated
    setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate changed history =
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw (setup.proposalRecoveryModel.infoOf focal history.trace)
            (changed focal (setup.proposalRecoveryModel.infoOf focal history.trace)))) history := by
  classical
  dsimp only
  let current := setup.proposalRecoveryModel.infoOf focal history.trace
  let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
    prescription focal
      (setup.proposalRecoveryPrescriptionWithLaw focal (prescription focal) query law)
  let baseline := setup.proposalRecoveryPrescribedProfile prescription
  let changed := setup.proposalRecoveryPrescribedProfile updated
  change setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate changed history =
    setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw current (changed focal current))) history
  apply setup.proposalRecoveryModel.runBehavioralTerminalFrom_congr certificate history
  intro later reached _ who
  obtain ⟨fuel, path⟩ := reached
  by_cases own : who = focal
  · subst who
    rw [Profile.update_same]
    by_cases sameLength : history.trace.length = later.trace.length
    · have equal := path.eq_of_trace_length_eq sameLength
      subst later
      exact (InformationModel.BehavioralPolicy.withLaw_self _ _ _).symm
    · have keyDifferent : setup.proposalRecoveryQuery focal
          (setup.proposalRecoveryModel.infoOf focal later.trace) ≠ query := by
        intro equal
        have lengths := congrArg (fun key => key.1.1.2.length) (equal.trans atQuery.symm)
        rw [setup.proposalRecoveryQuery_trace_length,
          setup.proposalRecoveryQuery_trace_length] at lengths
        exact sameLength lengths.symm
      have different : setup.proposalRecoveryModel.infoOf focal later.trace ≠ current :=
        fun equal => keyDifferent
          ((congrArg (setup.proposalRecoveryQuery focal) equal).trans atQuery)
      rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ different]
      apply pmf_map_injective Subtype.val_injective
      rw [setup.proposalRecoveryPrescribedProfile_raw,
        setup.proposalRecoveryPrescribedProfile_raw]
      change ((updated focal
        (setup.proposalRecoveryQuery focal
          (setup.proposalRecoveryModel.infoOf focal later.trace))).map
          Subtype.val) = _
      dsimp only [updated]
      rw [Profile.update_same, setup.proposalRecoveryPrescriptionWithLaw_of_ne _ _ _ _ keyDifferent]
  · rw [Profile.update_of_ne _ _ own]
    apply pmf_map_injective Subtype.val_injective
    rw [setup.proposalRecoveryPrescribedProfile_raw,
      setup.proposalRecoveryPrescribedProfile_raw]
    simp only [updated, Profile.update_of_ne _ _ own]

open Classical in
/-- Corresponding component interventions preserve the actual Bayes-sampled
terminal image on the full original information fibers. -/
theorem proposalRecovery_bayes_local_terminal_eq
    (finite : setup.program.FiniteBindingTypes)
    (beliefProfile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.proposalRecoveryModel.InformationSite who) choice,
      choice ∈ (beliefProfile who site.1).support)
    (prescription : ∀ who, setup.ProposalRecoveryPrescription who)
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
    let baseline := setup.proposalRecoveryPrescribedProfile prescription
    let changed := setup.proposalRecoveryPrescribedProfile updated
    ((setup.proposalRecoveryModel.bayesBelief beliefProfile focal source
        (setup.proposalRecoveryModel_decisionAntichain focal source)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal source)).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw source.1 (changed focal source.1))) history.1).map
            setup.proposalRecoveryErasedHistory =
      ((setup.proposalRecoveryModel.bayesBelief beliefProfile focal target
        (setup.proposalRecoveryModel_decisionAntichain focal target)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          beliefProfile mixed focal target)).bind fun history =>
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw target.1 (changed focal target.1))) history.1).map
            setup.proposalRecoveryErasedHistory := by
  classical
  dsimp only
  let query := setup.proposalRecoveryQuery focal source.1
  let updated := Profile.update (sig := setup.proposalRecoveryPrescriptionSignature)
    prescription focal
      (setup.proposalRecoveryPrescriptionWithLaw focal (prescription focal) query law)
  let baseline := setup.proposalRecoveryPrescribedProfile prescription
  let changed := setup.proposalRecoveryPrescribedProfile updated
  have targetQuery : setup.proposalRecoveryQuery focal target.1 = query := by
    apply Prod.ext
    · dsimp only [query, proposalRecoveryQuery]
      rw [setup.commitRecoveryNoMissInformation_erased,
        setup.commitRecoveryNoMissInformation_erased, semantic]
    · exact archive
  have localRun (site : setup.proposalRecoveryModel.InformationSite focal)
      (atQuery : setup.proposalRecoveryQuery focal site.1 = query)
      (history : setup.proposalRecoveryModel.InformationHistory focal site.1) :
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate changed history.1 =
        setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
          (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
            ((baseline focal).withLaw site.1 (changed focal site.1))) history.1 := by
    have localLaw := setup.proposalRecoveryPrescribedProfile_terminal_local_law prescription
      certificate focal history.1 query (by rw [history.2]; exact atQuery) law
    change setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate changed history.1 =
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
          ((baseline focal).withLaw (setup.proposalRecoveryModel.infoOf focal history.1.trace)
            (changed focal (setup.proposalRecoveryModel.infoOf focal history.1.trace)))) history.1
      at localLaw
    rw [history.2] at localLaw
    exact localLaw
  have shared := setup.proposalRecovery_bayes_terminal_eq finite beliefProfile mixed changed
    (setup.proposalRecoveryPrescribedProfile_normalized updated) certificate focal target source
    semantic archive
  convert shared using 1
  · apply congrArg (PMF.map _)
    apply congrArg (PMF.bind _)
    funext history
    exact (localRun source rfl history).symm
  · apply congrArg (PMF.map _)
    apply congrArg (PMF.bind _)
    funext history
    exact (localRun target targetQuery history).symm

end Vegas.SourceProgram.Setup
