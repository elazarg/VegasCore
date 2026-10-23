/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryReach
import Vegas.Game.ProposalRecoveryWordReadback
import Vegas.Game.CommitRecoveryReference
import Vegas.Game.CommitRecoverySpliceErasure

/-! # Actual full-information fiber exchange for proposal-labeled recovery -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private def proposalBackground (focal : Player)
    (original exchanged : setup.proposalRecoveryProtocol.History) : Prop :=
  (∃ (first : CommitRecoveryState setup.program)
      (prior : setup.commitRecoveryProtocol.Trace (some first)),
    prior.length = 1 ∧ TracePrefix prior (setup.proposalRecoveryEraseTrace original.trace) ∧
      TracePrefix prior (setup.proposalRecoveryEraseTrace exchanged.trace)) ∧
  (∀ who, setup.proposalRecoveryPublicRecall who exchanged.trace =
    setup.proposalRecoveryPublicRecall who original.trace) ∧
  ∀ who, who ≠ focal →
    (setup.proposalRecoveryJointRecall exchanged.trace).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall original.trace).map (fun joint => joint who)

private theorem proposalBackground_trans (focal : Player)
    {first middle last : setup.proposalRecoveryProtocol.History}
    (left : setup.proposalBackground focal first middle)
    (right : setup.proposalBackground focal middle last) :
    setup.proposalBackground focal first last := by
  obtain ⟨⟨initial, prior, length, firstKept, middleKept⟩, leftPublic, leftCoordinates⟩ := left
  obtain ⟨⟨otherInitial, otherPrior, otherLength, otherMiddle, lastKept⟩,
    rightPublic, rightCoordinates⟩ := right
  have same := middleKept.eq_of_same_length otherMiddle (length.trans otherLength.symm)
  cases same
  exact ⟨⟨initial, prior, length, firstKept, lastKept⟩,
    fun who => (rightPublic who).trans (leftPublic who),
    fun who foreign => (rightCoordinates who foreign).trans (leftCoordinates who foreign)⟩

private theorem proposalBackground_info_unique (focal : Player)
    {first second : setup.proposalRecoveryProtocol.History}
    (same : setup.proposalBackground focal first second)
    (information : setup.proposalRecoveryModel.infoOf focal first.trace =
      setup.proposalRecoveryModel.infoOf focal second.trace) : first = second := by
  obtain ⟨⟨initial, prior, _length, firstKept, secondKept⟩, publicWord, foreignCoordinates⟩ := same
  have coordinates who :
      (setup.proposalRecoveryJointRecall first.trace).map (fun joint => joint who) =
        (setup.proposalRecoveryJointRecall second.trace).map (fun joint => joint who) := by
    by_cases own : who = focal
    · subst who
      exact setup.proposalRecovery_coordinate_eq_of_info_eq focal
        first.trace second.trace information
    · exact (foreignCoordinates who own).symm
  have lengths := congrArg List.length (coordinates focal)
  simp only [List.length_map] at lengths
  have joints : setup.proposalRecoveryJointRecall first.trace =
      setup.proposalRecoveryJointRecall second.trace := by
    apply List.ext_getElem lengths
    intro index firstInside secondInside
    funext who
    have selected := congrArg (fun word => word[index]?) (coordinates who)
    simpa only [List.getElem?_map, List.getElem?_eq_getElem firstInside,
      List.getElem?_eq_getElem secondInside, Option.map_some, Option.some.injEq] using selected
  have semanticJoints : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace first.trace) =
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace second.trace) := by
    rw [← setup.proposalRecoveryJointRecall_semantic,
      ← setup.proposalRecoveryJointRecall_semantic, joints]
  have semanticPublic := setup.proposalRecoveryPublicRecall_semantic_eq focal
    second.trace first.trace (publicWord focal)
  have semantic := setup.commitRecovery_history_eq_of_public_and_joints focal initial prior
    (setup.proposalRecoveryEraseTrace first.trace) (setup.proposalRecoveryEraseTrace second.trace)
    firstKept secondKept semanticPublic.symm semanticJoints
  exact setup.proposalRecoveryHistory_eq_of_semantic_word first second semantic joints

private theorem proposal_site_state_some (focal : Player)
    (site : setup.proposalRecoveryModel.InformationSite focal)
    (history : setup.proposalRecoveryModel.InformationHistory focal site.1) :
    ∃ current : CommitRecoveryState setup.program, history.1.state = some current := by
  have active := InformationModel.InformationSite.active setup.proposalRecoveryModel site history
  cases state : history.1.state with
  | none => rw [state] at active; exact False.elim active
  | some current => exact ⟨current, rfl⟩

private theorem proposal_exchange_exists [Fintype Player]
    (finite : setup.program.FiniteBindingTypes)
    (strategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who) (focal : Player)
    (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1)
    (representative : setup.proposalRecoveryModel.InformationHistory focal target.1)
    (original : setup.proposalRecoveryModel.InformationHistory focal source.1) :
    ∃ exchanged : setup.proposalRecoveryModel.InformationHistory focal target.1,
      setup.proposalBackground focal original.1 exchanged.1 ∧
      (∀ who, who ≠ focal → setup.proposalRecoveryModel.infoOf who exchanged.1.trace =
        setup.proposalRecoveryModel.infoOf who original.1.trace) ∧
      setup.proposalRecoveryModel.counterfactualReachProbability strategy focal exchanged.1.trace =
        setup.proposalRecoveryModel.counterfactualReachProbability strategy focal
          original.1.trace ∧
      setup.proposalRecoveryErasedHistory exchanged.1 =
        setup.proposalRecoveryErasedHistory original.1 := by
  have mineActive := InformationModel.InformationSite.active
    setup.proposalRecoveryModel target representative
  have othersActive := InformationModel.InformationSite.active
    setup.proposalRecoveryModel source original
  obtain ⟨mine, mineState⟩ := setup.proposal_site_state_some focal target representative
  obtain ⟨others, othersState⟩ := setup.proposal_site_state_some focal source original
  rcases representative with ⟨⟨mineOption, mineTrace⟩, mineInfo⟩
  rcases original with ⟨⟨othersOption, othersTrace⟩, othersInfo⟩
  cases mineState
  cases othersState
  have mineSurvives : focal ∉ mine.excluded := by
    change setup.commitRecoveryProtocol.active (some mine) focal at mineActive
    exact mineActive.2
  have othersSurvives : focal ∉ others.excluded := by
    change setup.commitRecoveryProtocol.active (some others) focal at othersActive
    exact othersActive.2
  let reference := (setup.commitRecoveryReference finite).strategy
  have oldSame : setup.commitRecoveryErasedInformation focal
      (setup.commitRecoveryModel.infoOf focal (setup.proposalRecoveryEraseTrace mineTrace)) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryModel.infoOf focal
          (setup.proposalRecoveryEraseTrace othersTrace)) := by
    rw [← setup.proposalRecoveryEraseInfo_observed,
      ← setup.proposalRecoveryEraseInfo_observed, mineInfo, othersInfo]
    exact semantic
  obtain ⟨hybrid, shape, ⟨initial, prior, length, hybridKept, originalKept⟩,
    publicWord, coordinates, focalInfo, foreignInfo, chance⟩ :=
    setup.proposalRecovery_hybrid_of_erased_information_archive reference focal mine others
      mineTrace othersTrace oldSame (by rw [mineInfo, othersInfo]; exact archive)
  have density := setup.proposalRecovery_counterfactual_reach_eq_of_reference strategy reference
    (fun who site choice => setup.commitRecoveryReference_fullSupport finite who site.1 choice)
    focal hybrid.trace othersTrace foreignInfo chance
  have erasedState := setup.commitRecovery_splice_erased_state_eq focal mine others
    (setup.proposalRecoveryEraseTrace mineTrace) (setup.proposalRecoveryEraseTrace othersTrace)
    mineSurvives othersSurvives oldSame
  have erased : setup.proposalRecoveryErasedHistory hybrid =
      setup.proposalRecoveryErasedHistory ⟨some others, othersTrace⟩ := by
    apply Prod.ext
    · apply Prod.ext
      · change hybrid.state.map CommitRecoveryState.eraseHistory = some others.eraseHistory
        rw [shape]
        exact congrArg some erasedState
      · funext who
        change setup.commitRecoveryErasedInformation who
            (setup.commitRecoveryModel.infoOf who
              (setup.proposalRecoveryEraseTrace hybrid.trace)) =
          setup.commitRecoveryErasedInformation who
            (setup.commitRecoveryModel.infoOf who
              (setup.proposalRecoveryEraseTrace othersTrace))
        rw [← setup.proposalRecoveryEraseInfo_observed,
          ← setup.proposalRecoveryEraseInfo_observed]
        by_cases own : who = focal
        · subst who
          rw [focalInfo, setup.proposalRecoveryEraseInfo_observed,
            setup.proposalRecoveryEraseInfo_observed]
          exact oldSame
        · rw [foreignInfo who own]
    · have words := congrArg (List.map Prod.snd) (publicWord focal)
      rw [setup.proposalRecoveryPublicRecall_deltas,
        setup.proposalRecoveryPublicRecall_deltas] at words
      exact List.append_cancel_right words
  exact ⟨⟨hybrid, focalInfo.trans mineInfo⟩,
    ⟨⟨initial, prior, length, originalKept, hybridKept⟩, publicWord,
      fun who foreign => by simpa only [foreign, ite_false] using coordinates who⟩,
    foreignInfo, density, erased⟩

/-- A bijection of actual full enriched information fibers preserves every
opponent's complete information and the original counterfactual reach. Its
inverse restores the entire original labeled history. No Bayes law is assumed. -/
theorem proposalRecovery_information_fiber_equiv [Fintype Player]
    (finite : setup.program.FiniteBindingTypes)
    (strategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who) (focal : Player)
    (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1) :
    ∃ exchange : setup.proposalRecoveryModel.InformationHistory focal source.1 ≃
        setup.proposalRecoveryModel.InformationHistory focal target.1,
      ∀ original,
        (∀ who, setup.proposalRecoveryPublicRecall who (exchange original).1.trace =
          setup.proposalRecoveryPublicRecall who original.1.trace) ∧
        (∀ who, who ≠ focal → setup.proposalRecoveryModel.infoOf who
          (exchange original).1.trace = setup.proposalRecoveryModel.infoOf who original.1.trace) ∧
        setup.proposalRecoveryModel.counterfactualReachProbability strategy focal
          (exchange original).1.trace =
            setup.proposalRecoveryModel.counterfactualReachProbability strategy focal
              original.1.trace ∧
        setup.proposalRecoveryErasedHistory (exchange original).1 =
          setup.proposalRecoveryErasedHistory original.1 := by
  classical
  obtain ⟨targetRepresentative, _, _⟩ := target.2
  obtain ⟨sourceRepresentative, _, _⟩ := source.2
  let forward := fun original => Classical.choose
    (setup.proposal_exchange_exists finite strategy focal target source semantic archive
      targetRepresentative original)
  let backward := fun original => Classical.choose
    (setup.proposal_exchange_exists finite strategy focal source target semantic.symm archive.symm
      sourceRepresentative original)
  have forwardSpec original := Classical.choose_spec
    (setup.proposal_exchange_exists finite strategy focal target source semantic archive
      targetRepresentative original)
  have backwardSpec original := Classical.choose_spec
    (setup.proposal_exchange_exists finite strategy focal source target semantic.symm archive.symm
      sourceRepresentative original)
  refine ⟨⟨forward, backward, ?_, ?_⟩, ?_⟩
  · intro original
    apply Subtype.ext
    exact (setup.proposalBackground_info_unique focal
      (setup.proposalBackground_trans focal (forwardSpec original).1
        (backwardSpec (forward original)).1)
      (original.2.trans (backward (forward original)).2.symm)).symm
  · intro original
    apply Subtype.ext
    exact (setup.proposalBackground_info_unique focal
      (setup.proposalBackground_trans focal (backwardSpec original).1
        (forwardSpec (backward original)).1)
      (original.2.trans (forward (backward original)).2.symm)).symm
  · intro original
    exact ⟨(forwardSpec original).1.2.1, (forwardSpec original).2⟩

end Vegas.SourceProgram.Setup
