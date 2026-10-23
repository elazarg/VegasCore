/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryHybridWordDisclosure
import Vegas.Game.ProposalRecoveryArchivePublicHistory
import Vegas.Source.ProposalRecoveryArchiveChronology
import Vegas.Source.ProposalRecoveryArchiveLookup
import Vegas.Source.ProposalRecoveryWordSplice

/-! # Full enriched information under the genuine semantic history exchange -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecovery_information_of_split_coordinates (focal : Player)
    {mineState othersState hybridState : setup.proposalRecoveryProtocol.State}
    (mine : setup.proposalRecoveryProtocol.Trace mineState)
    (others : setup.proposalRecoveryProtocol.Trace othersState)
    (hybrid : setup.proposalRecoveryProtocol.Trace hybridState)
    (publicMine : ∀ who,
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace mine) =
        setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace others))
    (publicHybrid : ∀ who,
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace hybrid) =
        setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace others))
    (information : ∀ who,
      setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace hybrid) =
        if who = focal then
          setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace mine)
        else setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace others))
    (coordinates : ∀ who,
      (setup.proposalRecoveryJointRecall hybrid).map (fun joint => joint who) =
        if who = focal then (setup.proposalRecoveryJointRecall mine).map (fun joint => joint who)
        else (setup.proposalRecoveryJointRecall others).map (fun joint => joint who))
    (archive : setup.proposalRecoveryArchive focal
        (setup.proposalRecoveryModel.infoOf focal mine) =
      setup.proposalRecoveryArchive focal (setup.proposalRecoveryModel.infoOf focal others)) :
    ∀ who, setup.proposalRecoveryModel.infoOf who hybrid =
      if who = focal then setup.proposalRecoveryModel.infoOf who mine
      else setup.proposalRecoveryModel.infoOf who others := by
  have cursor := setup.proposalRecoveryCursorWord_eq_of_semantic_public focal mine others
    (publicMine focal)
  have originalDeltas := setup.proposalRecoveryDeltaRecall_eq_of_archive_cursor_word focal
    mine others cursor archive
  have hybridDeltas := setup.proposalRecoveryDeltaRecall_eq_of_split_information focal
    mine others hybrid (publicMine focal) (publicHybrid focal) information coordinates
    originalDeltas
  have archiveFromDelta {leftState rightState : setup.proposalRecoveryProtocol.State}
      (left : setup.proposalRecoveryProtocol.Trace leftState)
      (right : setup.proposalRecoveryProtocol.Trace rightState)
      (same : setup.proposalRecoveryDeltaRecall left = setup.proposalRecoveryDeltaRecall right)
      (who : Player) :
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who left) =
        setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right) := by
    unfold proposalRecoveryArchive
    rw [setup.proposalRecoveryProposalWord_eq_deltas,
      setup.proposalRecoveryProposalWord_eq_deltas, same]
  intro who
  have hybridPublic := setup.proposalRecoveryPublicRecall_eq_of_semantic_archive who hybrid others
    (publicHybrid who) (archiveFromDelta hybrid others hybridDeltas who)
  by_cases own : who = focal
  · subst who
    simp only [ite_true]
    apply setup.proposalRecovery_info_eq_of_semantic_public_coordinate focal hybrid mine
    · simpa only [ite_true] using information focal
    · have originalPublic := setup.proposalRecoveryPublicRecall_eq_of_semantic_archive focal
        mine others (publicMine focal) archive
      exact hybridPublic.trans originalPublic.symm
    · simpa only [ite_true] using coordinates focal
  · simp only [own, ite_false]
    exact setup.proposalRecovery_info_eq_of_semantic_public_coordinate who hybrid others
      (by simpa only [own, ite_false] using information who) hybridPublic
      (by simpa only [own, ite_false] using coordinates who)

/-- The old semantic exchange supplies the actual setup draw and Nature path;
only valid labels are attached. Every foreign full enriched information value
is retained, rather than inferred from a forgetful observation projection. -/
theorem proposalRecovery_hybrid_of_erased_information_archive [Fintype Player]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (focal : Player)
    (mine others : CommitRecoveryState setup.program)
    (mineTrace : setup.proposalRecoveryProtocol.Trace (some mine))
    (othersTrace : setup.proposalRecoveryProtocol.Trace (some others))
    (same : setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryModel.infoOf focal (setup.proposalRecoveryEraseTrace mineTrace)) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryModel.infoOf focal (setup.proposalRecoveryEraseTrace othersTrace)))
    (archive : setup.proposalRecoveryArchive focal
        (setup.proposalRecoveryModel.infoOf focal mineTrace) =
      setup.proposalRecoveryArchive focal (setup.proposalRecoveryModel.infoOf focal othersTrace)) :
    ∃ hybrid : setup.proposalRecoveryProtocol.History,
      hybrid.state = some (CommitRecoveryState.splice focal mine others) ∧
      (∃ (first : CommitRecoveryState setup.program)
          (prior : setup.commitRecoveryProtocol.Trace (some first)),
        prior.length = 1 ∧
        TracePrefix prior (setup.proposalRecoveryEraseTrace hybrid.trace) ∧
        TracePrefix prior (setup.proposalRecoveryEraseTrace othersTrace)) ∧
      (∀ who, setup.proposalRecoveryPublicRecall who hybrid.trace =
        setup.proposalRecoveryPublicRecall who othersTrace) ∧
      (∀ who, (setup.proposalRecoveryJointRecall hybrid.trace).map (fun joint => joint who) =
        if who = focal then
          (setup.proposalRecoveryJointRecall mineTrace).map (fun joint => joint who)
        else (setup.proposalRecoveryJointRecall othersTrace).map (fun joint => joint who)) ∧
      setup.proposalRecoveryModel.infoOf focal hybrid.trace =
        setup.proposalRecoveryModel.infoOf focal mineTrace ∧
      (∀ who, who ≠ focal → setup.proposalRecoveryModel.infoOf who hybrid.trace =
        setup.proposalRecoveryModel.infoOf who othersTrace) ∧
      setup.commitRecoveryModel.counterfactualReachProbability strategy focal
          (setup.proposalRecoveryEraseTrace hybrid.trace) =
        setup.commitRecoveryModel.counterfactualReachProbability strategy focal
          (setup.proposalRecoveryEraseTrace othersTrace) := by
  obtain ⟨_input, _prior, _length, _retained, semantic, satisfies, _unique⟩ :=
    setup.commitRecovery_hybrid_of_erasedInformation_eq strategy focal mine others
      (setup.proposalRecoveryEraseTrace mineTrace)
      (setup.proposalRecoveryEraseTrace othersTrace) same
  obtain ⟨shape, _kept, publicWord, semanticCoordinates, focalInfo, foreignInfo, density, _mass⟩ :=
    satisfies
  have minePublic focalObserver := setup.attemptPublicRecall_eq_for_observer focal focalObserver
    (setup.proposalRecoveryEraseTrace mineTrace) (setup.proposalRecoveryEraseTrace othersTrace)
    (setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq focal
      (setup.proposalRecoveryEraseTrace mineTrace)
      (setup.proposalRecoveryEraseTrace othersTrace) same)
  have clock : mineTrace.length = othersTrace.length := by
    have sizes := congrArg List.length (minePublic focal)
    simpa only [setup.publicRecall_length, setup.proposalRecoveryEraseTrace_length,
      Nat.add_left_inj] using sizes
  obtain ⟨lifted, erased, coordinates⟩ := setup.proposalRecovery_lift_spliced_word focal
    mineTrace othersTrace semantic.trace clock semanticCoordinates
  have information who :
      setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace lifted) =
        if who = focal then
          setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace mineTrace)
        else setup.commitRecoveryModel.infoOf who
          (setup.proposalRecoveryEraseTrace othersTrace) := by
    rw [erased]
    by_cases own : who = focal
    · subst who
      simpa only [ite_true] using focalInfo
    · simpa only [own, ite_false] using foreignInfo who own
  have publicLifted who :
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace lifted) =
        setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace othersTrace) := by
    rw [erased]
    exact publicWord who
  have full := setup.proposalRecovery_information_of_split_coordinates focal mineTrace othersTrace
    lifted minePublic publicLifted information coordinates archive
  have originalDeltas := setup.proposalRecoveryDeltaRecall_eq_of_archive_cursor_word focal
    mineTrace othersTrace
    (setup.proposalRecoveryCursorWord_eq_of_semantic_public focal mineTrace othersTrace
      (minePublic focal)) archive
  have liftedDeltas := setup.proposalRecoveryDeltaRecall_eq_of_split_information focal
    mineTrace othersTrace lifted (minePublic focal) (publicLifted focal)
    information coordinates originalDeltas
  refine ⟨⟨semantic.state, lifted⟩, shape, ?_, ?_, coordinates, ?_, ?_, ?_⟩
  · exact ⟨_, _prior, _length, by rw [erased]; exact _kept, _retained⟩
  · intro who
    apply setup.proposalRecoveryPublicRecall_eq_of_semantic_archive who lifted othersTrace
      (publicLifted who)
    unfold proposalRecoveryArchive
    rw [setup.proposalRecoveryProposalWord_eq_deltas,
      setup.proposalRecoveryProposalWord_eq_deltas, liftedDeltas]
  · simpa only [ite_true] using full focal
  · intro who foreign
    simpa only [foreign, ite_false] using full who
  · rw [erased]
    exact density

end Vegas.SourceProgram.Setup
