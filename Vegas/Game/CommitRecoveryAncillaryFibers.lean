/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoverySpliceErasure
import Vegas.Source.CommitRecoveryErasedContinuation

/-! # Original source information-fiber exchange

The actual history substitution gives inverse maps between full source
information fibers. Original setup and Nature factors are retained.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private def background (focal : Player)
    (original exchanged : setup.commitRecoveryProtocol.History) : Prop :=
  (∃ first : CommitRecoveryState setup.program,
    ∃ prior : setup.commitRecoveryProtocol.Trace (some first),
      prior.length = 1 ∧ TracePrefix prior original.trace ∧ TracePrefix prior exchanged.trace) ∧
  setup.attemptPublicRecall focal exchanged.trace =
    setup.attemptPublicRecall focal original.trace ∧
  ∀ who, who ≠ focal →
    (setup.recoveryJointRecall exchanged.trace).map (fun joint => joint who) =
      (setup.recoveryJointRecall original.trace).map (fun joint => joint who)

private theorem background_symm (focal : Player)
    {original exchanged : setup.commitRecoveryProtocol.History}
    (same : setup.background focal original exchanged) :
    setup.background focal exchanged original := by
  obtain ⟨⟨first, prior, length, originalKept, exchangedKept⟩, publicWord, coordinates⟩ := same
  exact ⟨⟨first, prior, length, exchangedKept, originalKept⟩, publicWord.symm,
    fun who foreign => (coordinates who foreign).symm⟩

private theorem background_trans (focal : Player)
    {first middle last : setup.commitRecoveryProtocol.History}
    (left : setup.background focal first middle)
    (right : setup.background focal middle last) :
    setup.background focal first last := by
  obtain ⟨⟨initial, prior, length, firstKept, middleKept⟩, leftPublic, leftCoordinates⟩ := left
  obtain ⟨⟨otherInitial, otherPrior, otherLength, otherMiddle, lastKept⟩,
    rightPublic, rightCoordinates⟩ := right
  have equal := middleKept.eq_of_same_length otherMiddle (length.trans otherLength.symm)
  cases equal
  exact ⟨⟨initial, prior, length, firstKept, lastKept⟩,
    rightPublic.trans leftPublic,
    fun who foreign => (rightCoordinates who foreign).trans (leftCoordinates who foreign)⟩

private theorem background_info_unique (focal : Player)
    {first second : setup.commitRecoveryProtocol.History}
    (same : setup.background focal first second)
    (information : setup.commitRecoveryModel.infoOf focal first.trace =
      setup.commitRecoveryModel.infoOf focal second.trace) : first = second := by
  obtain ⟨⟨initial, prior, _, firstKept, secondKept⟩, publicWord, foreignCoordinates⟩ := same
  have coordinates who :
      (setup.recoveryJointRecall first.trace).map (fun joint => joint who) =
        (setup.recoveryJointRecall second.trace).map (fun joint => joint who) := by
    by_cases own : who = focal
    · subst who
      exact setup.commitRecovery_coordinate_eq_of_info_eq focal first.trace second.trace information
    · exact (foreignCoordinates who own).symm
  have lengths := congrArg List.length (coordinates focal)
  simp only [List.length_map] at lengths
  have joints : setup.recoveryJointRecall first.trace =
      setup.recoveryJointRecall second.trace := by
    apply List.ext_getElem lengths
    intro index firstInside secondInside
    funext who
    have selected := congrArg (fun word => word[index]?) (coordinates who)
    simpa only [List.getElem?_map, List.getElem?_eq_getElem firstInside,
      List.getElem?_eq_getElem secondInside, Option.map_some, Option.some.injEq] using selected
  exact setup.commitRecovery_history_eq_of_public_and_joints focal initial prior
    first.trace second.trace firstKept secondKept publicWord.symm joints

private theorem site_state_some (focal : Player)
    (site : setup.commitRecoveryModel.InformationSite focal)
    (history : setup.commitRecoveryModel.InformationHistory focal site.1) :
    ∃ current : CommitRecoveryState setup.program, history.1.state = some current := by
  have active := InformationModel.InformationSite.active setup.commitRecoveryModel site history
  cases state : history.1.state with
  | none =>
      rw [state] at active
      exact False.elim active
  | some current => exact ⟨current, rfl⟩

private theorem exchange_exists [Fintype Player]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (focal : Player)
    (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1)
    (representative : setup.commitRecoveryModel.InformationHistory focal target.1)
    (original : setup.commitRecoveryModel.InformationHistory focal source.1) :
    ∃ exchanged : setup.commitRecoveryModel.InformationHistory focal target.1,
      setup.background focal original.1 exchanged.1 ∧
      (∀ who, who ≠ focal → setup.commitRecoveryModel.infoOf who exchanged.1.trace =
        setup.commitRecoveryModel.infoOf who original.1.trace) ∧
      setup.commitRecoveryModel.counterfactualReachProbability strategy focal exchanged.1.trace =
        setup.commitRecoveryModel.counterfactualReachProbability strategy focal original.1.trace ∧
      setup.commitRecoveryErasedHistory exchanged.1 =
        setup.commitRecoveryErasedHistory original.1 := by
  have mineActive := InformationModel.InformationSite.active
    setup.commitRecoveryModel target representative
  have othersActive := InformationModel.InformationSite.active
    setup.commitRecoveryModel source original
  obtain ⟨mine, mineState⟩ := setup.site_state_some focal target representative
  obtain ⟨others, othersState⟩ := setup.site_state_some focal source original
  rcases representative with ⟨⟨mineOption, mineTrace⟩, mineInfo⟩
  rcases original with ⟨⟨othersOption, othersTrace⟩, othersInfo⟩
  cases mineState
  cases othersState
  obtain ⟨input, prior, length, originalKept, hybrid, satisfies, _⟩ :=
    setup.commitRecovery_hybrid_of_erasedInformation_eq strategy focal mine others
      mineTrace othersTrace (by rw [mineInfo, othersInfo]; exact same)
  obtain ⟨shape, hybridKept, publicWord, coordinates, focalInfo, foreignInfo, density, _⟩ :=
    satisfies
  have semantic := setup.commitRecovery_splice_erased_state_eq focal mine others
    mineTrace othersTrace mineActive.2 othersActive.2 (by rw [mineInfo, othersInfo]; exact same)
  have erased : setup.commitRecoveryErasedHistory hybrid =
      setup.commitRecoveryErasedHistory ⟨some others, othersTrace⟩ := by
    apply Prod.ext
    · change hybrid.state.map CommitRecoveryState.eraseHistory = some others.eraseHistory
      rw [shape]
      exact congrArg some semantic
    · funext who
      by_cases own : who = focal
      · subst who
        change setup.commitRecoveryErasedInformation focal
            (setup.commitRecoveryModel.infoOf focal hybrid.trace) =
          setup.commitRecoveryErasedInformation focal
            (setup.commitRecoveryModel.infoOf focal othersTrace)
        rw [focalInfo, mineInfo, othersInfo]
        exact same
      · exact congrArg (setup.commitRecoveryErasedInformation who) (foreignInfo who own)
  exact ⟨⟨hybrid, focalInfo.trans mineInfo⟩,
    ⟨⟨_, prior, length, originalKept, hybridKept⟩, publicWord focal,
      fun who foreign => by simpa only [foreign, ↓reduceIte] using coordinates who⟩,
    foreignInfo, density, erased⟩

/-- Equal actual erased keys induce a bijection of the ORIGINAL full-information
fibers. The bijection preserves all opponents' full information and the exact
counterfactual reach under any original source profile. Its inverse restores
the entire original History, not merely the semantic reset state. -/
theorem commitRecovery_information_fiber_equiv [Fintype Player]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (focal : Player)
    (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    ∃ exchange : setup.commitRecoveryModel.InformationHistory focal source.1 ≃
        setup.commitRecoveryModel.InformationHistory focal target.1,
      ∀ original,
        setup.attemptPublicRecall focal (exchange original).1.trace =
          setup.attemptPublicRecall focal original.1.trace ∧
        (∀ who, who ≠ focal → setup.commitRecoveryModel.infoOf who
          (exchange original).1.trace = setup.commitRecoveryModel.infoOf who original.1.trace) ∧
        setup.commitRecoveryModel.counterfactualReachProbability strategy focal
          (exchange original).1.trace =
            setup.commitRecoveryModel.counterfactualReachProbability strategy focal
              original.1.trace ∧
        setup.commitRecoveryErasedHistory (exchange original).1 =
          setup.commitRecoveryErasedHistory original.1 := by
  classical
  obtain ⟨targetRepresentative, _, _⟩ := target.2
  obtain ⟨sourceRepresentative, _, _⟩ := source.2
  let forward := fun original => Classical.choose
    (setup.exchange_exists strategy focal target source same targetRepresentative original)
  let backward := fun original => Classical.choose
    (setup.exchange_exists strategy focal source target same.symm sourceRepresentative original)
  have forwardSpec original := Classical.choose_spec
    (setup.exchange_exists strategy focal target source same targetRepresentative original)
  have backwardSpec original := Classical.choose_spec
    (setup.exchange_exists strategy focal source target same.symm sourceRepresentative original)
  refine ⟨⟨forward, backward, ?_, ?_⟩, ?_⟩
  · intro original
    apply Subtype.ext
    exact (setup.background_info_unique focal
      (setup.background_trans focal (forwardSpec original).1
        (backwardSpec (forward original)).1)
      (original.2.trans (backward (forward original)).2.symm)).symm
  · intro original
    apply Subtype.ext
    exact (setup.background_info_unique focal
      (setup.background_trans focal (backwardSpec original).1
        (forwardSpec (backward original)).1)
      (original.2.trans (forward (backward original)).2.symm)).symm
  · intro original
    exact ⟨(forwardSpec original).1.2.1, (forwardSpec original).2⟩

end Vegas.SourceProgram.Setup
