/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryInformationReadback
import Vegas.Game.ProposalRecoveryArchivePublicHistory
import Vegas.Game.CommitRecoveryGlobalWordDensity
import Vegas.Source.ProposalRecoveryChronology
import Vegas.Source.ProposalRecoveryMenuKind
import Vegas.Source.CommitRecoveryVoluntaryFailure

/-! # Full source fibers across distinct original input draws

The comparison retains the literal proposal chronology and focal labeled
word. It compares actual source traces, without changing initializer weights
or identifying different full joint inputs.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A surviving observer cannot have chosen the extra failed-disclosure
label: its semantic action actually excludes its author. Accepted failed
bindings remain literal ordinary actions in this statement. -/
theorem proposalRecovery_surviving_option_ordinary (who : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (survives : who ∉ (setup.commitRecoveryPublic after).1) :
    ((joint who).map (·.semantic)).map ProposalRecoveryMove.ordinary = joint who := by
  cases chosen : joint who with
  | none => rfl
  | some move =>
      have offered := legal.2 who
      rw [chosen] at offered
      have absent : move.proposed = false := by
        apply Bool.eq_false_iff.mpr
        intro proposed
        obtain ⟨owner, name, revealing⟩ := offered.2.2 proposed
        cases before with
        | none => exact offered.1.elim
        | some current =>
            have allowed : move.semantic ∈ ProtocolView.recoveryAvailable who setup.program
                (ProtocolState.observe who setup.program current.point) := offered.2.1
            have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal who
              setup.program current.point move.semantic allowed ⟨owner, name, false, revealing⟩
            let semanticTrace := setup.proposalRecoveryEraseTrace prior
            let semanticLegal := setup.proposalRecovery_erase_legal joint legal
            let choice : setup.commitRecoveryModel.Choice who
                (setup.commitRecoveryModel.infoOf who semanticTrace) :=
              ⟨proposalRecoveryJoint joint who,
                (setup.commitRecoveryModel.menu_adequate who semanticTrace _).mpr
                  (setup.commitRecoveryProtocol.legalOption_of_legal semanticLegal who)⟩
            have fails : ¬ setup.CommitRecoveryContinues who
                (setup.commitRecoveryModel.infoOf who semanticTrace) choice.1 := by
              intro continues
              have selected : choice.1 = some move.semantic := by
                simp only [choice, proposalRecoveryJoint, chosen, Option.map_some]
              have required := (continues move.semantic selected).2
              have observed :
                  (setup.commitRecoveryModel.infoOf who semanticTrace).1.1.1.elim false
                    (ProtocolView.atCommit who setup.program) = false := by
                rw [setup.commitRecovery_atCommit_info who semanticTrace]
                exact notCommit
              exact required observed (by rw [revealing]; trivial)
            have excluded := setup.commitRecovery_voluntaryFailure_step who semanticTrace choice
              fails (proposalRecoveryJoint joint) semanticLegal rfl after supported
            exact survives excluded
      change some (ProposalRecoveryMove.ordinary move.semantic) = some move
      cases move with
      | mk semantic proposed => cases absent; rfl

/-- All remembered labels of a surviving owner are the ordinary lift of its
literal semantic coordinates. This includes canceled accepted bad bindings
and every inactive NONE; foreign failed-disclosure copies remain unrestricted. -/
theorem proposalRecovery_surviving_coordinate_ordinary (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (survives : who ∉ (setup.commitRecoveryPublic state).1) :
    (setup.proposalRecoveryJointRecall trace).map (fun joint => joint who) =
      ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace)).map
        (fun joint => joint who)).map (Option.map ProposalRecoveryMove.ordinary) := by
  induction trace with
  | start => rfl
  | extend earlier joint legal supported ih =>
      have before : who ∉ (setup.commitRecoveryPublic _).1 := fun member =>
        survives (setup.commitRecovery_step_excluded_subset (proposalRecoveryJoint joint)
          (setup.proposalRecovery_erase_legal joint legal) supported member)
      have ordinary := setup.proposalRecovery_surviving_option_ordinary who earlier joint legal
        supported survives
      simp only [proposalRecoveryJointRecall, proposalRecoveryEraseTrace, recoveryJointRecall,
        List.map_cons, proposalRecoveryJoint, ih before, ordinary]

/-- Transport complete labeled information from two genuinely observed
prefixes. Foreign hidden inputs can differ; only the focal prefix observation
and own labeled word are fixed. This identifies a literal full information
fiber, rather than only a normalized query or public archive. -/
theorem proposalRecovery_info_eq_of_observed_prefixes (who : Player)
    (first second : CommitRecoveryState setup.program)
    (leftPrior : setup.proposalRecoveryProtocol.Trace (some first))
    (rightPrior : setup.proposalRecoveryProtocol.Trace (some second))
    (prefixClock : leftPrior.length = rightPrior.length)
    (prefixObserved :
      (ProtocolState.observe who setup.program first.point,
        ProtocolState.observe who setup.program first.saved,
        first.excluded, first.entryExcluded, first.generation) =
      (ProtocolState.observe who setup.program second.point,
        ProtocolState.observe who setup.program second.saved,
        second.excluded, second.entryExcluded, second.generation))
    (prefixInfo : setup.proposalRecoveryModel.infoOf who leftPrior =
      setup.proposalRecoveryModel.infoOf who rightPrior)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix leftPrior left)
    (rightRetained : TracePrefix rightPrior right)
    (publicWord : setup.proposalRecoveryPublicRecall who left =
      setup.proposalRecoveryPublicRecall who right)
    (coordinate : (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right).map (fun joint => joint who)) :
    setup.proposalRecoveryModel.infoOf who left = setup.proposalRecoveryModel.infoOf who right := by
  have semanticPrefix := congrArg (setup.proposalRecoveryEraseInfo who) prefixInfo
  rw [setup.proposalRecoveryEraseInfo_observed, setup.proposalRecoveryEraseInfo_observed]
    at semanticPrefix
  have semanticCoordinate :
      (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace left)).map
          (fun joint => joint who) =
        (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace right)).map
          (fun joint => joint who) := by
    rw [← setup.proposalRecoveryJointRecall_semantic,
      ← setup.proposalRecoveryJointRecall_semantic]
    have erased := congrArg (List.map (Option.map ProposalRecoveryMove.semantic)) coordinate
    simpa only [List.map_map, Function.comp_def, proposalRecoveryJoint] using erased
  have semantic := setup.commitRecovery_info_eq_of_observed_prefixes who first second
    (setup.proposalRecoveryEraseTrace leftPrior) (setup.proposalRecoveryEraseTrace rightPrior)
    (by simpa only [setup.proposalRecoveryEraseTrace_length] using prefixClock)
    prefixObserved semanticPrefix (setup.proposalRecoveryEraseTrace left)
    (setup.proposalRecoveryEraseTrace right)
    (setup.proposalRecoveryEraseTrace_prefix leftRetained)
    (setup.proposalRecoveryEraseTrace_prefix rightRetained)
    (setup.proposalRecoveryPublicRecall_semantic_eq who left right publicWord) semanticCoordinate
  exact setup.proposalRecovery_info_eq_of_semantic_public_coordinate who left right semantic
    publicWord coordinate

/-- Reconstruct complete labeled information after recovering only the
erased public record and the observer's cumulative actual own actions.
Survival recovers every raw omission flag and proposal label. No equality of
complete source information or complete joint coordinates is assumed. -/
theorem proposalRecovery_info_eq_of_erased_archive_and_own_history (who : Player)
    (first second : CommitRecoveryState setup.program)
    (leftPrior : setup.proposalRecoveryProtocol.Trace (some first))
    (rightPrior : setup.proposalRecoveryProtocol.Trace (some second))
    (prefixClock : leftPrior.length = rightPrior.length)
    (prefixObserved :
      (ProtocolState.observe who setup.program first.point,
        ProtocolState.observe who setup.program first.saved,
        first.excluded, first.entryExcluded, first.generation) =
      (ProtocolState.observe who setup.program second.point,
        ProtocolState.observe who setup.program second.saved,
        second.excluded, second.entryExcluded, second.generation))
    (prefixInfo : setup.proposalRecoveryModel.infoOf who leftPrior =
      setup.proposalRecoveryModel.infoOf who rightPrior)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix leftPrior left)
    (rightRetained : TracePrefix rightPrior right)
    (leftSurvives : who ∉ (setup.commitRecoveryPublic leftState).1)
    (rightSurvives : who ∉ (setup.commitRecoveryPublic rightState).1)
    (erased : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace left)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace right)))
    (archive : setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who left) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right))
    (ownedHistory :
      leftState.map (fun state => ProtocolState.history setup.program state.point who) =
        rightState.map (fun state => ProtocolState.history setup.program state.point who)) :
    setup.proposalRecoveryModel.infoOf who left = setup.proposalRecoveryModel.infoOf who right := by
  have publicWord := setup.proposalRecoveryPublicRecall_eq_of_erased_archive who left right
    erased archive
  have semanticPrefix := congrArg (setup.proposalRecoveryEraseInfo who) prefixInfo
  rw [setup.proposalRecoveryEraseInfo_observed, setup.proposalRecoveryEraseInfo_observed]
    at semanticPrefix
  have semanticCoordinate := setup.commitRecovery_coordinate_eq_of_public_and_own_history who
    first second (setup.proposalRecoveryEraseTrace leftPrior)
    (setup.proposalRecoveryEraseTrace rightPrior)
    (by simpa only [setup.proposalRecoveryEraseTrace_length] using prefixClock)
    (setup.commitRecovery_coordinate_eq_of_info_eq who _ _ semanticPrefix)
    (setup.proposalRecoveryEraseTrace left) (setup.proposalRecoveryEraseTrace right)
    (setup.proposalRecoveryEraseTrace_prefix leftRetained)
    (setup.proposalRecoveryEraseTrace_prefix rightRetained)
    (setup.proposalRecoveryPublicRecall_semantic_eq who left right publicWord)
    leftSurvives rightSurvives ownedHistory
  have coordinate :
      (setup.proposalRecoveryJointRecall left).map (fun joint => joint who) =
        (setup.proposalRecoveryJointRecall right).map (fun joint => joint who) := by
    rw [setup.proposalRecovery_surviving_coordinate_ordinary who left leftSurvives,
      setup.proposalRecovery_surviving_coordinate_ordinary who right rightSurvives,
      semanticCoordinate]
  exact setup.proposalRecovery_info_eq_of_observed_prefixes who first second leftPrior rightPrior
    prefixClock prefixObserved prefixInfo left right leftRetained rightRetained publicWord
    coordinate

end Vegas.SourceProgram.Setup
