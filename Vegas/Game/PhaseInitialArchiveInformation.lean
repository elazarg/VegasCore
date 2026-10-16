/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitChronology
import Vegas.Game.RecoveryCheckpointHistory

/-! # Initial archived source information determined by actual physical observations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At the initial archived attempt, equal actual owner inputs determine the
complete chosen source information at the real close, including retry and
exhaustion. The real setup draw supplies the prior-information base. -/
theorem phase_initial_archive_information_eq_of_observed
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some second))
    (who : Player) (survives : who ∉ first.execution.application.current.excluded)
    (record : RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))
    (selected : first.execution.application.retired[0]? = some record)
    (phase : record.attempt.phase = 0) (generation : record.attempt.generation = 0)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    ∃ (firstFinal : RecoverySourceCheckpoint setup mode first.execution.application)
      (secondFinal : RecoverySourceCheckpoint setup mode second.execution.application)
      (leftState rightState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
      (left : RecoverySourceCheckpoint setup mode leftState)
      (right : RecoverySourceCheckpoint setup mode rightState)
      (rightRecord : RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))
      (leftClosed rightClosed : setup.commitRecoveryProtocol.History)
      (leftSteps rightSteps leftLater rightLater : Nat),
      firstFinal.ArchivedRecall ∧ secondFinal.ArchivedRecall ∧
      ArchivedSourceOrigins setup mode first.execution.application.retired ⟨_, firstFinal.trace⟩ ∧
      ArchivedSourceOrigins setup mode second.execution.application.retired
        ⟨_, secondFinal.trace⟩ ∧
      second.execution.application.retired[0]? = some rightRecord ∧
      leftState.attempt = record.attempt ∧ rightState.attempt = rightRecord.attempt ∧
      setup.commitRecoveryProtocol.ReachesWithin leftSteps ⟨_, left.trace⟩ leftClosed ∧
      setup.commitRecoveryProtocol.ReachesWithin rightSteps ⟨_, right.trace⟩ rightClosed ∧
      setup.recoveryJointRecall leftClosed.trace =
        (left.commitInstructionWord record.state).reverse ++
          setup.recoveryJointRecall left.trace ∧
      setup.recoveryJointRecall rightClosed.trace =
        (right.commitInstructionWord rightRecord.state).reverse ++
          setup.recoveryJointRecall right.trace ∧
      setup.commitRecoveryProtocol.ReachesWithin leftLater leftClosed ⟨_, firstFinal.trace⟩ ∧
      setup.commitRecoveryProtocol.ReachesWithin rightLater rightClosed ⟨_, secondFinal.trace⟩ ∧
      setup.commitRecoveryModel.infoOf who leftClosed.trace =
        setup.commitRecoveryModel.infoOf who rightClosed.trace := by
  let inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs :=
    setup.initialLaw.map encodeInputs
  have firstRaw : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact firstTrace
  have secondRaw : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact secondTrace
  have archives := congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
    view.application.2.retired) observed
  have lengths := congrArg List.length archives
  change (first.execution.application.retired.map _).length =
    (second.execution.application.retired.map _).length at lengths
  simp only [List.length_map] at lengths
  have bound : 0 < first.execution.application.retired.length :=
    List.getElem?_eq_some_iff.mp selected |>.1
  have secondBound : 0 < second.execution.application.retired.length := by omega
  let rightRecord := second.execution.application.retired[0]
  have secondSelected : second.execution.application.retired[0]? = some rightRecord :=
    List.getElem?_eq_getElem secondBound
  have firstRecord : first.execution.application.retired[0] = record := by
    exact Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans selected)
  obtain ⟨firstFinal, firstAligned, firstOrigins⟩ :=
    recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler
      firstTrace
  obtain ⟨secondFinal, secondAligned, secondOrigins⟩ :=
    recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler
      secondTrace
  obtain ⟨leftState, left, leftAligned, _leftEarlier, leftArchives, leftAttempt, leftRetained,
    leftSaved, leftAgrees, leftPositive, leftClosed, leftSteps, leftLater, leftPath,
    leftInstructions, leftFollowing⟩ := firstOrigins.get 0 bound
  obtain ⟨rightState, right, rightAligned, _rightEarlier, rightArchives, rightAttempt,
    rightRetained, rightSaved, rightAgrees, rightPositive, rightClosed, rightSteps, rightLater,
    rightPath,
    rightInstructions, rightFollowing⟩ := secondOrigins.get 0 secondBound
  rw [firstRecord] at leftAttempt leftRetained leftAgrees leftInstructions
  have native := phaseArchivedSavedObservations_eq_of_observed runtime leaks plan inputs horizon
    scheduler firstRaw secondRaw who 0 observed
  simp only [selected, secondSelected, Option.map_some] at native
  have attempts := congrArg Prod.fst (Option.some.inj native)
  have sameAttempt : leftState.attempt = rightState.attempt :=
    leftAttempt.trans (attempts.trans rightAttempt.symm)
  have firstInitial := left.initial_clear
    ((congrArg CommitAttemptId.phase leftAttempt).trans phase)
    ((congrArg CommitAttemptId.generation leftAttempt).trans generation)
  have secondInitial := right.initial_clear
    ((congrArg CommitAttemptId.phase sameAttempt).symm.trans
      ((congrArg CommitAttemptId.phase leftAttempt).trans phase))
    ((congrArg CommitAttemptId.generation sameAttempt).symm.trans
      ((congrArg CommitAttemptId.generation leftAttempt).trans generation))
  have leftActive : who ∉ leftState.entry.excluded := by
    change leftState.entry.excluded = ∅ at firstInitial
    rw [firstInitial]
    exact Finset.notMem_empty who
  have rightActive : who ∉ rightState.entry.excluded := by
    change rightState.entry.excluded = ∅ at secondInitial
    rw [secondInitial]
    exact Finset.notMem_empty who
  have privateViews := phase_archived_saved_source_views_eq_of_observed runtime leaks plan inputs
    horizon scheduler firstRaw secondRaw who 0 record rightRecord selected secondSelected observed
    leftState rightState left right leftAligned rightAligned leftActive rightActive
    leftArchives rightArchives leftAttempt rightAttempt leftRetained rightRetained leftSaved
    rightSaved leftAgrees rightAgrees leftPositive rightPositive
  have privateBefore : setup.commitRecoveryPrivate who (some (CommitRecoveryState.atPoint
      (left.residual.lift (ProtocolState.entry left.residual.tail left.source))
        leftState.entry.excluded leftState.generation)) =
      setup.commitRecoveryPrivate who (some (CommitRecoveryState.atPoint
        (right.residual.lift (ProtocolState.entry right.residual.tail right.source))
          rightState.entry.excluded rightState.generation)) := congrArg some privateViews
  have fullPrior := setup.commitRecovery_clear_info_eq who left.trace right.trace
    firstInitial secondInitial privateBefore
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who left.trace =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who right.trace at fullPrior
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at fullPrior
  have prior := congrArg Prod.fst fullPrior
  have information := phase_archived_chosen_information_eq_of_observed setup mode runtime leaks
    plan maximal
    inputs horizon scheduler firstRaw secondRaw who true id survives 0 record rightRecord selected
    secondSelected observed left right leftAttempt firstFinal secondFinal
    ⟨congrArg (fun info => setup.commitRecoveryHistorySignal who true info.1) prior,
      congrArg (setup.commitRecoveryProjectedRecall who true id) prior⟩ leftClosed
    rightClosed leftPath rightPath leftFollowing rightFollowing leftInstructions rightInstructions
  have information := setup.commitRecovery_surviving_info_eq who leftClosed.trace
    rightClosed.trace information.1 information.2.1
    (by simpa only [Setup.commitRecoveryProjectedRecall_true,
      List.map_id_fun, Prod.map_id, id_eq] using information.2.2.2)
  exact ⟨firstFinal, secondFinal, leftState, rightState, left, right, rightRecord, leftClosed,
    rightClosed, leftSteps, rightSteps, leftLater, rightLater, firstAligned, secondAligned,
    firstOrigins, secondOrigins,
    secondSelected, leftAttempt,
    rightAttempt, leftPath, rightPath, leftInstructions, rightInstructions, leftFollowing,
    rightFollowing, information⟩

end Vegas
