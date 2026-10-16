/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseInitialArchiveInformation
import Vegas.Game.RecoveryRetryChronology
import Vegas.Pending.PhaseInitialRetryChronology

/-! # Full source information through an actual initial commitment retry window -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Equal actual full owner inputs determine complete source information at
every archived close in the initial commitment retry window. The actual
namespace pattern is derived from the initialized runtime history. Prior source
information follows from the real setup draw and exact chosen retry splices. -/
theorem phase_initial_retry_information_eq_of_observed
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
    (index : Nat) (record : RetiredCommitAttempt ((toEventGraph setup.program).withMode mode))
    (selected : first.execution.application.retired[index]? = some record)
    (atStart : first.execution.application.attempt.phase = 0)
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
      second.execution.application.retired[index]? = some rightRecord ∧
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
  have namespaces := PhaseRuntimeState.initial_phase_retry_namespaces runtime leaks plan inputs
    horizon scheduler firstRaw atStart
  have addresses : ∀ earlier ≤ index, ∀ previous,
      first.execution.application.retired[earlier]? = some previous →
        previous.attempt.phase = 0 ∧ previous.attempt.generation = earlier := by
    intro earlier _ previous chosen
    obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp chosen
    have address := namespaces.2 ⟨earlier, bound⟩
    change first.execution.application.retired[earlier].attempt = ⟨0, earlier⟩ at address
    rw [value] at address
    exact ⟨congrArg CommitAttemptId.phase address, congrArg CommitAttemptId.generation address⟩
  induction index generalizing record with
  | zero =>
      obtain ⟨phase, generation⟩ := addresses 0 (Nat.le_refl _) record selected
      exact phase_initial_archive_information_eq_of_observed setup mode runtime leaks plan maximal
        horizon scheduler firstTrace secondTrace who survives record selected phase generation
        observed
  | succ index ih =>
      let inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs :=
        setup.initialLaw.map encodeInputs
      have firstRaw : ((phaseApplication runtime leaks).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first) := by
        dsimp only [inputs]
        rw [PMF.map_comp]
        exact firstTrace
      have secondRaw : ((phaseApplication runtime leaks).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some second) := by
        dsimp only [inputs]
        rw [PMF.map_comp]
        exact secondTrace
      have bound : index + 1 < first.execution.application.retired.length :=
        List.getElem?_eq_some_iff.mp selected |>.1
      have oldBound : index < first.execution.application.retired.length := by omega
      let oldRecord := first.execution.application.retired[index]
      have oldSelected : first.execution.application.retired[index]? = some oldRecord :=
        List.getElem?_eq_getElem oldBound
      obtain ⟨firstFinal, secondFinal, oldLeftState, oldRightState, oldLeft, oldRight,
        oldRightRecord, oldLeftClosed, oldRightClosed, oldLeftSteps, oldRightSteps,
        oldLeftLater, oldRightLater, firstAligned, secondAligned, firstOrigins, secondOrigins,
        oldSecondSelected,
        oldLeftAttempt, oldRightAttempt, oldLeftPath, oldRightPath, oldLeftInstructions,
        oldRightInstructions, oldLeftFollowing, oldRightFollowing, oldInformation⟩ :=
          ih oldRecord oldSelected (fun earlier bounded previous chosen =>
            addresses earlier (bounded.trans (Nat.le_succ _)) previous chosen)
      have archives := congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
        view.application.2.retired) observed
      change first.execution.application.retired.map
          (fun record => (record.attempt, record.state.publicView)) =
        second.execution.application.retired.map
          (fun record => (record.attempt, record.state.publicView)) at archives
      have lengths := congrArg List.length archives
      change (first.execution.application.retired.map _).length =
        (second.execution.application.retired.map _).length at lengths
      simp only [List.length_map] at lengths
      have secondBound : index + 1 < second.execution.application.retired.length := by omega
      let rightRecord := second.execution.application.retired[index + 1]
      have secondSelected : second.execution.application.retired[index + 1]? = some rightRecord :=
        List.getElem?_eq_getElem secondBound
      have recordEq : first.execution.application.retired[index + 1] = record :=
        Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans selected)
      obtain ⟨leftState, left, _leftAligned, _leftEarlier, _leftArchives, leftAttempt,
        _leftRetained, _leftSaved, _leftAgrees, _leftPositive, leftClosed, leftSteps, leftLater,
        leftPath, leftInstructions, leftFollowing⟩ := firstOrigins.get (index + 1) bound
      obtain ⟨rightState, right, _rightAligned, _rightEarlier, _rightArchives, rightAttempt,
        _rightRetained, _rightSaved, _rightAgrees, _rightPositive, rightClosed, rightSteps,
        rightLater, rightPath, rightInstructions, rightFollowing⟩ :=
          secondOrigins.get (index + 1) secondBound
      rw [recordEq] at leftAttempt leftInstructions
      have sameAttempt (position : Nat) (leftRecord rightRecord : RetiredCommitAttempt
          ((toEventGraph setup.program).withMode mode))
          (leftSelected : first.execution.application.retired[position]? = some leftRecord)
          (rightSelected : second.execution.application.retired[position]? = some rightRecord) :
          leftRecord.attempt = rightRecord.attempt := by
        have selectedPublic := congrArg (fun records => records[position]?) archives
        simp only [List.getElem?_map, leftSelected, rightSelected, Option.map_some]
          at selectedPublic
        exact congrArg Prod.fst (Option.some.inj selectedPublic)
      have oldRightAddress := sameAttempt index oldRecord oldRightRecord oldSelected
        oldSecondSelected
      have rightAddress := sameAttempt (index + 1) record rightRecord selected secondSelected
      have oldMetadata := addresses index (Nat.le_succ _) oldRecord oldSelected
      have metadata := addresses (index + 1) (Nat.le_refl _) record selected
      have firstPhase : leftState.attempt.phase = oldLeftState.attempt.phase := by
        rw [leftAttempt, oldLeftAttempt, metadata.1, oldMetadata.1]
      have firstGeneration : leftState.generation = oldLeftState.generation + 1 := by
        change leftState.attempt.generation = oldLeftState.attempt.generation + 1
        rw [leftAttempt, oldLeftAttempt, metadata.2, oldMetadata.2]
      have secondPhase : rightState.attempt.phase = oldRightState.attempt.phase := by
        rw [rightAttempt, oldRightAttempt, ← rightAddress, ← oldRightAddress,
          metadata.1, oldMetadata.1]
      have secondGeneration : rightState.generation = oldRightState.generation + 1 := by
        change rightState.attempt.generation = oldRightState.attempt.generation + 1
        rw [rightAttempt, oldRightAttempt, ← rightAddress, ← oldRightAddress,
          metadata.2, oldMetadata.2]
      obtain ⟨oldPhase, oldMember, oldLow, oldKind, oldCompleted, _receipts, _failures⟩ :=
        (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler
          firstRaw).archives
          oldRecord (List.mem_of_getElem? oldSelected)
      have oldCommitting := (oldLeft.completed_commit_phase plan maximal oldPhase oldMember oldKind
        (oldLow.symm.trans (congrArg CommitAttemptId.phase oldLeftAttempt).symm) who
        oldRecord.state
        oldCompleted).1
      obtain ⟨rightPhase, rightMember, rightLow, rightKind, rightCompleted,
        _receipts, _failures⟩ :=
        (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler
          secondRaw).archives
          oldRightRecord (List.mem_of_getElem? oldSecondSelected)
      have rightCommitting := (oldRight.completed_commit_phase plan maximal rightPhase rightMember
        rightKind (rightLow.symm.trans (congrArg CommitAttemptId.phase oldRightAttempt).symm) who
        oldRightRecord.state rightCompleted).1
      have firstCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon
        scheduler
        firstRaw
      have secondCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon
        scheduler secondRaw
      have sameExcluded : first.execution.application.current.excluded =
          second.execution.application.current.excluded :=
        congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
          view.application.2.excluded) observed
      have secondSurvives : who ∉ second.execution.application.current.excluded := by
        rwa [← sameExcluded]
      have leftSplice := oldLeft.retry_chosen_history_eq left oldRecord.state oldCommitting
        firstPhase firstGeneration oldLeftClosed ⟨_, firstFinal.trace⟩ oldLeftPath
        oldLeftInstructions oldLeftFollowing (leftPath.trans leftFollowing) who
        (fun excluded => survives (firstCoverage.inherited excluded))
      have rightSplice := oldRight.retry_chosen_history_eq right oldRightRecord.state
        rightCommitting secondPhase secondGeneration oldRightClosed ⟨_, secondFinal.trace⟩
        oldRightPath oldRightInstructions oldRightFollowing (rightPath.trans rightFollowing) who
        (fun excluded => secondSurvives (secondCoverage.inherited excluded))
      have firstInfo := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.commitRecoveryModel.infoOf who history.trace) leftSplice
      have secondInfo := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.commitRecoveryModel.infoOf who history.trace) rightSplice
      have prior := firstInfo.symm.trans (oldInformation.trans secondInfo)
      change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who left.trace =
        setup.commitRecoverySignals.withOwnPlayRecall.infoOf who right.trace at prior
      rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at prior
      have information := phase_archived_chosen_information_eq_of_observed setup mode runtime leaks
        plan maximal inputs horizon scheduler firstRaw secondRaw who true id survives
        (index + 1) record
        rightRecord selected secondSelected observed left right leftAttempt firstFinal secondFinal
        ⟨congrArg (fun info => setup.commitRecoveryHistorySignal who true info.1.1) prior,
          congrArg (fun info => setup.commitRecoveryProjectedRecall who true id info.1) prior⟩
        leftClosed rightClosed
        leftPath rightPath leftFollowing
        rightFollowing leftInstructions rightInstructions
      have information := setup.commitRecovery_surviving_info_eq who leftClosed.trace
        rightClosed.trace information.1 information.2.1
        (by simpa only [Setup.commitRecoveryProjectedRecall_true,
      List.map_id_fun, Prod.map_id, id_eq] using information.2.2.2)
      exact ⟨firstFinal, secondFinal, leftState, rightState, left, right, rightRecord, leftClosed,
        rightClosed, leftSteps, rightSteps, leftLater, rightLater, firstAligned, secondAligned,
        firstOrigins, secondOrigins,
        secondSelected, leftAttempt, rightAttempt, leftPath, rightPath, leftInstructions,
        rightInstructions, leftFollowing, rightFollowing, information⟩

end Vegas
