/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseInitialRetryInformation
import Vegas.Game.RecoverySavedSourceView

/-! # Actual saved source information in the initial commitment phase -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At a genuine binding request before leaving the initial static phase,
equal full owner inputs determine the complete saved source information.
Every prior retry is reconstructed from the actual archived instruction word. -/
theorem phase_initial_saved_information_eq_of_observed
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
    (atStart : first.execution.application.attempt.phase = 0)
    (event : ((toEventGraph setup.program).withMode mode).EventId) (payload : L.Ty)
    (binding : ((toEventGraph setup.program).withMode mode).outputLayout event =
      .binding who payload)
    (firstRequest : first.execution.application.SeedRequest who
      ⟨first.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest who
      ⟨second.execution.application.attempt, event⟩)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    ∃ (left : RecoverySourceCheckpoint setup mode first.execution.application)
      (right : RecoverySourceCheckpoint setup mode second.execution.application),
      left.ArchivedRecall ∧ right.ArchivedRecall ∧
      ArchivedSourceOrigins setup mode first.execution.application.retired ⟨_, left.trace⟩ ∧
      ArchivedSourceOrigins setup mode second.execution.application.retired ⟨_, right.trace⟩ ∧
      setup.commitRecoveryModel.infoOf who left.trace =
        setup.commitRecoveryModel.infoOf who right.trace := by
  let := Fintype.ofFinite Player
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
  have sameAttempt : first.execution.application.attempt = second.execution.application.attempt :=
    congrArg (fun view => view.application.2.attempt) observed
  have secondStart : second.execution.application.attempt.phase = 0 := by
    rw [← sameAttempt]
    exact atStart
  have firstNamespaces := PhaseRuntimeState.initial_phase_retry_namespaces runtime leaks plan
    inputs horizon scheduler firstRaw atStart
  have secondNamespaces := PhaseRuntimeState.initial_phase_retry_namespaces runtime leaks plan
    inputs horizon scheduler secondRaw secondStart
  have sameGeneration : first.execution.application.generation =
      second.execution.application.generation := congrArg CommitAttemptId.generation sameAttempt
  have secondSurvives : who ∉ second.execution.application.current.excluded := by
    have sameExcluded : first.execution.application.current.excluded =
        second.execution.application.current.excluded :=
      congrArg (fun view => view.application.2.excluded) observed
    rwa [← sameExcluded]
  cases count : first.execution.application.retired.length with
  | zero =>
      obtain ⟨left, leftAligned, _leftChronology, leftOrigins⟩ :=
        recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler
          firstTrace
      obtain ⟨right, rightAligned, _rightChronology, rightOrigins⟩ :=
        recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler
          secondTrace
      have firstGeneration : first.execution.application.generation = 0 :=
        firstNamespaces.1.trans count
      have secondGeneration : second.execution.application.generation = 0 :=
        sameGeneration.symm.trans firstGeneration
      have firstInitial := left.initial_clear atStart firstGeneration
      have secondInitial := right.initial_clear secondStart secondGeneration
      have views := phase_saved_source_views_eq_of_observed setup mode runtime leaks plan maximal
        horizon scheduler firstTrace secondTrace left right leftAligned rightAligned who event
        payload binding firstRequest secondRequest observed
      have privateViews : setup.commitRecoveryPrivate who (some (CommitRecoveryState.atPoint
          (left.residual.lift (ProtocolState.entry left.residual.tail left.source))
            first.execution.application.entry.excluded first.execution.application.generation)) =
        setup.commitRecoveryPrivate who (some (CommitRecoveryState.atPoint
          (right.residual.lift (ProtocolState.entry right.residual.tail right.source))
            second.execution.application.entry.excluded
              second.execution.application.generation)) :=
        congrArg some views
      exact ⟨left, right, leftAligned, rightAligned, leftOrigins, rightOrigins,
        setup.commitRecovery_clear_info_eq who left.trace right.trace firstInitial secondInitial
          privateViews⟩
  | succ index =>
      have bound : index < first.execution.application.retired.length := by omega
      let record := first.execution.application.retired[index]
      have selected : first.execution.application.retired[index]? = some record :=
        List.getElem?_eq_getElem bound
      obtain ⟨left, right, leftState, rightState, oldLeft, oldRight, rightRecord,
        leftClosed, rightClosed, leftSteps, rightSteps, leftLater, rightLater,
        leftAligned, rightAligned, leftOrigins, rightOrigins, rightSelected, leftAttempt,
        rightAttempt, leftPath, rightPath, leftInstructions, rightInstructions,
        leftFollowing, rightFollowing, information⟩ :=
          phase_initial_retry_information_eq_of_observed setup mode runtime leaks plan maximal
            horizon scheduler firstTrace secondTrace who survives index record selected atStart
            observed
      have recordAddress := firstNamespaces.2 ⟨index, bound⟩
      change record.attempt = ⟨0, index⟩ at recordAddress
      have secondCount : second.execution.application.retired.length = index + 1 := by
        rw [← secondNamespaces.1, ← sameGeneration, firstNamespaces.1, count]
      have rightBound : index < second.execution.application.retired.length := by omega
      have rightRecordEq : second.execution.application.retired[index] = rightRecord :=
        Option.some.inj ((List.getElem?_eq_getElem rightBound).symm.trans rightSelected)
      have rightAddress := secondNamespaces.2 ⟨index, rightBound⟩
      change second.execution.application.retired[index].attempt = ⟨0, index⟩ at rightAddress
      rw [rightRecordEq] at rightAddress
      obtain ⟨phase, member, low, kind, completed, _receipts, _failures⟩ :=
        (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler
          firstRaw).archives record (List.mem_of_getElem? selected)
      have committing := (oldLeft.completed_commit_phase plan maximal phase member kind
        (low.symm.trans (congrArg CommitAttemptId.phase leftAttempt).symm) who record.state
        completed).1
      obtain ⟨otherPhase, otherMember, otherLow, otherKind, otherCompleted,
        _receipts, _failures⟩ :=
        (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler
          secondRaw).archives rightRecord (List.mem_of_getElem? rightSelected)
      have otherCommitting := (oldRight.completed_commit_phase plan maximal otherPhase otherMember
        otherKind (otherLow.symm.trans (congrArg CommitAttemptId.phase rightAttempt).symm) who
        rightRecord.state otherCompleted).1
      have phaseEq : first.execution.application.attempt.phase = leftState.attempt.phase := by
        rw [atStart, leftAttempt, recordAddress]
      have generationEq : first.execution.application.generation = leftState.generation + 1 := by
        change first.execution.application.generation = leftState.attempt.generation + 1
        rw [firstNamespaces.1, count, leftAttempt, recordAddress]
      have otherPhaseEq : second.execution.application.attempt.phase =
          rightState.attempt.phase := by
        rw [secondStart, rightAttempt, rightAddress]
      have otherGenerationEq : second.execution.application.generation =
          rightState.generation + 1 := by
        change second.execution.application.generation = rightState.attempt.generation + 1
        rw [secondNamespaces.1, secondCount, rightAttempt, rightAddress]
      have firstCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon
        scheduler firstRaw
      have secondCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon
        scheduler secondRaw
      have leftSplice := oldLeft.retry_chosen_history_eq left record.state committing phaseEq
        generationEq leftClosed ⟨_, left.trace⟩ leftPath leftInstructions leftFollowing (.refl 0 _)
        who (fun excluded => survives (firstCoverage.inherited excluded))
      have rightSplice := oldRight.retry_chosen_history_eq right rightRecord.state otherCommitting
        otherPhaseEq otherGenerationEq rightClosed ⟨_, right.trace⟩ rightPath rightInstructions
        rightFollowing (.refl 0 _) who
        (fun excluded => secondSurvives (secondCoverage.inherited excluded))
      have leftInfo := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.commitRecoveryModel.infoOf who history.trace) leftSplice
      have rightInfo := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.commitRecoveryModel.infoOf who history.trace) rightSplice
      exact ⟨left, right, leftAligned, rightAligned, leftOrigins, rightOrigins,
        leftInfo.symm.trans (information.trans rightInfo)⟩

end Vegas
