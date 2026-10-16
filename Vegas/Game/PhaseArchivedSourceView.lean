/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Pending.PhaseArchivedSavedObservation
import Vegas.Source.CommitRecoveryOwnHistory

/-! # Archived chosen source views determined by actual owner observations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem source_excluded_subset_of_reaches
    (setup : Setup (Player := Player) (L := L))
    {fuel : Nat} {first last : setup.commitRecoveryProtocol.History}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel first last) :
    (setup.commitRecoveryPublic first.state).1 ⊆
      (setup.commitRecoveryPublic last.state).1 := by
  induction reached with
  | refl => exact Finset.Subset.refl _
  | step joint legal supported _rest ih =>
      exact (setup.commitRecovery_step_excluded_subset joint legal supported).trans ih

/-- Equal real owner inputs determine both earlier chosen source views at any
retired attempt. Earlier coherent source histories and their archive prefixes are
retained; no given source view or source-information equality is assumed. -/
theorem phase_archived_source_views_eq_of_observed [Finite Player]
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
    (index : Nat) (bound : index < first.execution.application.retired.length)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    ∃ (leftState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
      (left : RecoverySourceCheckpoint setup mode leftState)
      (rightState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
      (right : RecoverySourceCheckpoint setup mode rightState),
      leftState.retired = first.execution.application.retired.take index ∧
      rightState.retired = second.execution.application.retired.take index ∧
      ArchivedSourceOrigins setup mode leftState.retired ⟨_, left.trace⟩ ∧
      ArchivedSourceOrigins setup mode rightState.retired ⟨_, right.trace⟩ ∧
      leftState.attempt = rightState.attempt ∧
      ProtocolState.observe who setup.program (left.residual.lift
          (ProtocolState.entry left.residual.tail left.source)) =
        ProtocolState.observe who setup.program (right.residual.lift
          (ProtocolState.entry right.residual.tail right.source)) := by
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
  have archives := congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
    view.application.2.retired) observed
  have lengths := congrArg List.length archives
  change (first.execution.application.retired.map _).length =
    (second.execution.application.retired.map _).length at lengths
  simp only [List.length_map] at lengths
  have secondBound : index < second.execution.application.retired.length := by omega
  let leftRecord := first.execution.application.retired[index]
  let rightRecord := second.execution.application.retired[index]
  have firstSelected : first.execution.application.retired[index]? = some leftRecord :=
    List.getElem?_eq_getElem bound
  have secondSelected : second.execution.application.retired[index]? = some rightRecord :=
    List.getElem?_eq_getElem secondBound
  obtain ⟨firstCheckpoint, _firstAligned, _firstChronology, firstOrigins⟩ :=
    recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler
      firstTrace
  obtain ⟨secondCheckpoint, _secondAligned, _secondChronology, secondOrigins⟩ :=
    recoverySourceCheckpoint_history setup mode runtime leaks plan maximal horizon scheduler
      secondTrace
  obtain ⟨leftState, left, leftAligned, leftEarlier, leftArchives, leftAttempt, leftRetained,
    leftSaved, leftAgrees, leftPositive, leftClosed, leftSteps, leftLater, leftPath,
    _leftInstructions, leftFollowing⟩ := firstOrigins.get index bound
  obtain ⟨rightState, right, rightAligned, rightEarlier, rightArchives, rightAttempt, rightRetained,
    rightSaved, rightAgrees, rightPositive, rightClosed, rightSteps, rightLater, rightPath,
    _rightInstructions, rightFollowing⟩ := secondOrigins.get index secondBound
  have leftSubset := source_excluded_subset_of_reaches setup (leftPath.trans leftFollowing)
  have rightSubset := source_excluded_subset_of_reaches setup (rightPath.trans rightFollowing)
  change leftState.entry.excluded ⊆ first.execution.application.entry.excluded at leftSubset
  change rightState.entry.excluded ⊆ second.execution.application.entry.excluded at rightSubset
  have firstCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    firstRaw
  have secondCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    secondRaw
  have sameExcluded : first.execution.application.current.excluded =
      second.execution.application.current.excluded :=
    congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
      view.application.2.excluded) observed
  have rightSurvives : who ∉ second.execution.application.current.excluded := by
    rwa [← sameExcluded]
  have leftActive : who ∉ leftState.entry.excluded :=
    fun inactive => survives (firstCoverage.inherited (leftSubset inactive))
  have rightActive : who ∉ rightState.entry.excluded :=
    fun inactive => rightSurvives (secondCoverage.inherited (rightSubset inactive))
  have native := phaseArchivedSavedObservations_eq_of_observed runtime leaks plan inputs horizon
    scheduler firstRaw secondRaw who index observed
  simp only [firstSelected, secondSelected, Option.map_some] at native
  have pair := Option.some.inj native
  have attempts := congrArg Prod.fst pair
  have observations := congrArg Prod.snd pair
  have sameAttempt : leftState.attempt = rightState.attempt :=
    leftAttempt.trans (attempts.trans rightAttempt.symm)
  have own := congrArg (fun view :
      ((toEventGraph setup.program).withMode mode).PlayerObservation who =>
    view.ownActions) observations
  change ((toEventGraph setup.program).withMode mode).ownCompletions who
      (PhaseRuntimeState.archivedHistory (first.execution.application.retired.take index)
        (leftRecord.state.config.history.filter fun completion =>
          completion.event.val < leftRecord.attempt.phase)) =
    ((toEventGraph setup.program).withMode mode).ownCompletions who
      (PhaseRuntimeState.archivedHistory (second.execution.application.retired.take index)
        (rightRecord.state.config.history.filter fun completion =>
          completion.event.val < rightRecord.attempt.phase)) at own
  change leftState.attempt = leftRecord.attempt at leftAttempt
  change rightState.attempt = rightRecord.attempt at rightAttempt
  rw [← leftArchives, ← rightArchives, ← leftAttempt, ← rightAttempt] at own
  have words := decodeHistory_fromMode_congr setup.program mode _ _ who own
  have leftWord := left.saved_history_of_retained_image leftAligned who leftActive
    leftRecord.state.config leftRetained leftSaved
  have rightWord := right.saved_history_of_retained_image rightAligned who rightActive
    rightRecord.state.config rightRetained rightSaved
  have sameWord : left.source.history who = right.source.history who :=
    leftWord.trans (words.trans rightWord.symm)
  have stores := congrArg (fun view :
      ((toEventGraph setup.program).withMode mode).PlayerObservation who =>
    view.store) observations
  have leftDecode := ProtocolViewSuffix.decode_entry setup.program left.residual.tail
    left.refs left.embedding
    left.residual.lift left.views leftPositive who left.source leftRecord.state.config.store
      leftAgrees
  have rightDecode := ProtocolViewSuffix.decode_entry setup.program right.residual.tail
    right.refs right.embedding
    right.residual.lift right.views rightPositive who right.source rightRecord.state.config.store
      rightAgrees
  have sameEvent : left.embedding.event ⟨0, leftPositive⟩ =
      right.embedding.event ⟨0, rightPositive⟩ := by
    apply Fin.ext
    have leftRank := left.compiled.rankEq ⟨0, leftPositive⟩
    have rightRank := right.compiled.rankEq ⟨0, rightPositive⟩
    simp only [Nat.add_zero] at leftRank rightRank
    exact leftRank.trans ((congrArg CommitAttemptId.phase sameAttempt).trans rightRank.symm)
  change (toEventGraph setup.program).playerStore who leftRecord.state.config.store =
    (toEventGraph setup.program).playerStore who rightRecord.state.config.store at stores
  rw [sameEvent, stores, sameWord] at leftDecode
  exact ⟨leftState, left, rightState, right, leftArchives, rightArchives, leftEarlier,
    rightEarlier, sameAttempt, Option.some.inj (leftDecode.symm.trans rightDecode)⟩

end Vegas
