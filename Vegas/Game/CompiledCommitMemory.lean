/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledAttemptObservation
import Vegas.Source.CommitRecoveryErasedStep
import Vegas.Source.CommitRecoveryInstructions
import Vegas.Source.CommitRecoveryObservedMemory

/-! # The native commitment decoder retains semantic fields independently of memory -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}


/-- Replacing the remembered entry word changes neither decoded semantic fields,
physical omissions nor the exact original instruction word. It is the same decoder
and the same physical accepted catalogue, including accepted failed bindings. -/
theorem decodeCommitAttempt_eraseHistory
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (block.prepend suffix))
      (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
      (entry : Config Player L Γ) (past : History Player L) (excluded : Finset Player),
      let actual := decodeCommitAttempt whole mode block suffix embedding native entry excluded
      let changed := decodeCommitAttempt whole mode block suffix embedding native
        {entry with history := past} excluded
      {changed.1 with history := fun _ => []} = {actual.1 with history := fun _ => []} ∧
        changed.2.1 = actual.2.1 ∧ changed.2.2.joints = actual.2.2.joints := by
  induction block with
  | nil => intro suffix embedding native entry past excluded; exact ⟨rfl, rfl, rfl⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding native entry past excluded
      let event := embedding.event ⟨0, by
        simp only [CommitPrefix.prepend, eventCount]
        omega⟩
      let tailEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      by_cases inactive : owner ∈ excluded
      · let actualTail := decodeCommitAttempt whole mode rest suffix tailEmbedding native
          (automaticCommit name owner payload entry) excluded
        let changedTail := decodeCommitAttempt whole mode rest suffix tailEmbedding native
          (automaticCommit name owner payload {entry with history := past}) excluded
        have actualEq : decodeCommitAttempt whole mode (.commit name owner fresh guard rest)
            suffix embedding native entry excluded =
            ⟨actualTail.1, actualTail.2.1, .excluded inactive actualTail.2.2⟩ := by
          unfold decodeCommitAttempt
          rw [dite_eq_left inactive]
        have changedEq : decodeCommitAttempt whole mode (.commit name owner fresh guard rest)
            suffix embedding native {entry with history := past} excluded =
            ⟨changedTail.1, changedTail.2.1, .excluded inactive changedTail.2.2⟩ := by
          unfold decodeCommitAttempt
          rw [dite_eq_left inactive]
        have next := ih suffix tailEmbedding native (automaticCommit name owner payload entry)
          past excluded
        dsimp only
        rw [actualEq, changedEq]
        exact ⟨next.1, next.2.1, congrArg (List.cons (fun _ => none)) next.2.2⟩
      · let accepted := native.accepted (.inr event)
        let choice := accepted.elim PublicationResult.failure
          (fun candidate => native.bindingResult candidate payload)
        let nextPast := Function.update past owner
          (past owner ++ [OwnAction.commit owner name payload choice])
        have missingFailure : accepted.isNone = true → choice = .failure := by
          cases found : accepted <;>
            simp only [choice, found, Option.isNone_none, Option.isNone_some,
              Option.elim_none, Bool.false_eq_true, false_implies, implies_true]
        let actualTail := decodeCommitAttempt whole mode rest suffix tailEmbedding native
          (commitSuccessor name guard entry choice) (excludeCommit excluded owner accepted.isNone)
        let changedTail := decodeCommitAttempt whole mode rest suffix tailEmbedding native
          (commitSuccessor name guard {entry with history := past} choice)
          (excludeCommit excluded owner accepted.isNone)
        have actualEq : decodeCommitAttempt whole mode (.commit name owner fresh guard rest)
            suffix embedding native entry excluded =
            ⟨actualTail.1, actualTail.2.1,
              .active inactive choice accepted.isNone missingFailure actualTail.2.2⟩ := by
          unfold decodeCommitAttempt
          rw [dite_eq_right inactive]
        have changedEq : decodeCommitAttempt whole mode (.commit name owner fresh guard rest)
            suffix embedding native {entry with history := past} excluded =
            ⟨changedTail.1, changedTail.2.1,
              .active inactive choice accepted.isNone missingFailure changedTail.2.2⟩ := by
          unfold decodeCommitAttempt
          rw [dite_eq_right inactive]
        have next := ih suffix tailEmbedding native (commitSuccessor name guard entry choice)
          nextPast (excludeCommit excluded owner accepted.isNone)
        dsimp only
        rw [actualEq, changedEq]
        exact ⟨next.1, next.2.1, congrArg (List.cons (fun player : Player =>
          if player = owner then some
            (⟨.commit owner name payload choice, accepted.isNone⟩ : CommitRecoveryMove Player L)
          else none)) next.2.2⟩

/-- Equal actual typed entry cells suffice for the decoded typed result cells.
The two previous private words may differ; both original missing scans are kept. -/
theorem decodeCommitAttempt_semantic_view_eq
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (first second : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (who : Player) (firstEntry secondEntry : Config Player L Γ) (excluded : Finset Player)
    (entry : (firstEntry.view who).1 = (secondEntry.view who).1)
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph whole).withMode mode).playerObserve who first.config =
      ((toEventGraph whole).withMode mode).playerObserve who second.config)
    (firstCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → embedding.event index ∈ first.config.cut.completed)
    (secondCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → embedding.event index ∈ second.config.cut.completed) :
    ((decodeCommitAttempt whole mode block suffix embedding first firstEntry excluded).1.view
          who).1 =
        ((decodeCommitAttempt whole mode block suffix embedding second secondEntry excluded).1.view
          who).1 ∧
      (decodeCommitAttempt whole mode block suffix embedding first firstEntry excluded).2.1 =
        (decodeCommitAttempt whole mode block suffix embedding second secondEntry
          excluded).2.1 := by
  have compared := decodeCommitAttempt_view_eq whole mode block suffix embedding first second
    firstValid secondValid who {firstEntry with history := fun _ => []}
    {secondEntry with history := fun _ => []} excluded
    (Prod.ext entry rfl) publicView observed firstCompleted secondCompleted
  have left := decodeCommitAttempt_eraseHistory whole mode block suffix embedding first
    firstEntry (fun _ => []) excluded
  have right := decodeCommitAttempt_eraseHistory whole mode block suffix embedding second
    secondEntry (fun _ => []) excluded
  constructor
  · have cells := congrArg (fun config : Config Player L Δ => (config.view who).1) left.1
    have other := congrArg (fun config : Config Player L Δ => (config.view who).1) right.1
    exact cells.symm.trans ((congrArg Prod.fst compared.1).trans other)
  · exact left.2.1.symm.trans (compared.2.trans right.2.1)

/-- Erasing the remembered words commutes with installing the actual decoded
block and its real close, including retry and exhausted restore. -/
theorem decodeCommitAttempt_install_eraseHistory
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    {lift : ProtocolState (block.prepend suffix) → ProtocolState whole}
    (origin : ProtocolSuffix whole (block.prepend suffix) lift)
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : Config Player L Γ) (state : CommitRecoveryState whole) :
    let actual := decodeCommitAttempt whole mode block suffix embedding native entry state.excluded
    let changed := decodeCommitAttempt whole mode block suffix embedding native
      {entry with history := fun _ => []} state.excluded
    let actualRaw := state.install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix actual.1)), actual.2.1)
      (fun _ member => actual.2.2.excluded_subset member)
    let changedRaw := state.eraseHistory.install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix changed.1)), changed.2.1)
      (fun _ member => changed.2.2.excluded_subset member)
    actualRaw.close.eraseHistory = changedRaw.close.eraseHistory := by
  intro actual changed actualRaw changedRaw
  have decoded := decodeCommitAttempt_eraseHistory whole mode block suffix embedding native
    entry (fun _ => []) state.excluded
  have points : ProtocolState.withHistory whole
      (lift (block.liftPoint suffix (ProtocolState.entry suffix actual.1))) (fun _ => []) =
      ProtocolState.withHistory whole
        (lift (block.liftPoint suffix (ProtocolState.entry suffix changed.1)))
        (fun _ => []) := by
    simpa only [← origin.withHistory_lift, ← (block.protocolSuffix suffix).withHistory_lift,
      ProtocolState.withHistory_entry] using
      congrArg (fun config : Config Player L Δ =>
        lift (block.liftPoint suffix (ProtocolState.entry suffix config))) decoded.1.symm
  have exclusions : actual.2.1 = changed.2.1 := decoded.2.1.symm
  have raw : actualRaw.eraseHistory = changedRaw.eraseHistory := by
    dsimp only [actualRaw, changedRaw, CommitRecoveryState.eraseHistory,
      CommitRecoveryState.install]
    simp only [ProtocolState.withHistory_withHistory, points, exclusions]
  rw [CommitRecoveryState.eraseHistory_close, CommitRecoveryState.eraseHistory_close, raw]

end Vegas
