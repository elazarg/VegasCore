/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledAttemptObservation
import Vegas.Compile.ProtocolViewSuffix
import Vegas.Source.CommitRecoveryObservedClosure
import Vegas.Source.CommitRecoveryBlockEmbedding
import Vegas.Pending.ArchivePlayerObservation
import Vegas.Pending.PhaseArchivedExclusionEntries
import Vegas.Pending.PhaseRetiredCompletion

/-! # Processed source commitment observations recovered from real archives -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Equal actual owner inputs determine every decoded processed prefix in the
same retired attempt. The prior typed entry view and static interval containment
are induction data; native validity, completion, historical exclusions and the
original attempt generation are derived from the real archived histories. -/
theorem phase_archived_commit_prefix_view_eq_of_observed
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph whole).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player) (index : Nat)
    (left right : RetiredCommitAttempt ((toEventGraph whole).withMode mode))
    (firstSelected : first.execution.application.retired[index]? = some left)
    (secondSelected : second.execution.application.retired[index]? = some right)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (inside : ∀ phase ∈ plan.phases, left.attempt.phase = phase.low →
      ∀ selected : Fin (eventCount (block.prepend suffix)), selected.val < block.length →
        embedding.event selected ∈ phase.events)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (entry : firstEntry.view who = secondEntry.view who) :
    let firstExcluded := PhaseRuntimeState.archivedFailureOwners
        (first.execution.application.retired.take index) ∪
      left.state.failureOwnersBefore left.attempt.phase
    let secondExcluded := PhaseRuntimeState.archivedFailureOwners
        (second.execution.application.retired.take index) ∪
      right.state.failureOwnersBefore right.attempt.phase
    let firstDecoded := decodeCommitAttempt whole mode block suffix embedding left.state
      firstEntry firstExcluded
    let secondDecoded := decodeCommitAttempt whole mode block suffix embedding right.state
      secondEntry secondExcluded
    firstDecoded.1.view who = secondDecoded.1.view who ∧
      firstDecoded.2.1 = secondDecoded.2.1 ∧ firstExcluded = secondExcluded ∧
        left.attempt = right.attempt := by
  intro firstExcluded secondExcluded firstDecoded secondDecoded
  have sharedView : first.execution.application.publicView =
      second.execution.application.publicView :=
    congrArg (fun view : (phaseApplication runtime leaks).PlayerView => view.application.2) observed
  have archives := congrArg PhasePublicView.retired sharedView
  change first.execution.application.retired.map
      (fun record => (record.attempt, record.state.publicView)) =
    second.execution.application.retired.map
      (fun record => (record.attempt, record.state.publicView)) at archives
  have selectedPublic := congrArg (fun records => records[index]?) archives
  simp only [List.getElem?_map, firstSelected, secondSelected, Option.map_some] at selectedPublic
  have pair := Option.some.inj selectedPublic
  have sameAttempt := congrArg Prod.fst pair
  have samePublic := congrArg Prod.snd pair
  have native := phaseArchivedPlayerObservations_eq_of_observed runtime leaks plan inputs horizon
    scheduler firstTrace secondTrace who observed
  have selectedNative := congrArg (fun records => records[index]?) native
  simp only [List.getElem?_map, firstSelected, secondSelected, Option.map_some] at selectedNative
  have sameNative := congrArg Prod.snd (Option.some.inj selectedNative)
  have earlier := PhaseRuntimeState.archivedFailureOwners_eq_of_publicViews_eq
    (first.execution.application.retired.take index)
    (second.execution.application.retired.take index) (by
      simpa only [List.map_take] using congrArg (List.take index) archives)
  have failures : left.state.failureOwnersBefore left.attempt.phase =
      right.state.failureOwnersBefore right.attempt.phase := by
    rw [congrArg CommitAttemptId.phase sameAttempt]
    exact State.failureOwnersBefore_congr samePublic _
  have sameExcluded : firstExcluded = secondExcluded := congrArg₂ (fun a b => a ∪ b) earlier
    failures
  have firstMember := List.mem_of_getElem? firstSelected
  have secondMember := List.mem_of_getElem? secondSelected
  have leftValid := (phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler
    firstTrace left firstMember).1
  have rightValid := (phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler
    secondTrace right secondMember).1
  obtain ⟨phase, member, low, _kind, completed, _receipts, _failures⟩ :=
    (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler firstTrace).archives
      left firstMember
  have firstCompleted : ∀ selected : Fin (eventCount (block.prepend suffix)),
      selected.val < block.length → embedding.event selected ∈ left.state.config.cut.completed :=
    fun selected before => completed (inside phase member low selected before)
  have publicOrder := congrArg (fun view => view.observation.completionOrder) samePublic
  have secondCompleted : ∀ selected : Fin (eventCount (block.prepend suffix)),
      selected.val < block.length →
        embedding.event selected ∈ right.state.config.cut.completed := by
    intro selected before
    have present := (left.state.config.history_exact (embedding.event selected)).mpr
      (firstCompleted selected before)
    change embedding.event selected ∈ left.state.publicView.observation.completionOrder at present
    rw [publicOrder] at present
    exact (right.state.config.history_exact (embedding.event selected)).mp present
  have decoded := decodeCommitAttempt_view_eq whole mode block suffix embedding left.state
    right.state leftValid rightValid who firstEntry secondEntry firstExcluded entry samePublic
    sameNative firstCompleted secondCompleted
  refine ⟨?_, ?_, sameExcluded, sameAttempt⟩
  · exact decoded.1.trans (congrArg (fun owners =>
      (decodeCommitAttempt whole mode block suffix embedding right.state secondEntry owners).1.view
        who) sameExcluded)
  · exact decoded.2.trans (congrArg (fun owners =>
      (decodeCommitAttempt whole mode block suffix embedding right.state secondEntry owners).2.1)
        sameExcluded)

/-- Every processed archived prefix has the same full closed source signal in
equal actual owner-input fibers. The compiler suffix certificates identify the
real source positions; the closure includes its actual retry or exhaustion and
does not insert a fictitious pre-close signal. -/
theorem phase_archived_commit_signal_eq_of_observed
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph whole).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player) (index : Nat)
    (left right : RetiredCommitAttempt ((toEventGraph whole).withMode mode))
    (firstSelected : first.execution.application.retired[index]? = some left)
    (secondSelected : second.execution.application.retired[index]? = some right)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (inside : ∀ phase ∈ plan.phases, left.attempt.phase = phase.low →
      ∀ selected : Fin (eventCount (block.prepend suffix)), selected.val < block.length →
        embedding.event selected ∈ phase.events)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (entry : firstEntry.view who = secondEntry.view who)
    (refs : ContextRefs (graphLayout whole) Γ)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState whole)
    (views : ProtocolViewSuffix whole (block.prepend suffix) refs embedding lift)
    (tailRefs : ContextRefs (graphLayout whole) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) suffix)
    (tailViews : ProtocolViewSuffix whole suffix tailRefs tailEmbedding
      (fun point => lift (block.liftPoint suffix point))) :
    let firstExcluded := PhaseRuntimeState.archivedFailureOwners
        (first.execution.application.retired.take index) ∪
      left.state.failureOwnersBefore left.attempt.phase
    let secondExcluded := PhaseRuntimeState.archivedFailureOwners
        (second.execution.application.retired.take index) ∪
      right.state.failureOwnersBefore right.attempt.phase
    let firstDecoded := decodeCommitAttempt whole mode block suffix embedding left.state
      firstEntry firstExcluded
    let secondDecoded := decodeCommitAttempt whole mode block suffix embedding right.state
      secondEntry secondExcluded
    let firstStart := CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) firstEntry)) firstExcluded
      left.attempt.generation
    let secondStart := CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) secondEntry)) secondExcluded
      right.attempt.generation
    let firstRaw := firstStart.install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix firstDecoded.1)), firstDecoded.2.1)
      (fun _ member => firstDecoded.2.2.excluded_subset member)
    let secondRaw := secondStart.install
      (lift (block.liftPoint suffix (ProtocolState.entry suffix secondDecoded.1)),
        secondDecoded.2.1)
      (fun _ member => secondDecoded.2.2.excluded_subset member)
    (ProtocolState.observe who whole firstRaw.close.point,
        ProtocolState.observe who whole firstRaw.close.saved, firstRaw.close.excluded,
        firstRaw.close.entryExcluded, firstRaw.close.generation) =
      (ProtocolState.observe who whole secondRaw.close.point,
        ProtocolState.observe who whole secondRaw.close.saved, secondRaw.close.excluded,
        secondRaw.close.entryExcluded, secondRaw.close.generation) := by
  intro firstExcluded secondExcluded firstDecoded secondDecoded firstStart secondStart firstRaw
    secondRaw
  obtain ⟨decodedView, decodedExcluded, savedExcluded, attempt⟩ :=
    phase_archived_commit_prefix_view_eq_of_observed whole mode runtime leaks plan inputs horizon
      scheduler firstTrace secondTrace who index left right firstSelected secondSelected observed
      block suffix embedding inside firstEntry secondEntry entry
  have saved : ProtocolState.observe who whole firstRaw.saved =
      ProtocolState.observe who whole secondRaw.saved := by
    change ProtocolState.observe who whole
        (lift (ProtocolState.entry (block.prepend suffix) firstEntry)) =
      ProtocolState.observe who whole
        (lift (ProtocolState.entry (block.prepend suffix) secondEntry))
    rw [views.observe, views.observe]
    exact congrArg (views.view who)
      (ProtocolState.observe_entry_congr who (block.prepend suffix) _ _ entry)
  have point : ProtocolState.observe who whole firstRaw.point =
      ProtocolState.observe who whole secondRaw.point := by
    change ProtocolState.observe who whole
        (lift (block.liftPoint suffix (ProtocolState.entry suffix firstDecoded.1))) =
      ProtocolState.observe who whole
        (lift (block.liftPoint suffix (ProtocolState.entry suffix secondDecoded.1)))
    rw [tailViews.observe, tailViews.observe]
    exact congrArg (tailViews.view who)
      (ProtocolState.observe_entry_congr who suffix _ _ decodedView)
  exact CommitRecoveryState.close_observed_congr who firstRaw secondRaw point saved decodedExcluded
    savedExcluded (congrArg CommitAttemptId.generation attempt)

end Vegas
