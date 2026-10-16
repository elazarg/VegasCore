/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryResidualUniqueness
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Game.CompiledCommitObservedRecall
import Vegas.Source.CommitRecoverySurvivingInformation
import Vegas.Game.CompiledCommitMaximality
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.ArchivePlayerObservation
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Source.CommitRecoveryOwnHistory
import Vegas.Source.CommitRecoveryClearRecall
import Vegas.Source.CommitRecoveryControl

/-! # Complete information on chosen decoded commitment continuations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


private theorem clear_of_initial_control
    (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (initial : setup.commitRecoveryControl state = 1) : setup.CommitRecoveryClear state := by
  cases trace with
  | start => trivial
  | @extend before after prior joint legal supported =>
      cases before with
      | none =>
          obtain ⟨draw, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          rfl
      | some previous =>
          have strict := setup.commitRecoveryControl_step joint legal supported
          have positive : 0 < setup.commitRecoveryControl (some previous) :=
            Nat.zero_lt_succ _
          omega

/-- The initial public address and generation force a genuine checkpoint to precede
all source instructions, so its saved source exclusion is empty. -/
theorem RecoverySourceCheckpoint.initial_clear
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : state.attempt.phase = 0) (generation : state.generation = 0) :
    setup.CommitRecoveryClear (some (CommitRecoveryState.atPoint
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        state.entry.excluded state.generation)) := by
  apply clear_of_initial_control setup checkpoint.trace
  have position := checkpoint.saved_position
  rw [phase] at position
  simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
    CommitRecoveryState.atPoint, generation, Nat.zero_mul, Nat.zero_add, position]

/-- Literal chosen commitment continuations retain the complete surviving
source information when their real native binding observations agree. -/
theorem RecoverySourceCheckpoint.commit_information_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (left : RecoverySourceCheckpoint setup mode first)
    (right : RecoverySourceCheckpoint setup mode second)
    (firstNative secondNative : EventGraphRuntime.State
      ((toEventGraph setup.program).withMode mode))
    (firstValid : firstNative.BindingInvariant) (secondValid : secondNative.BindingInvariant)
    (committing : ProtocolState.atCommit left.residual.tail
      (ProtocolState.entry left.residual.tail left.source) = true)
    (firstCompleted : match commitPhase left.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            left.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ firstNative.config.cut.completed)
    (secondCompleted : match commitPhase left.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            left.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ secondNative.config.cut.completed)
    (publicView : firstNative.publicView = secondNative.publicView) (who : Player)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who firstNative.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who secondNative.config)
    (prior : setup.commitRecoverySignals.infoOf who left.trace =
      setup.commitRecoverySignals.infoOf who right.trace)
    (leftClosed rightClosed : setup.commitRecoveryProtocol.History)
    {leftFuel rightFuel : Nat}
    (leftPath : setup.commitRecoveryProtocol.ReachesWithin leftFuel
      ⟨_, left.trace⟩ leftClosed)
    (rightPath : setup.commitRecoveryProtocol.ReachesWithin rightFuel
      ⟨_, right.trace⟩ rightClosed)
    (leftInstructions : setup.recoveryJointRecall leftClosed.trace =
      (left.commitInstructionWord firstNative).reverse ++ setup.recoveryJointRecall left.trace)
    (rightInstructions : setup.recoveryJointRecall rightClosed.trace =
      (right.commitInstructionWord secondNative).reverse ++ setup.recoveryJointRecall right.trace)
    (firstSurvives : who ∉ (setup.commitRecoveryPublic leftClosed.state).1)
    (secondSurvives : who ∉ (setup.commitRecoveryPublic rightClosed.state).1) :
    setup.commitRecoveryModel.infoOf who leftClosed.trace =
      setup.commitRecoveryModel.infoOf who rightClosed.trace := by
  have current := congrArg Prod.fst prior
  rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at current
  have privateBefore := congrArg Prod.fst current
  have publicBefore := congrArg Prod.snd current
  have firstPosition := left.saved_position
  have secondPosition := right.saved_position
  change (first.entry.excluded, first.generation, _) =
    (second.entry.excluded, second.generation, _) at publicBefore
  dsimp only [CommitRecoveryState.atPoint] at publicBefore
  rw [firstPosition, secondPosition] at publicBefore
  have phases : first.attempt.phase = second.attempt.phase :=
    congrArg (fun signal => signal.2.2) publicBefore
  have exclusions : first.entry.excluded = second.entry.excluded :=
    congrArg Prod.fst publicBefore
  have generation : first.generation = second.generation :=
    congrArg (fun signal => signal.2.1) publicBefore
  have residual := left.residual_eq_of_phase_eq right phases
  have embeddings := left.embedding_eq_of_phase_eq right phases
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord] at leftInstructions rightInstructions
  rcases left with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, leftTrace, views,
    historyAlignment, origin⟩
  rcases right with ⟨otherResidual, otherSource, otherRefs, otherRegistry, otherEmbedding,
    otherBefore, otherCompiled, otherAlignment, otherAgrees, otherGuards, otherFailures,
    otherUnique, otherRanks, otherActors, otherCommits, otherOwners, otherEndpoints,
    otherAutomatic, otherHistory, otherMemory, otherSteps, otherMenus, otherReadout,
    rightTrace, otherViews, otherHistoryAlignment, otherOrigin⟩
  change (⟨Γ, O, program, lift⟩ : ResidualProgram setup.program) = otherResidual at residual
  subst otherResidual
  have sameEmbedding : embedding = otherEmbedding := by simpa using embeddings
  subst otherEmbedding
  dsimp only at committing firstCompleted secondCompleted leftInstructions rightInstructions
  generalize decomposition : commitPhase program = segment at *
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only at firstCompleted secondCompleted leftInstructions rightInstructions
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit name owner fresh guard rest =>
        simp only [CommitPrefix.length]
        omega
  have privateView : ProtocolState.observe who setup.program
      (lift (ProtocolState.entry (block.prepend suffix) source)) =
      ProtocolState.observe who setup.program
        (lift (ProtocolState.entry (block.prepend suffix) otherSource)) :=
    Option.some.inj privateBefore
  have localView := origin.observe_reflect who _ _ privateView
  have entry := congrArg (ProtocolView.entryView who (block.prepend suffix)) localView
  simp only [ProtocolView.entryView_observe_entry] at entry
  let leftStart := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) source)) first.entry.excluded first.generation
  let rightStart := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) otherSource)) second.entry.excluded
      second.generation
  have firstCommitting : ProtocolState.atCommit setup.program leftStart.saved = true := by
    change ProtocolState.atCommit setup.program
      (lift (ProtocolState.entry (block.prepend suffix) source)) = true
    rw [origin.atCommit_lift]
    exact committing
  have secondCommitting : ProtocolState.atCommit setup.program rightStart.saved = true := by
    change ProtocolState.atCommit setup.program
      (lift (ProtocolState.entry (block.prepend suffix) otherSource)) = true
    rw [← ProtocolState.atCommit_observe setup.program _ who, ← privateView,
      ProtocolState.atCommit_observe]
    exact firstCommitting
  have firstEnd : ProtocolState.commitEnd setup.program leftStart.saved ≤
      instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (block.prepend suffix) source)) ≤ instructionCount suffix
    rw [origin.commitEnd_lift, block.commitEnd_entry_prepend suffix boundary]
  have secondEnd : ProtocolState.commitEnd setup.program rightStart.saved ≤
      instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (block.prepend suffix) otherSource)) ≤ instructionCount suffix
    rw [origin.commitEnd_lift, block.commitEnd_entry_prepend suffix boundary]
  have signals := decoded_commit_block_chosen_signal_eq setup mode who block suffix embedding
    lift origin ranks actors (fun point owner => menus owner point) steps firstNative secondNative
    firstValid secondValid source otherSource leftStart rightStart entry publicView observed
    firstCompleted secondCompleted privateView exclusions exclusions generation rfl rfl
    firstCommitting secondCommitting firstEnd secondEnd positive leftTrace rightTrace prior
    leftClosed.trace rightClosed.trace leftPath rightPath leftInstructions rightInstructions
  exact setup.commitRecovery_surviving_info_eq who leftClosed.trace rightClosed.trace
    firstSurvives secondSurvives signals

/-- An actual completed member commitment phase identifies the saved typed block
and supplies all of its native completion witnesses. -/
theorem RecoverySourceCheckpoint.completed_commit_phase
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (member : phase ∈ plan.phases) (kind : phase.kind = .commitment)
    (low : phase.low = state.attempt.phase) (who : Player)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (completed : ∀ event ∈ phase.events, event ∈ native.config.cut.completed) :
    ProtocolState.atCommit checkpoint.residual.tail
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true ∧
      (match commitPhase checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ native.config.cut.completed) := by
  have total := checkpoint.compiled.countEq
  have bounded := phase.bounded
  have nonempty := phase.nonempty
  change phase.high ≤ eventCount setup.program at bounded
  have positive : 0 < eventCount checkpoint.residual.tail := by omega
  let zero : Fin (eventCount checkpoint.residual.tail) := ⟨0, positive⟩
  have ranked : (checkpoint.embedding.event zero).val = state.attempt.phase := by
    simpa only [zero, Nat.add_zero] using checkpoint.compiled.rankEq zero
  have headBinding := phase.fields (checkpoint.embedding.event zero) (by omega) (by omega)
  rw [kind] at headBinding
  obtain ⟨owner, payload, layout⟩ := headBinding
  change outputLayout setup.program (checkpoint.embedding.event zero) = .binding owner payload
    at layout
  have decoded := ProtocolViewSuffix.decode_entry setup.program checkpoint.residual.tail
    checkpoint.refs checkpoint.embedding checkpoint.residual.lift checkpoint.views positive who
    checkpoint.source state.entry.native.config.store checkpoint.agrees
  have headCommit := decodeEventView?_atCommit setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who (checkpoint.embedding.event zero)
    ((toEventGraph setup.program).playerStore who state.entry.native.config.store)
    (checkpoint.source.history who) _ decoded owner payload layout
  have committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true := by
    simpa only [ProtocolState.atCommit_observe, checkpoint.atCommit] using headCommit
  refine ⟨committing, ?_⟩
  obtain ⟨prior, remaining, installed⟩ := List.mem_iff_append.mp member
  have suffixProof : phase :: remaining <:+ plan.phases := ⟨prior, installed.symm⟩
  obtain ⟨adjacent, last, maximalTail⟩ := plan.suffix_geometry maximal _ suffixProof
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, trace, views,
    historyAlignment, origin⟩
  dsimp only at ⊢
  generalize decomposition : commitPhase program = segment
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only
  have blockPositive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit name owner fresh guard rest => simp only [CommitPrefix.length]; omega
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix
    embedding compiled blockPositive boundary phase remaining adjacent last maximalTail low
  intro index earlier
  apply completed
  rw [phaseEq, RuntimePhase.mem_events]
  have rank := compiled.rankEq index
  change state.attempt.phase ≤ (embedding.event index).val ∧
    (embedding.event index).val < state.attempt.phase + block.length
  omega

/-- Actual indistinguishable archived attempts have equal complete chosen AUX
information after their decoded commitment continuations. All native validity,
completion and survival premises come from the real current histories. -/
theorem phase_archived_chosen_information_eq_of_observed
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : Interaction.MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player) (survives : who ∉ first.execution.application.current.excluded)
    (index : Nat) (firstRecord secondRecord : RetiredCommitAttempt
      ((toEventGraph setup.program).withMode mode))
    (firstSelected : first.execution.application.retired[index]? = some firstRecord)
    (secondSelected : second.execution.application.retired[index]? = some secondRecord)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who)
    {firstSource secondSource : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (left : RecoverySourceCheckpoint setup mode firstSource)
    (right : RecoverySourceCheckpoint setup mode secondSource)
    (firstAttempt : firstSource.attempt = firstRecord.attempt)
    (firstFinal : RecoverySourceCheckpoint setup mode first.execution.application)
    (secondFinal : RecoverySourceCheckpoint setup mode second.execution.application)
    (prior : setup.commitRecoverySignals.infoOf who left.trace =
      setup.commitRecoverySignals.infoOf who right.trace)
    (leftClosed rightClosed : setup.commitRecoveryProtocol.History)
    {leftFuel rightFuel leftLater rightLater : Nat}
    (leftPath : setup.commitRecoveryProtocol.ReachesWithin leftFuel
      ⟨_, left.trace⟩ leftClosed)
    (rightPath : setup.commitRecoveryProtocol.ReachesWithin rightFuel
      ⟨_, right.trace⟩ rightClosed)
    (leftFollowing : setup.commitRecoveryProtocol.ReachesWithin leftLater leftClosed
      ⟨_, firstFinal.trace⟩)
    (rightFollowing : setup.commitRecoveryProtocol.ReachesWithin rightLater rightClosed
      ⟨_, secondFinal.trace⟩)
    (leftInstructions : setup.recoveryJointRecall leftClosed.trace =
      (left.commitInstructionWord firstRecord.state).reverse ++
        setup.recoveryJointRecall left.trace)
    (rightInstructions : setup.recoveryJointRecall rightClosed.trace =
      (right.commitInstructionWord secondRecord.state).reverse ++
        setup.recoveryJointRecall right.trace) :
    setup.commitRecoveryModel.infoOf who leftClosed.trace =
      setup.commitRecoveryModel.infoOf who rightClosed.trace := by
  have archives := congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
    view.application.2.retired) observed
  change first.execution.application.retired.map
      (fun record => (record.attempt, record.state.publicView)) =
    second.execution.application.retired.map
      (fun record => (record.attempt, record.state.publicView)) at archives
  have selectedPublic := congrArg (fun records => records[index]?) archives
  simp only [List.getElem?_map, firstSelected, secondSelected, Option.map_some] at selectedPublic
  have samePublic := congrArg Prod.snd (Option.some.inj selectedPublic)
  have native := phaseArchivedPlayerObservations_eq_of_observed runtime leaks plan inputs horizon
    scheduler firstTrace secondTrace who observed
  have selectedNative := congrArg (fun records => records[index]?) native
  simp only [List.getElem?_map, firstSelected, secondSelected, Option.map_some] at selectedNative
  have sameNative := congrArg Prod.snd (Option.some.inj selectedNative)
  have firstMember := List.mem_of_getElem? firstSelected
  have secondMember := List.mem_of_getElem? secondSelected
  have firstValid := (phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler
    firstTrace firstRecord firstMember).1
  have secondValid := (phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler
    secondTrace secondRecord secondMember).1
  obtain ⟨phase, member, low, kind, completed, _receipts, _failures⟩ :=
    (phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler firstTrace).archives
      firstRecord firstMember
  have phaseLow : phase.low = firstSource.attempt.phase :=
    low.symm.trans (congrArg CommitAttemptId.phase firstAttempt).symm
  obtain ⟨committing, firstCompleted⟩ := left.completed_commit_phase plan maximal phase member
    kind phaseLow who firstRecord.state completed
  have publicOrder := congrArg (fun view => view.observation.completionOrder) samePublic
  have completionTransfer : ∀ event, event ∈ firstRecord.state.config.cut.completed →
      event ∈ secondRecord.state.config.cut.completed := by
    intro event present
    have history := (firstRecord.state.config.history_exact event).mpr present
    change event ∈ firstRecord.state.publicView.observation.completionOrder at history
    rw [publicOrder] at history
    exact (secondRecord.state.config.history_exact event).mp history
  have secondCompleted : match commitPhase left.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            left.embedding
        ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
          embedding.event index ∈ secondRecord.state.config.cut.completed := by
    generalize decomposition : commitPhase left.residual.tail = segment at firstCompleted ⊢
    rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
    intro event earlier
    exact completionTransfer _ (firstCompleted event earlier)
  have excludedSubset {fuel : Nat} {before after : setup.commitRecoveryProtocol.History}
      (path : setup.commitRecoveryProtocol.ReachesWithin fuel before after) :
      (setup.commitRecoveryPublic before.state).1 ⊆
        (setup.commitRecoveryPublic after.state).1 := by
    induction path with
    | refl => exact Finset.Subset.refl _
    | step joint legal supported _rest ih =>
        exact (setup.commitRecovery_step_excluded_subset joint legal supported).trans ih
  have firstInherited := excludedSubset leftFollowing
  have secondInherited := excludedSubset rightFollowing
  change (setup.commitRecoveryPublic leftClosed.state).1 ⊆
    first.execution.application.entry.excluded at firstInherited
  change (setup.commitRecoveryPublic rightClosed.state).1 ⊆
    second.execution.application.entry.excluded at secondInherited
  have firstCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    firstTrace
  have secondCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    secondTrace
  have sameExcluded : first.execution.application.current.excluded =
      second.execution.application.current.excluded :=
    congrArg (fun view : (phaseApplication runtime leaks).PlayerView =>
      view.application.2.excluded) observed
  have rightSurvives : who ∉ second.execution.application.current.excluded := by
    rwa [← sameExcluded]
  have leftActive : who ∉ (setup.commitRecoveryPublic leftClosed.state).1 :=
    fun inactive => survives (firstCoverage.inherited (firstInherited inactive))
  have rightActive : who ∉ (setup.commitRecoveryPublic rightClosed.state).1 :=
    fun inactive => rightSurvives (secondCoverage.inherited (secondInherited inactive))
  exact left.commit_information_eq right firstRecord.state secondRecord.state firstValid secondValid
    committing firstCompleted secondCompleted samePublic who sameNative prior leftClosed rightClosed
    leftPath rightPath leftInstructions rightInstructions leftActive rightActive

end Vegas
