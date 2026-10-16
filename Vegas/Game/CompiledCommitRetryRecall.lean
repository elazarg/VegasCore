/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitBlockRecall
import Vegas.Source.CommitRecoveryBlockCloseLift
import Vegas.Source.CommitRecoverySurvivingInformation

/-! # Genuine paired source recall at the exact restored retry checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem source_info_cast (setup : Setup (Player := Player) (L := L)) (who : Player)
    {first second : setup.commitRecoveryProtocol.State} (same : first = second)
    (trace : setup.commitRecoveryProtocol.Trace first) :
    setup.commitRecoverySignals.infoOf who (same ▸ trace) =
      setup.commitRecoverySignals.infoOf who trace := by
  cases same
  rfl

private theorem source_reaches_cast (setup : Setup (Player := Player) (L := L))
    {first second : setup.commitRecoveryProtocol.State} (same : first = second)
    (trace : setup.commitRecoveryProtocol.Trace first)
    {fuel : Nat} {start : setup.commitRecoveryProtocol.History}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel start ⟨first, trace⟩) :
    setup.commitRecoveryProtocol.ReachesWithin fuel start ⟨second, same ▸ trace⟩ := by
  cases same
  exact reached

/-- Completed native attempts with the same observations extend their actual
prior source recalls to the exact restored retry points. The original missing
scan, completed action words and new generation are retained. -/
theorem decoded_commit_retry_source_traces
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode) (who : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (boundary : IsCommitBoundary suffix)
    (positive : 0 < block.length)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (ranks : ∀ point, ProtocolState.remaining setup.program (lift point) =
      ProtocolState.remaining (block.prepend suffix) point)
    (actors : ∀ point, ProtocolState.actor setup.program (lift point) =
      ProtocolState.actor (block.prepend suffix) point)
    (menus : ∀ point player, ProtocolView.recoveryAvailable player setup.program
      (ProtocolState.observe player setup.program (lift point)) =
      ProtocolView.recoveryAvailable player (block.prepend suffix)
        (ProtocolState.observe player (block.prepend suffix) point))
    (steps : ∀ point owners joint, ProtocolState.recoveryStep setup.program (lift point) owners
        joint =
      (ProtocolState.recoveryStep (block.prepend suffix) point owners joint).map
        (fun result => (lift result.1, result.2)))
    (commits : ∀ point, ProtocolState.atCommit setup.program (lift point) =
      ProtocolState.atCommit (block.prepend suffix) point)
    (owners : ∀ point, ProtocolState.commitOwners setup.program (lift point) =
      ProtocolState.commitOwners (block.prepend suffix) point)
    (endpoints : ∀ point, ProtocolState.commitEnd setup.program (lift point) =
      ProtocolState.commitEnd (block.prepend suffix) point)
    (histories : ∀ point, ProtocolState.history setup.program (lift point) =
      ProtocolState.history (block.prepend suffix) point)
    (memories : ∀ point past, lift (ProtocolState.withHistory (block.prepend suffix) point past) =
      ProtocolState.withHistory setup.program (lift point) past)
    (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (entry : firstEntry.view who = secondEntry.view who)
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
    (firstCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → embedding.event index ∈ first.config.cut.completed)
    (secondCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
      index.val < block.length → embedding.event index ∈ second.config.cut.completed)
    (excluded : Finset Player) (generation : Nat)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) firstEntry)) excluded generation)))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (block.prepend suffix) secondEntry)) excluded generation)))
    (prior : setup.commitRecoverySignals.infoOf who firstTrace =
      setup.commitRecoverySignals.infoOf who secondTrace)
    (failed : ((decodeCommitAttempt setup.program mode block suffix embedding first firstEntry
      excluded).2.1 \ excluded).Nonempty)
    (survives : (block.owners \ (decodeCommitAttempt setup.program mode block suffix embedding
      first firstEntry excluded).2.1).Nonempty)
    (active : who ∉ (decodeCommitAttempt setup.program mode block suffix embedding first
      firstEntry excluded).2.1) :
    let leftDecoded := decodeCommitAttempt setup.program mode block suffix embedding first
      firstEntry excluded
    let rightDecoded := decodeCommitAttempt setup.program mode block suffix embedding second
      secondEntry excluded
    ∃ (leftTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (lift (ProtocolState.entry (block.prepend suffix)
            { firstEntry with history := leftDecoded.1.history }))
          leftDecoded.2.1 (generation + 1))))
      (rightTrace : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (lift (ProtocolState.entry (block.prepend suffix)
            { secondEntry with history := rightDecoded.1.history }))
          rightDecoded.2.1 (generation + 1)))),
      ∃ (leftFuel rightFuel : Nat),
      setup.commitRecoveryProtocol.ReachesWithin leftFuel
        ⟨_, firstTrace⟩ ⟨_, leftTrace⟩ ∧
      setup.commitRecoveryProtocol.ReachesWithin rightFuel
        ⟨_, secondTrace⟩ ⟨_, rightTrace⟩ ∧
      setup.commitRecoveryModel.infoOf who leftTrace =
        setup.commitRecoveryModel.infoOf who rightTrace := by
  intro leftDecoded rightDecoded
  let left := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) firstEntry)) excluded generation
  let right := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) secondEntry)) excluded generation
  let leftRaw := left.install
    (lift (block.liftPoint suffix (ProtocolState.entry suffix leftDecoded.1)), leftDecoded.2.1)
    (fun _ member => leftDecoded.2.2.excluded_subset member)
  let rightRaw := right.install
    (lift (block.liftPoint suffix (ProtocolState.entry suffix rightDecoded.1)), rightDecoded.2.1)
    (fun _ member => rightDecoded.2.2.excluded_subset member)
  have current := congrArg Prod.fst prior
  rw [setup.commitRecoverySignals_current who firstTrace,
    setup.commitRecoverySignals_current who secondTrace] at current
  have saved : ProtocolState.observe who setup.program left.saved =
      ProtocolState.observe who setup.program right.saved := by
    exact Option.some.inj (congrArg Prod.fst current)
  have committing (config : SourceProgram.Config Player L Γ) :
      ProtocolState.atCommit (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) config) = true := by
    cases block with
    | nil => cases positive
    | commit => rfl
  have firstCommitting := (commits _).trans (committing firstEntry)
  have secondCommitting := (commits _).trans (committing secondEntry)
  have firstEndpoint : ProtocolState.commitEnd setup.program left.saved ≤ instructionCount suffix :=
    ((endpoints _).trans (block.commitEnd_entry_prepend suffix boundary firstEntry)).le
  have secondEndpoint : ProtocolState.commitEnd setup.program right.saved ≤
      instructionCount suffix :=
    ((endpoints _).trans (block.commitEnd_entry_prepend suffix boundary secondEntry)).le
  obtain ⟨leftTrace, rightTrace, leftFuel, rightFuel, leftPath, rightPath, same,
    _firstInstructions, _secondInstructions⟩ :=
    decoded_commit_block_source_traces setup mode who block
    suffix embedding lift origin ranks actors menus steps first second firstValid secondValid
    firstEntry secondEntry left right entry publicView observed firstCompleted secondCompleted
    saved rfl rfl rfl rfl rfl firstCommitting secondCommitting firstEndpoint secondEndpoint positive
    firstTrace secondTrace prior
  have reachedSignal := congrArg Prod.fst same
  rw [setup.commitRecoverySignals_current who leftTrace,
    setup.commitRecoverySignals_current who rightTrace] at reachedSignal
  have afterExcluded := congrArg (fun signal => signal.2.1) reachedSignal
  change leftRaw.close.excluded = rightRaw.close.excluded at afterExcluded
  have actualExcluded : leftDecoded.2.1 = rightDecoded.2.1 := by
    simpa only [CommitRecoveryState.close_excluded, leftRaw, rightRaw,
      CommitRecoveryState.install] using afterExcluded
  have firstFailed : leftDecoded.2.2.failedOwners.Nonempty := by
    rw [← leftDecoded.2.2.newly_excluded]
    exact failed
  have secondFailed : rightDecoded.2.2.failedOwners.Nonempty := by
    rw [← rightDecoded.2.2.newly_excluded, ← actualExcluded]
    exact failed
  have secondSurvives : (block.owners \ rightDecoded.2.1).Nonempty := by
    rw [← actualExcluded]
    exact survives
  have leftClosed := leftDecoded.2.2.close_retry_lift setup.program suffix boundary positive
    generation lift ranks commits owners endpoints histories memories firstFailed survives
  have rightClosed := rightDecoded.2.2.close_retry_lift setup.program suffix boundary positive
    generation lift ranks commits owners endpoints histories memories secondFailed secondSurvives
  have leftState := congrArg some leftClosed
  have rightState := congrArg some rightClosed
  refine ⟨leftState ▸ leftTrace, rightState ▸ rightTrace, leftFuel, rightFuel,
    source_reaches_cast setup leftState leftTrace leftPath,
    source_reaches_cast setup rightState rightTrace rightPath, ?_⟩
  apply setup.commitRecovery_surviving_info_eq who
  · simpa only [SourceProgram.Setup.commitRecoveryPublic, CommitRecoveryState.atPoint] using active
  · simpa only [SourceProgram.Setup.commitRecoveryPublic, CommitRecoveryState.atPoint,
      ← actualExcluded]
      using active
  · rw [source_info_cast, source_info_cast]
    exact same

end Vegas
