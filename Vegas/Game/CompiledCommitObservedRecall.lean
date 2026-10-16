/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitBlockRecall
import Vegas.Source.CommitRecoveryCommitUnique
import Vegas.Source.CommitRecoveryCommitWindow

/-! # Genuine chosen commitment histories have the decoded physical signal transcript -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Chosen genuine source continuations carrying the actual decoded original
instructions have equal complete signal recall on physically indistinguishable
completed binding blocks. Final retries and exhausted closes are retained. -/
theorem decoded_commit_block_chosen_signal_eq
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode) (who : Player)
    (remember : Bool)
    {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
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
      (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
      (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
      (firstEntry secondEntry : SourceProgram.Config Player L Γ)
      (left right : CommitRecoveryState setup.program)
      (entry : DecisionView.historyProjection remember (firstEntry.view who) =
        DecisionView.historyProjection remember (secondEntry.view who))
      (publicView : first.publicView = second.publicView)
      (observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
        ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
      (firstCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length → embedding.event index ∈ first.config.cut.completed)
      (secondCompleted : ∀ index : Fin (eventCount (block.prepend suffix)),
        index.val < block.length → embedding.event index ∈ second.config.cut.completed)
      (saved : ProtocolView.historyProjection who setup.program remember
          (ProtocolState.observe who setup.program left.saved) =
        ProtocolView.historyProjection who setup.program remember
          (ProtocolState.observe who setup.program right.saved))
      (excluded : left.excluded = right.excluded)
      (entryExcluded : left.entryExcluded = right.entryExcluded)
      (generation : left.generation = right.generation)
      (firstAtEntry : left.point = lift (ProtocolState.entry (block.prepend suffix) firstEntry))
      (secondAtEntry : right.point = lift (ProtocolState.entry (block.prepend suffix) secondEntry))
      (firstCommitting : ProtocolState.atCommit setup.program left.saved = true)
      (secondCommitting : ProtocolState.atCommit setup.program right.saved = true)
      (firstEndpoint : ProtocolState.commitEnd setup.program left.saved ≤ instructionCount suffix)
      (secondEndpoint : ProtocolState.commitEnd setup.program right.saved ≤
        instructionCount suffix)
      (positive : 0 < block.length)
      (firstTrace : setup.commitRecoveryProtocol.Trace (some left))
      (secondTrace : setup.commitRecoveryProtocol.Trace (some right))
      (prior : setup.commitRecoveryProjectedRecall who remember observe
          (setup.commitRecoverySignals.infoOf who firstTrace) =
        setup.commitRecoveryProjectedRecall who remember observe
          (setup.commitRecoverySignals.infoOf who secondTrace))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    {leftFuel rightFuel : Nat}
    (leftChosen : setup.commitRecoveryProtocol.Trace leftState)
    (rightChosen : setup.commitRecoveryProtocol.Trace rightState)
    (leftReached : setup.commitRecoveryProtocol.ReachesWithin leftFuel
      ⟨some left, firstTrace⟩ ⟨leftState, leftChosen⟩)
    (rightReached : setup.commitRecoveryProtocol.ReachesWithin rightFuel
      ⟨some right, secondTrace⟩ ⟨rightState, rightChosen⟩)
    (leftInstructions : setup.recoveryJointRecall leftChosen =
      (decodeCommitAttempt setup.program mode block suffix embedding first firstEntry
        left.excluded).2.2.joints.reverse ++ setup.recoveryJointRecall firstTrace)
    (rightInstructions : setup.recoveryJointRecall rightChosen =
      (decodeCommitAttempt setup.program mode block suffix embedding second secondEntry
        right.excluded).2.2.joints.reverse ++ setup.recoveryJointRecall secondTrace) :
    setup.commitRecoveryHistorySignal who remember
          (setup.commitRecoverySignals.infoOf who leftChosen).1 =
        setup.commitRecoveryHistorySignal who remember
          (setup.commitRecoverySignals.infoOf who rightChosen).1 ∧
      setup.commitRecoveryProjectedRecall who remember observe
          (setup.commitRecoverySignals.infoOf who leftChosen) =
        setup.commitRecoveryProjectedRecall who remember observe
          (setup.commitRecoverySignals.infoOf who rightChosen) := by
  obtain ⟨leftPaired, rightPaired, leftPairedFuel, rightPairedFuel, leftPairedReached,
    rightPairedReached, pairedCurrent, pairedSignals, leftPairedInstructions,
    rightPairedInstructions⟩ :=
    decoded_commit_block_source_traces setup mode who remember observe block suffix embedding
      lift origin
      ranks
      actors menus steps first second firstValid secondValid firstEntry secondEntry left right
      entry publicView observed firstCompleted secondCompleted saved excluded entryExcluded
      generation firstAtEntry secondAtEntry firstCommitting secondCommitting firstEndpoint
      secondEndpoint positive firstTrace secondTrace prior
  have leftCommit : ProtocolState.atCommit setup.program left.point = true := by
    rw [firstAtEntry, origin.atCommit_lift]
    cases block with
    | nil => exact (Nat.not_lt_zero _ positive).elim
    | commit name owner fresh guard rest => rfl
  have rightCommit : ProtocolState.atCommit setup.program right.point = true := by
    rw [secondAtEntry, origin.atCommit_lift]
    cases block with
    | nil => exact (Nat.not_lt_zero _ positive).elim
    | commit name owner fresh guard rest => rfl
  have leftLength := congrArg List.length leftInstructions
  simp only [List.length_append, List.length_reverse, CommitPrefix.Attempt.joints_length,
    setup.recoveryJointRecall_length] at leftLength
  have rightLength := congrArg List.length rightInstructions
  simp only [List.length_append, List.length_reverse, CommitPrefix.Attempt.joints_length,
    setup.recoveryJointRecall_length] at rightLength
  have leftWindow := block.length_le_commit_window suffix firstEntry
  rw [← origin.commitEnd_lift, ← ranks, ← firstAtEntry] at leftWindow
  have rightWindow := block.length_le_commit_window suffix secondEntry
  rw [← origin.commitEnd_lift, ← ranks, ← secondAtEntry] at rightWindow
  have leftSame := setup.commitRecovery_history_eq_of_commit_window left firstTrace leftCommit
    leftChosen leftPaired leftReached leftPairedReached
    (leftInstructions.trans leftPairedInstructions.symm) (by omega)
  have rightSame := setup.commitRecovery_history_eq_of_commit_window right secondTrace rightCommit
    rightChosen rightPaired rightReached rightPairedReached
    (rightInstructions.trans rightPairedInstructions.symm) (by omega)
  have leftSignals := congrArg
    (fun history : setup.commitRecoveryProtocol.History =>
      setup.commitRecoverySignals.infoOf who history.trace) leftSame
  have rightSignals := congrArg
    (fun history : setup.commitRecoveryProtocol.History =>
      setup.commitRecoverySignals.infoOf who history.trace) rightSame
  constructor
  · exact (congrArg (fun signal => setup.commitRecoveryHistorySignal who remember signal.1)
      leftSignals).trans
      (pairedCurrent.trans (congrArg
        (fun signal => setup.commitRecoveryHistorySignal who remember signal.1)
        rightSignals).symm)
  · exact (congrArg (setup.commitRecoveryProjectedRecall who remember observe) leftSignals).trans
      (pairedSignals.trans
        (congrArg (setup.commitRecoveryProjectedRecall who remember observe) rightSignals).symm)

end Vegas
