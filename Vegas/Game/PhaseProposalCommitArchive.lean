/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryChosenCommitControl

/-! # Decoded physical commitment attempts disclose no opening proposals -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The actual decoded attempt word remains inside its saved maximal
commitment window, including its final retry or exhausted close. -/
theorem RecoverySourceCheckpoint.commit_instruction_word_window
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode)) :
    (checkpoint.commitInstructionWord native).length +
        ProtocolState.commitEnd setup.program
          (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail
            checkpoint.source)) ≤
      ProtocolState.remaining setup.program
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail
          checkpoint.source)) := by
  rw [checkpoint.commitEnd, checkpoint.remaining]
  unfold RecoverySourceCheckpoint.commitInstructionWord
  generalize decomposition : commitPhase checkpoint.residual.tail = segment
  rcases segment with ⟨Δ, O, suffix, block, reconstruct, _boundary⟩
  dsimp only
  rw [CommitPrefix.Attempt.joints_length, ← reconstruct]
  exact block.length_le_commit_window suffix checkpoint.source

/-- Labeling the SAME chosen commitment continuation cannot manufacture a
proposal. All previous consumed publication proposals remain in the archive. -/
theorem RecoverySourceCheckpoint.commit_proposal_archive
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) (who : Player) :
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace labels
          closed.trace)) =
      setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace labels
          checkpoint.trace)) := by
  let first := CommitRecoveryState.atPoint
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation
  have atCommit : ProtocolState.atCommit setup.program first.point = true :=
    (checkpoint.atCommit _).trans committing
  have length := congrArg List.length instructions
  simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse] at length
  have window := checkpoint.commit_instruction_word_window native
  apply setup.proposalRecoveryArchive_eq_of_commit_window who first
    (setup.proposalRecoveryLiftTrace labels checkpoint.trace) atCommit
    (setup.proposalRecoveryLiftTrace labels closed.trace)
    (setup.proposalRecoveryLiftTrace_prefix labels reached.tracePrefix)
  simp only [setup.proposalRecoveryLiftTrace_length]
  dsimp only [first, CommitRecoveryState.atPoint]
  omega

end Vegas
