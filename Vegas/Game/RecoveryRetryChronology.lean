/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryChosenCommitControl
import Vegas.Source.CommitRecoverySavedProgress

/-! # The decoded retry close is the literal subsequent chosen source checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A next-attempt checkpoint at the same physical phase is the genuine decoded
retry close in the same final chosen source trace. An exhausted source close
cannot be spliced to that checkpoint, because its saved frontier is later. -/
theorem RecoverySourceCheckpoint.retry_chosen_history_eq
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state nextState : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (nextCheckpoint : RecoverySourceCheckpoint setup mode nextState)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : nextState.attempt.phase = state.attempt.phase)
    (generation : nextState.generation = state.generation + 1)
    (closed target : setup.commitRecoveryProtocol.History)
    {fuel later nextLater : Nat}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (following : setup.commitRecoveryProtocol.ReachesWithin later closed target)
    (nextFollowing : setup.commitRecoveryProtocol.ReachesWithin nextLater
      ⟨_, nextCheckpoint.trace⟩ target)
    (who : Player) (survives : who ∉ (setup.commitRecoveryPublic target.state).1) :
    closed = ⟨_, nextCheckpoint.trace⟩ := by
  obtain ⟨after, afterState, atPoint, retry | advanced⟩ :=
    checkpoint.chosen_commit_control native committing closed reached instructions
  · have sameControl : setup.commitRecoveryControl closed.state =
        setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
          (nextCheckpoint.residual.lift
            (ProtocolState.entry nextCheckpoint.residual.tail nextCheckpoint.source))
              nextState.entry.excluded nextState.generation)) := by
      rw [afterState]
      simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
        CommitRecoveryState.atPoint, retry.1, ← atPoint, retry.2,
        checkpoint.saved_position, nextCheckpoint.saved_position, generation, phase]
    exact setup.commitRecovery_ancestor_eq_of_control_eq following nextFollowing sameControl
  · have beforeBound := ProtocolState.remaining_le_instructionCount setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
    have nextBound := ProtocolState.remaining_le_instructionCount setup.program
      (nextCheckpoint.residual.lift
        (ProtocolState.entry nextCheckpoint.residual.tail nextCheckpoint.source))
    have endBound := ProtocolState.commitEnd_le_remaining setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
    have beforePosition := checkpoint.saved_position
    have nextPosition := nextCheckpoint.saved_position
    have sameRemaining : ProtocolState.remaining setup.program
        (nextCheckpoint.residual.lift
          (ProtocolState.entry nextCheckpoint.residual.tail nextCheckpoint.source)) =
        ProtocolState.remaining setup.program (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
      rw [phase] at nextPosition
      omega
    have ordered : setup.commitRecoveryControl closed.state ≤
        setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
          (nextCheckpoint.residual.lift
            (ProtocolState.entry nextCheckpoint.residual.tail nextCheckpoint.source))
              nextState.entry.excluded nextState.generation)) := by
      rw [afterState]
      simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
        CommitRecoveryState.atPoint, advanced.1, ← atPoint, advanced.2, generation,
        Nat.add_mul, Nat.one_mul]
      omega
    have path := setup.commitRecovery_ancestor_of_control_le following nextFollowing ordered
    have inherited : ∀ {steps : Nat} {first last : setup.commitRecoveryProtocol.History},
        setup.commitRecoveryProtocol.ReachesWithin steps first last →
          (setup.commitRecoveryPublic first.state).1 ⊆
            (setup.commitRecoveryPublic last.state).1 := by
      intro steps first last carried
      induction carried with
      | refl => exact Finset.Subset.refl _
      | step joint legal supported _rest ih =>
          exact (setup.commitRecovery_step_excluded_subset joint legal supported).trans ih
    have active : who ∉ nextState.entry.excluded := fun excluded =>
      survives (inherited nextFollowing excluded)
    have monotone := setup.commitRecovery_saved_remaining_le_of_prefix who closed.trace
      nextCheckpoint.trace path.tracePrefix active
    rw [afterState] at monotone
    change ProtocolState.remaining setup.program
        (nextCheckpoint.residual.lift
          (ProtocolState.entry nextCheckpoint.residual.tail nextCheckpoint.source)) ≤
      ProtocolState.remaining setup.program after.saved at monotone
    rw [sameRemaining, advanced.2] at monotone
    have bound := ProtocolState.commitEnd_lt_remaining setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      ((checkpoint.atCommit _).trans committing)
    omega

end Vegas
