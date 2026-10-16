/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySurvivingBindingSource
import Vegas.Source.CommitAttemptRanks

/-! # Saved source observations recovered at the public phase rank -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem entryView_observe_cast
    {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (point : ProtocolState first) :
    ProtocolView.entryView who second
        (ProtocolState.observe who second (cast (congrArg ProtocolState same) point)) =
      ProtocolView.entryView who first (ProtocolState.observe who first point) := by
  cases same
  rfl

/-- The actual saved source view is the existing rank readout of a surviving
owner's later attempt view. Foreign exclusions and actual missing flags are
retained by the typed attempt; no physical current exclusion set is substituted. -/
theorem RecoverySourceCheckpoint.attempt_saved_rank
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : earlier.prepend suffix = checkpoint.residual.tail)
    {excluded after : Finset Player} {finished : SourceProgram.Config Player L Δ}
    (attempt : earlier.Attempt checkpoint.source excluded finished after)
    (who : Player) (survives : who ∉ after) :
    ProtocolView.atRank who setup.program state.attempt.phase
        (ProtocolState.observe who setup.program (checkpoint.residual.lift
          (cast (congrArg ProtocolState reconstruct)
            (earlier.liftPoint suffix (ProtocolState.entry suffix finished))))) =
      some (ProtocolState.observe who setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) := by
  let point := cast (congrArg ProtocolState reconstruct)
    (earlier.liftPoint suffix (ProtocolState.entry suffix finished))
  have localEntry : ProtocolView.entryView who checkpoint.residual.tail
      (ProtocolState.observe who checkpoint.residual.tail point) = checkpoint.source.view who := by
    exact (entryView_observe_cast who reconstruct _).trans (attempt.entryView suffix who survives)
  have localRank := ProtocolView.atRank_zero_of_entryView who checkpoint.residual.tail
    (ProtocolState.observe who checkpoint.residual.tail point) checkpoint.source localEntry
  have lifted := checkpoint.origin.atRank_lift who
    (ProtocolState.entry checkpoint.residual.tail checkpoint.source) point 0 localRank
  have address := checkpoint.saved_position
  rw [checkpoint.remaining, ProtocolState.remaining_entry] at address
  simpa only [Nat.add_zero, address] using lifted

/-- The existing virtual fill also retains the exact saved focal source view
under rank readout. This is a view identity and does not identify the fill's
foreign omission flags with a partly completed physical attempt. -/
theorem RecoverySourceCheckpoint.filled_prefix_saved_rank
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : earlier.prepend suffix = checkpoint.residual.tail)
    (store : EventGraph.Store (graphLayout setup.program)) (who : Player) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier suffix embedding store checkpoint.source
    ProtocolView.atRank who setup.program state.attempt.phase
        (ProtocolState.observe who setup.program (checkpoint.residual.lift
          (cast (congrArg ProtocolState reconstruct)
            (earlier.liftPoint suffix (ProtocolState.entry suffix filled))))) =
      some (ProtocolState.observe who setup.program (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) := by
  intro embedding filled
  exact checkpoint.attempt_saved_rank earlier suffix reconstruct
    (fillCommitPrefix_attempt setup.program earlier suffix embedding store checkpoint.source) who
      (Finset.notMem_empty who)

end Vegas
