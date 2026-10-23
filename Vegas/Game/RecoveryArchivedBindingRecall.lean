/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedRetry
import Vegas.Game.RecoveryCommitPrefixWitness
import Vegas.Game.RecoveryBindingPrefix
import Vegas.Game.CommitPrefixSurvivingRecall

/-! # Actual archived own words at surviving ready source bindings -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Filling the actually ready prefix retains the surviving owner's complete
source word across every retired attempt and the current effective suffix. -/
theorem RecoverySourceCheckpoint.filled_prefix_archived_history_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) (archives : state.ArchivesBefore)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (survives : owner ∉ state.entry.excluded)
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : state.current.native.config.cut.Ready (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (valid : state.current.native.BindingInvariant) {inputs}
    (reachable : state.current.native.config.Reachable inputs)
    (retained : state.HistoryCheckpoint)
    (saved : state.entry.native.config.cut.IsPrefix state.attempt.phase) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
      state.current.native.config.store checkpoint.source).history owner =
      decodeHistory setup.program
        ((PhaseRuntimeState.archivedHistory state.retired
          state.current.native.config.history).map
            ((toEventGraph setup.program).fromModeCompletion mode)) owner := by
  have history := aligned owner survives
  have physical := decodeArchivedHistory_checkpoint_extension setup.program mode state.retired
    state.entry.native.config state.current.native.config state.attempt.phase archives saved
      retained owner
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, _origin⟩
  dsimp only at *
  change SourceProgram.Config Player L Γ at entry
  change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
    at embedding
  change SourceProgram.CommitPrefix Γ O Δ P at earlier
  change Fin (eventCount program) at selected
  change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
  subst program
  apply Eq.trans (fillCommitPrefix_history_extension_of_ready setup.program mode earlier
    (.commit name owner fresh guard next) embedding state.attempt.phase compiled.rankEq
    state.entry.native state.current.native entry valid reachable retained saved owner
    views.actionEq selected atEnd ready acting)
  rw [history]
  exact physical.symm

end Vegas
