/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ArchivedSourceRecall
import Vegas.Game.RecoveryCommitCheckpoint

/-! # Chosen retry checkpoints retain the actual archived source action word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source checkpoint's surviving own actions are read from the full physical
archive and its current effective semantic prefix. -/
def RecoverySourceCheckpoint.ArchivedRecall
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state) : Prop :=
  ∀ who, who ∉ state.entry.excluded → checkpoint.source.history who =
    decodeHistory setup.program
      ((PhaseRuntimeState.archivedHistory state.retired state.entry.native.config.history).map
        ((toEventGraph setup.program).fromModeCompletion mode)) who

end Vegas
