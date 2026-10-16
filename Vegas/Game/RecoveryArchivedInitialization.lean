/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryArchivedRetry
import Vegas.Game.RecoveryInitialCheckpoint

/-! # The single supported setup draw initializes the complete source own word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem archivedRecall_cast {setup : Setup (Player := Player) (L := L)}
    {mode : ExecutionMode}
    {state other : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (same : state = other) (checkpoint : RecoverySourceCheckpoint setup mode state)
    (aligned : checkpoint.ArchivedRecall) :
    (cast (congrArg (RecoverySourceCheckpoint setup mode) same) checkpoint).ArchivedRecall := by
  cases same
  exact aligned

/-- The chosen actual initial checkpoint has exactly the original empty own
word, with no retired attempt or independently chosen initial source state. -/
theorem RecoverySourceCheckpoint.initialized_archived
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    (RecoverySourceCheckpoint.initialized setup mode plan initial supported).ArchivedRecall := by
  unfold RecoverySourceCheckpoint.initialized
  apply archivedRecall_cast (phaseInitial_eq_raw plan (encodeInputs initial)).symm
    (RecoverySourceCheckpoint.initial setup mode plan initial supported)
  intro who _active
  rfl

end Vegas
