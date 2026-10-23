/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphState
import Vegas.Compile.EventGraphHistory
import Vegas.EventGraph.SequentialLaw

/-! # Source state agreement at native reveal checkpoints

These lemmas use the existing source successor and native completion functions.
They preserve typed context references across either disclosure choice; no
source executor or native state is reconstructed or replaced. Service timing,
packet acceptance, and the information-history correspondence are separate
obligations of the adapter.
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Arbitrarily correlated initialized source states are encoded exactly in
the actual sequential runtime's initial store. -/
theorem initial_agrees (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    (initial : State L setup.context) :
    (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees initial
      (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs initial)).config.store := by
  apply ContextRefs.initial_agrees
  intro input
  rfl

theorem initial_history (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (initial : State L setup.context) : decodeHistory
    setup.program
    ((EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs initial)).config.history.map
        (setup.eventGraph.fromModeCompletion mode)) = fun _ => [] := rfl

end Vegas
