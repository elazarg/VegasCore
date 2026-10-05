/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRuntime
import Vegas.Compile.EventGraphState
import Vegas.Compile.EventGraphHistory
import Vegas.EventGraph.SequentialLaw

/-! # Initialized source observations
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Arbitrarily correlated initialized source states are encoded exactly in
the actual sequential runtime's initial store. -/
theorem initial_agrees (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees initial
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config.store := by
  apply ContextRefs.initial_agrees
  intro input
  rfl

theorem initial_history (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    decodeHistory setup.program
      ((EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = fun _ => [] := rfl

end Vegas
