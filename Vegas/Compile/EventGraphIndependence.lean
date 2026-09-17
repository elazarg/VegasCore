/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphPolicy
import Vegas.EventGraph.NormalizedPolicy

/-! # Compiled policy independence from foreign hidden completions

The actual graph observation includes completion order. Compiled source
policies use its typed source view and own-action history, and therefore make
the same decision when a foreign hidden event completes first. This is a
local policy law, not whole-run scheduler invariance or deviation extraction.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Source policy compilation already ignores chronological scheduling
metadata. Graph-level normalization therefore leaves the actual compiled
profile unchanged, on every observation rather than only reachable ones. -/
theorem normalizeProfile_compileEventProfile
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program) :
    (toEventGraph program).normalizeProfile
        (compileEventProfile program profile) =
      compileEventProfile program profile := rfl

/-- Advancing an event hidden from the player and absent from its own-action
history leaves the player's actual compiled decision kernel unchanged. -/
theorem compileEventPolicy_complete_hidden
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (who : Player)
    (policy : BehavioralPolicy who program)
    (config : (toEventGraph program).Config)
    (completed event : Fin (eventCount program))
    (ready : config.cut.Ready completed)
    (action : (toEventGraph program).Action completed)
    (value : (outputLayout program completed).Value)
    (hidden : ¬ (toEventGraph program).fieldVisibleTo who (.inr completed))
    (notOwned : (toEventGraph program).actor? completed ≠ some who)
    (actor : (toEventGraph program).actor? event = some who) :
    compileEventPolicy program who policy event actor
        ((toEventGraph program).playerObserve who
          (config.complete completed ready action value)) =
      compileEventPolicy program who policy event actor
        ((toEventGraph program).playerObserve who config) := by
  unfold compileEventPolicy Vegas.EventGraph.playerObserve
  dsimp only
  rw [(toEventGraph program).playerStore_complete_of_hidden who config
      completed ready action value hidden,
    (toEventGraph program).ownCompletions_complete_of_not_actor who config
      completed ready action value notOwned]

end Vegas.SourceProgram.EventLowering
