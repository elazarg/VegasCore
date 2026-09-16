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
    (unique : (Γ.map Prod.fst).Nodup) (profile : BehavioralProfile program) :
    (toEventGraph program unique).normalizeProfile
        (compileEventProfile program unique profile) =
      compileEventProfile program unique profile := rfl

/-- Advancing an event hidden from the player and absent from its own-action
history leaves the player's actual compiled decision kernel unchanged. -/
theorem compileEventPolicy_complete_hidden
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup) (who : Player)
    (policy : BehavioralPolicy who program)
    (config : (toEventGraph program unique).Config)
    (completed event : Fin (eventCount program))
    (ready : config.cut.Ready completed)
    (action : (toEventGraph program unique).Action completed)
    (value : (outputLayout program completed).Value)
    (hidden : ¬ (toEventGraph program unique).fieldVisibleTo who (.inr completed))
    (notOwned : (toEventGraph program unique).actor? completed ≠ some who)
    (actor : (toEventGraph program unique).actor? event = some who) :
    compileEventPolicy program unique who policy event actor
        ((toEventGraph program unique).playerObserve who
          (config.complete completed ready action value)) =
      compileEventPolicy program unique who policy event actor
        ((toEventGraph program unique).playerObserve who config) := by
  unfold compileEventPolicy Vegas.EventGraph.playerObserve
  dsimp only
  rw [(toEventGraph program unique).playerStore_complete_of_hidden who config
      completed ready action value hidden,
    (toEventGraph program unique).ownCompletions_complete_of_not_actor who config
      completed ready action value notOwned]

end Vegas.SourceProgram.EventLowering
