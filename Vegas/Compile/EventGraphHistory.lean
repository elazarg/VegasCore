/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphPolicy

/-! # Source-history decoding for compiled event graphs

Chronological graph completions retain the original dependent action. Decoding
one supported graph step therefore appends exactly one source own action for a
strategic event and appends nothing for chance.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Decode the original actions retained for each player. Foreign completions
and chance events contribute nothing to that player's source history. -/
def decodeHistory {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (history : List (toEventGraph program unique).Completion) :
    SourceProgram.History Player L :=
  fun who => decodeCompletions program unique
    ((toEventGraph program unique).ownCompletions who history)

/-- Appending one graph completion decodes to an update of exactly its source
owner, or to no source-history change when the event is chance. -/
theorem decodeHistory_append_completion
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (history : List (toEventGraph program unique).Completion)
    (event : Fin (eventCount program))
    (action : (toEventGraph program unique).Action event) :
    decodeHistory program unique (history ++ [⟨event, action⟩]) =
      match decodeEventAction program event action with
      | none => decodeHistory program unique history
      | some sourceAction =>
          Function.update (decodeHistory program unique history)
            (sourceActionOwner sourceAction)
            (decodeHistory program unique history (sourceActionOwner sourceAction) ++
              [sourceAction]) := by
  have ownerLaw := decodeEventAction_owner program event action
  rw [eventOwner?_eq_actor program unique event] at ownerLaw
  cases decoded : decodeEventAction program event action with
  | none =>
      have actorNone : (toEventGraph program unique).actor? event = none := by
        simpa [decoded] using ownerLaw.symm
      funext who
      simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
        actorNone]
  | some sourceAction =>
      have actorSome : (toEventGraph program unique).actor? event =
          some (sourceActionOwner sourceAction) := by
        simpa [decoded] using ownerLaw.symm
      funext who
      by_cases same : sourceActionOwner sourceAction = who
      · subst who
        simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
          actorSome, decoded, Function.update]
      · have notOwned : (toEventGraph program unique).actor? event ≠ some who := by
          rw [actorSome]
          simpa using same
        have whoNe : who ≠ sourceActionOwner sourceAction := Ne.symm same
        simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
          notOwned, Function.update, whoNe]

/-- One supported executor step has exactly the source-history effect of its
original dependent action. In particular the `none` branch is a chance event
and leaves every player's history unchanged. -/
theorem decodeHistory_step
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (config next : (toEventGraph program unique).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toEventGraph program unique).Action event)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program unique next.history =
      match decodeEventAction program event action with
      | none => decodeHistory program unique config.history
      | some sourceAction =>
          Function.update (decodeHistory program unique config.history)
            (sourceActionOwner sourceAction)
            (decodeHistory program unique config.history
                (sourceActionOwner sourceAction) ++ [sourceAction]) := by
  rw [config.step_history event ready action next supported]
  exact decodeHistory_append_completion program unique config.history event action

/-- A supported chance step leaves decoded source history unchanged. -/
theorem decodeHistory_step_of_none
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (config next : (toEventGraph program unique).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toEventGraph program unique).Action event)
    (chance : decodeEventAction program event action = none)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program unique next.history =
      decodeHistory program unique config.history := by
  rw [decodeHistory_step program unique config next event ready action supported, chance]

/-- A supported strategic step appends the retained original action to exactly
its source owner's history. -/
theorem decodeHistory_step_of_some
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (config next : (toEventGraph program unique).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toEventGraph program unique).Action event)
    (sourceAction : SourceProgram.OwnAction Player L)
    (decoded : decodeEventAction program event action = some sourceAction)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program unique next.history =
      Function.update (decodeHistory program unique config.history)
        (sourceActionOwner sourceAction)
        (decodeHistory program unique config.history (sourceActionOwner sourceAction) ++
          [sourceAction]) := by
  rw [decodeHistory_step program unique config next event ready action supported, decoded]

end Vegas.SourceProgram.EventLowering
