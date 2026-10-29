/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphPolicy

/-! # Source-history decoding for compiled event graphs

Chronological graph completions retain actual dependent decisions. Decoding a
supported step appends precisely its actual source action; automatic completion
and chance contribute no strategic choice.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Source own history retains precisely the player's actual choices. -/
def decodeHistory {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (history : List (toEventGraph program).Completion) : SourceProgram.History Player L :=
  fun who => decodeCompletions program ((toEventGraph program).ownCompletions who history)

/-- A completion contributes only its actual source decision to own history. -/
theorem decodeHistory_append_completion {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (history : List (toEventGraph program).Completion)
    (event : Fin (eventCount program)) (decision : Option ((toEventGraph program).Action event))
    (defaultEvent : Option Player) :
    decodeHistory program (history ++ [⟨event, decision, defaultEvent⟩]) =
      match decision.bind (decodeEventAction program event) with
      | none => decodeHistory program history
      | some sourceAction =>
          Function.update (decodeHistory program history) (sourceActionOwner sourceAction)
            (decodeHistory program history (sourceActionOwner sourceAction) ++ [sourceAction]) := by
  cases decision with
  | none =>
      funext who
      simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions]
  | some action =>
      have ownerLaw := decodeEventAction_owner program event action
      rw [eventOwner?_eq_actor program event] at ownerLaw
      cases decoded : decodeEventAction program event action with
      | none =>
          have actorNone : (toEventGraph program).actor? event = none := by
            simpa [decoded] using ownerLaw.symm
          funext who
          simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
            actorNone, decoded]
      | some sourceAction =>
          have actorSome : (toEventGraph program).actor? event =
              some (sourceActionOwner sourceAction) := by
            simpa [decoded] using ownerLaw.symm
          funext who
          by_cases same : sourceActionOwner sourceAction = who
          · subst who
            simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
              actorSome, decoded, Function.update]
          · have notOwned : (toEventGraph program).actor? event ≠ some who := by
              rw [actorSome]
              simpa using same
            have whoNe : who ≠ sourceActionOwner sourceAction := Ne.symm same
            simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
              notOwned, Function.update, whoNe, decoded]

/-- A supported step has exactly the history effect of its actual decision.
Automatic completions and chance steps leave every player's choices unchanged. -/
theorem decodeHistory_step {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config next : (toEventGraph program).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toEventGraph program).Action event)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program next.history =
      match (config.actualDecision event action).bind (decodeEventAction program event) with
      | none => decodeHistory program config.history
      | some sourceAction =>
          Function.update (decodeHistory program config.history) (sourceActionOwner sourceAction)
            (decodeHistory program config.history (sourceActionOwner sourceAction) ++
              [sourceAction]) := by
  obtain ⟨value, _, history⟩ := config.step_completion event ready action next supported
  rw [history]
  exact decodeHistory_append_completion program config.history event
    (config.actualDecision event action)
    ((Vegas.EventGraph.Completion.fromDecision (graph := toEventGraph program) event
      (config.actualDecision event action) value).defaultEvent)

/-- A step without an actual source decision leaves decoded own history unchanged. -/
theorem decodeHistory_step_of_none {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config next : (toEventGraph program).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toEventGraph program).Action event)
    (silent : (config.actualDecision event action).bind (decodeEventAction program event) = none)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program next.history = decodeHistory program config.history := by
  rw [decodeHistory_step program config next event ready action supported, silent]

/-- A step with an actual decision records precisely its original source action. -/
theorem decodeHistory_step_of_some {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config next : (toEventGraph program).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toEventGraph program).Action event) (sourceAction : OwnAction Player L)
    (decoded : (config.actualDecision event action).bind (decodeEventAction program event) =
      some sourceAction)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program next.history =
      Function.update (decodeHistory program config.history) (sourceActionOwner sourceAction)
        (decodeHistory program config.history (sourceActionOwner sourceAction) ++
          [sourceAction]) := by
  rw [decodeHistory_step program config next event ready action supported, decoded]

end Vegas
