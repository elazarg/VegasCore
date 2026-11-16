module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphPolicy
public import Vegas.EventGraph.NormalizedPolicy
public import Vegas.EventGraph.PrefixRestriction
public import Vegas.Source.Protocol

@[expose] public section

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

/-- Read an event's actual source action from its retained completion record. -/
def decodeActionAt {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (event : Fin (eventCount program))
    (history : List (toInformationGraph program).Completion) : Option (OwnAction Player L) :=
  (history.find? (fun record => decide (record.event = event))).bind
    fun record => record.decision.bind (decodeEventAction program record.event)

/-- An owned event's action is determined by the owner's observed completion records,
including the distinction between an omitted binding and no actual decision. -/
theorem decodeActionAt_ownCompletions {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (who : Player)
    (event : Fin (eventCount program)) (owned : (toInformationGraph program).actor? event = some
      who)
    (history : List (toInformationGraph program).Completion)
    (nodup : (history.map EventCompletion.event).Nodup) :
    decodeActionAt program event ((toInformationGraph program).ownCompletions who history) =
      decodeActionAt program event history := by
  unfold decodeActionAt EventGraph.ownCompletions
  rw [EventGraph.find?_filter_of_nodup history nodup]
  cases found : history.find? (fun record => decide (record.event = event)) with
  | none => rfl
  | some record =>
      have tagged : record.event = event := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have actor : (toInformationGraph program).actor? record.event = some who := tagged ▸ owned
      cases decision : record.decision <;> simp [Option.filter, actor, decision]

open EventGraph in
/-- Decoding an active completed binding recovers the same submitted value and record. -/
theorem completed_binding_source_record
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names)
    {deps : (toEventGraph program).Dependencies}
    {origin final : ((toEventGraph program).withDependencies deps).Config}
    (path : Relation.ReflTransGen EventGraph.Config.Step origin final)
    (event : ((toEventGraph program).withDependencies deps).EventId)
    (pending : event ∉ origin.cut.completed)
    (completed : event ∈ final.cut.completed) (owner : Player) (name : VarId) (payload : L.Ty)
    (binding : ((toEventGraph program).withDependencies deps).outputLayout event =
      .binding owner payload)
    (active : owner ∉ final.defaulted)
    (decode : ∀ choice : Option (PublicationResult (L.Val payload)),
      decodeEventAction program event
        (cast (congrArg EventField.Action binding.symm) choice) =
          some (.commit owner name payload choice)) :
    ∃ result : PublicationResult (L.Val payload),
      OwnAction.binding owner name payload
        (decodeActionAt program event final.history) = some result ∧
      completionOf final event = some (EventGraph.completion
        ((toEventGraph program).withDependencies deps) event
        (some (cast (congrArg EventField.Action binding.symm) (some result)))
        (cast (congrArg EventField.Value binding.symm) result)) ∧
      final.outputs event = some (cast (congrArg EventField.Value binding.symm) result) := by
  obtain ⟨result, record, stored⟩ := Config.Step.path_active_binding_record path event pending
    completed owner payload binding active
  refine ⟨result, ?_, record, stored⟩
  have decoded : decodeActionAt program event final.history =
      some (.commit owner name payload (some result)) := by
    unfold decodeActionAt
    change (completionOf final event).bind _ = _
    rw [record]
    change decodeEventAction program event
      (cast (congrArg EventField.Action binding.symm) (some result)) = _
    exact decode (some result)
  rw [decoded, OwnAction.binding_commit]


/-- Source own history retains precisely the player's actual choices. -/
def decodeHistory {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (history : List (toInformationGraph program).Completion) : SourceProgram.History Player L :=
  fun who => decodeCompletions program ((toInformationGraph program).ownCompletions who history)

/-- A completion contributes only its actual source decision to own history. -/
theorem decodeHistory_append_completion {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (history : List (toInformationGraph program).Completion)
    (event : Fin (eventCount program))
    (decision : Option ((toInformationGraph program).Action event))
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
          have actorNone : (toInformationGraph program).actor? event = none := by
            simpa [decoded] using ownerLaw.symm
          funext who
          simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
            actorNone, decoded]
      | some sourceAction =>
          have actorSome : (toInformationGraph program).actor? event =
              some (sourceActionOwner sourceAction) := by
            simpa [decoded] using ownerLaw.symm
          funext who
          by_cases same : sourceActionOwner sourceAction = who
          · subst who
            simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
              actorSome, decoded, Function.update]
          · have notOwned : (toInformationGraph program).actor? event ≠ some who := by
              rw [actorSome]
              simpa using same
            have whoNe : who ≠ sourceActionOwner sourceAction := Ne.symm same
            simp [decodeHistory, Vegas.EventGraph.ownCompletions, decodeCompletions,
              notOwned, Function.update, whoNe, decoded]

/-- A supported step has exactly the history effect of its actual decision.
Automatic completions and chance steps leave every player's choices unchanged. -/
theorem decodeHistory_step {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config next : (toInformationGraph program).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toInformationGraph program).Action event)
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
    ((EventGraph.completion (toInformationGraph program) event
      (config.actualDecision event action) value).defaultEvent)

/-- A step without an actual source decision leaves decoded own history unchanged. -/
theorem decodeHistory_step_of_none {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config next : (toInformationGraph program).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toInformationGraph program).Action event)
    (silent : (config.actualDecision event action).bind (decodeEventAction program event) = none)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program next.history = decodeHistory program config.history := by
  rw [decodeHistory_step program config next event ready action supported, silent]

/-- A step with an actual decision records precisely its original source action. -/
theorem decodeHistory_step_of_some {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config next : (toInformationGraph program).Config)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (action : (toInformationGraph program).Action event) (sourceAction : OwnAction Player L)
    (decoded : (config.actualDecision event action).bind (decodeEventAction program event) =
      some sourceAction)
    (supported : next ∈ (config.step event ready action).support) :
    decodeHistory program next.history =
      Function.update (decodeHistory program config.history) (sourceActionOwner sourceAction)
        (decodeHistory program config.history (sourceActionOwner sourceAction) ++
          [sourceAction]) := by
  rw [decodeHistory_step program config next event ready action supported, decoded]

end Vegas
