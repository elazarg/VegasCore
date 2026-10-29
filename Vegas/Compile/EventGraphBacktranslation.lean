/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphHistory

/-! # Backtranslation of compiled event-graph actions

Original source actions are reconstructed as dependent graph actions at their
source-ranked event identities. No value is invented when an action does not
belong to the selected event.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Invert a source action at its source-ranked event identity. The operation
is partial because the action carries its original owner, name, and payload,
all of which must agree with the selected strategic event. -/
def encodeEventAction? : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (event : Fin (eventCount program)) → OwnAction Player L →
      Option (Vegas.EventGraph.EventField.Action (outputLayout program event))
  | _, _, .ret _, event, _ => nomatch event
  | _, _, .sample name fresh law next, event, action =>
      Fin.cases (motive := fun event =>
          Option (Vegas.EventGraph.EventField.Action
            (outputLayout (.sample name fresh law next) event)))
        none (fun tail => encodeEventAction? next tail action) event
  | _, _, .commit (payload := payload) name owner fresh guard next, event, action =>
      Fin.cases (motive := fun event =>
          Option (Vegas.EventGraph.EventField.Action
            (outputLayout (.commit name owner fresh guard next) event)))
        (match action with
          | .commit actionOwner actionName actionPayload choice =>
              if _ownerEq : actionOwner = owner then
                if _nameEq : actionName = name then
                  if payloadEq : actionPayload = payload then
                    some (payloadEq ▸ choice)
                  else none
                else none
              else none
          | .reveal _ _ _ => none)
        (fun tail => encodeEventAction? next tail action) event
  | _, _, .reveal published owner name fresh selected unresolved next, event, action =>
      Fin.cases (motive := fun event =>
          Option (Vegas.EventGraph.EventField.Action
            (outputLayout
              (.reveal published owner name fresh selected unresolved next) event)))
        (match action with
          | .commit _ _ _ _ => none
          | .reveal actionOwner actionName disclose =>
              if _ownerEq : actionOwner = owner then
                if _nameEq : actionName = name then some disclose else none
              else none)
        (fun tail => encodeEventAction? next tail action) event

/-- Every successfully encoded action decodes to the exact original source
action, including its owner, source name, payload identity, and value. -/
theorem decodeEventAction_encodeEventAction?_eq_some :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (event : Fin (eventCount program)) → (sourceAction : OwnAction Player L) →
    (graphAction : Vegas.EventGraph.EventField.Action (outputLayout program event)) →
    encodeEventAction? program event sourceAction = some graphAction →
      decodeEventAction program event graphAction = some sourceAction
  | _, _, .ret _, event, _, _, _ => nomatch event
  | _, _, .sample name fresh law next, event, sourceAction, graphAction, encoded => by
      refine Fin.cases (motive := fun event =>
        ∀ graphAction : Vegas.EventGraph.EventField.Action
            (outputLayout (.sample name fresh law next) event),
          encodeEventAction? (.sample name fresh law next) event sourceAction =
              some graphAction →
            decodeEventAction (.sample name fresh law next) event graphAction =
              some sourceAction) ?_ ?_ event graphAction encoded
      · intro graphAction impossible
        simp [encodeEventAction?] at impossible
      · intro tail graphAction encoded
        exact decodeEventAction_encodeEventAction?_eq_some next tail sourceAction
          graphAction encoded
  | _, _, .commit name owner fresh guard next, event, sourceAction, graphAction,
      encoded => by
      refine Fin.cases (motive := fun event =>
        ∀ graphAction : Vegas.EventGraph.EventField.Action
            (outputLayout (.commit name owner fresh guard next) event),
          encodeEventAction? (.commit name owner fresh guard next) event sourceAction =
              some graphAction →
            decodeEventAction (.commit name owner fresh guard next) event graphAction =
              some sourceAction) ?_ ?_ event graphAction encoded
      · intro graphAction encoded
        cases sourceAction with
        | commit actionOwner actionName actionPayload choice =>
            simp only [encodeEventAction?] at encoded
            split at encoded <;> try contradiction
            split at encoded <;> try contradiction
            split at encoded <;> try contradiction
            rename_i ownerEq nameEq payloadEq
            cases ownerEq
            cases nameEq
            cases payloadEq
            cases encoded
            simp [decodeEventAction]
        | reveal actionOwner actionName disclose =>
            simp [encodeEventAction?] at encoded
      · intro tail graphAction encoded
        exact decodeEventAction_encodeEventAction?_eq_some next tail sourceAction
          graphAction encoded
  | _, _, .reveal published owner name fresh selected unresolved next, event,
      sourceAction, graphAction, encoded => by
      refine Fin.cases (motive := fun event =>
        ∀ graphAction : Vegas.EventGraph.EventField.Action
            (outputLayout
              (.reveal published owner name fresh selected unresolved next) event),
          encodeEventAction?
              (.reveal published owner name fresh selected unresolved next) event
              sourceAction = some graphAction →
            decodeEventAction
              (.reveal published owner name fresh selected unresolved next) event
              graphAction = some sourceAction) ?_ ?_ event graphAction encoded
      · intro graphAction encoded
        cases sourceAction with
        | commit actionOwner actionName actionPayload choice =>
            simp [encodeEventAction?] at encoded
        | reveal actionOwner actionName disclose =>
            simp only [encodeEventAction?] at encoded
            split at encoded <;> try contradiction
            split at encoded <;> try contradiction
            rename_i ownerEq nameEq
            cases ownerEq
            cases nameEq
            cases encoded
            rfl
      · intro tail graphAction encoded
        exact decodeEventAction_encodeEventAction?_eq_some next tail sourceAction
          graphAction encoded

/-- At every strategic event, encoding the action just decoded from that event
recovers the dependent graph action exactly. Chance events cannot satisfy the
premise. -/
theorem encodeEventAction?_decodeEventAction_eq_some :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (event : Fin (eventCount program)) →
    (graphAction : Vegas.EventGraph.EventField.Action (outputLayout program event)) →
    (sourceAction : OwnAction Player L) →
    decodeEventAction program event graphAction = some sourceAction →
      encodeEventAction? program event sourceAction = some graphAction
  | _, _, .ret _, event, _, _, _ => nomatch event
  | _, _, .sample name fresh law next, event, graphAction, sourceAction, decoded => by
      refine Fin.cases (motive := fun event =>
        ∀ graphAction : Vegas.EventGraph.EventField.Action
            (outputLayout (.sample name fresh law next) event),
          decodeEventAction (.sample name fresh law next) event graphAction =
              some sourceAction →
            encodeEventAction? (.sample name fresh law next) event sourceAction =
              some graphAction) ?_ ?_ event graphAction decoded
      · intro graphAction impossible
        simp [decodeEventAction] at impossible
      · intro tail graphAction decoded
        exact encodeEventAction?_decodeEventAction_eq_some next tail graphAction
          sourceAction decoded
  | _, _, .commit name owner fresh guard next, event, graphAction, sourceAction,
      decoded => by
      refine Fin.cases (motive := fun event =>
        ∀ graphAction : Vegas.EventGraph.EventField.Action
            (outputLayout (.commit name owner fresh guard next) event),
          decodeEventAction (.commit name owner fresh guard next) event graphAction =
              some sourceAction →
            encodeEventAction? (.commit name owner fresh guard next) event sourceAction =
              some graphAction) ?_ ?_ event graphAction decoded
      · intro graphAction decoded
        simp only [decodeEventAction] at decoded
        cases decoded
        simp [encodeEventAction?]
      · intro tail graphAction decoded
        exact encodeEventAction?_decodeEventAction_eq_some next tail graphAction
          sourceAction decoded
  | _, _, .reveal published owner name fresh selected unresolved next, event,
      graphAction, sourceAction, decoded => by
      refine Fin.cases (motive := fun event =>
        ∀ graphAction : Vegas.EventGraph.EventField.Action
            (outputLayout
              (.reveal published owner name fresh selected unresolved next) event),
          decodeEventAction
              (.reveal published owner name fresh selected unresolved next) event
              graphAction = some sourceAction →
            encodeEventAction?
              (.reveal published owner name fresh selected unresolved next) event
              sourceAction = some graphAction) ?_ ?_ event graphAction decoded
      · intro graphAction decoded
        simp only [decodeEventAction] at decoded
        cases decoded
        simp [encodeEventAction?]
      · intro tail graphAction decoded
        exact encodeEventAction?_decodeEventAction_eq_some next tail graphAction
          sourceAction decoded

/-- Encode an active player's actions against their source-ranked events.
Every retained choice has a decision and introduces no default of that player. -/
def encodeCompletions? {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    List (Fin (eventCount program)) → List (OwnAction Player L) →
      Option (List (toEventGraph program).Completion)
  | [], [] => some []
  | event :: events, action :: actions => do
      let encoded ← encodeEventAction? program event action
      let tail ← encodeCompletions? program events actions
      pure (⟨event, some encoded, none⟩ :: tail)
  | _, _ => none

/-- An active player's retained completion list is recovered exactly from
its event identities and decoded original actions. -/
theorem encodeCompletions?_decodeCompletions_eq_some
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (completions : List (toEventGraph program).Completion)
    (strategic : ∀ completion ∈ completions,
      ∃ action sourceAction, completion.decision = some action ∧
        decodeEventAction program completion.event action = some sourceAction)
    (noDefault : ∀ completion ∈ completions, completion.defaultEvent = none) :
    encodeCompletions? program (completions.map (·.event))
        (decodeCompletions program completions) = some completions := by
  induction completions with
  | nil => rfl
  | cons completion completions ih =>
      obtain ⟨action, sourceAction, chosen, decoded⟩ := strategic completion (by simp)
      have noNew := noDefault completion (by simp)
      have tailStrategic : ∀ candidate ∈ completions,
          ∃ action sourceAction, candidate.decision = some action ∧
            decodeEventAction program candidate.event action = some sourceAction := by
        intro candidate member
        exact strategic candidate (by simp [member])
      have tailNoDefault : ∀ candidate ∈ completions, candidate.defaultEvent = none := by
        intro candidate member
        exact noDefault candidate (by simp [member])
      have tailEncoded := ih tailStrategic tailNoDefault
      simp only [decodeCompletions, List.filterMap_cons, chosen, Option.bind_some, decoded]
      change encodeCompletions? program
          (completion.event :: completions.map (·.event))
          (sourceAction :: decodeCompletions program completions) =
        some (completion :: completions)
      rw [encodeCompletions?, encodeEventAction?_decodeEventAction_eq_some program
        completion.event action sourceAction decoded, tailEncoded]
      change some (⟨completion.event, some action, none⟩ :: completions) =
        some (completion :: completions)
      congr 2
      cases completion
      congr 1
      · exact chosen.symm
      · exact noNew.symm

end Vegas
