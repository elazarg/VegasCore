/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphHistory

/-! # Backtranslation of compiled event-graph actions

Original source actions are reconstructed as dependent graph actions at their
source-ranked event identities. No value is invented when an action does not
belong to the selected event.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

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

/-- Encode a source action list against a concrete list of source-ranked event
identities. Length or event/action mismatches fail explicitly. -/
def encodeCompletions? {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    List (Fin (eventCount program)) → List (OwnAction Player L) →
      Option (List (toEventGraph program).Completion)
  | [], [] => some []
  | event :: events, action :: actions => do
      let encoded ← encodeEventAction? program event action
      let tail ← encodeCompletions? program events actions
      pure (⟨event, encoded⟩ :: tail)
  | _, _ => none

/-- The constructive history encoder is a genuine right inverse of completion
decoding whenever it succeeds. -/
theorem decodeCompletions_encodeCompletions?_eq :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (events : List (Fin (eventCount program))) →
    (actions : List (OwnAction Player L)) →
    (completions : List (toEventGraph program).Completion) →
    encodeCompletions? program events actions = some completions →
      decodeCompletions program completions = actions
  | _, _, program, [], [], completions, encoded => by
      simp [encodeCompletions?] at encoded
      subst completions
      rfl
  | _, _, program, event :: events, action :: actions, completions,
      encoded => by
      cases actionEncoded : encodeEventAction? program event action with
      | none =>
        rw [encodeCompletions?, actionEncoded] at encoded
        contradiction
      | some graphAction =>
        cases tailEncoded : encodeCompletions? program events actions with
        | none =>
          rw [encodeCompletions?, actionEncoded, tailEncoded] at encoded
          contradiction
        | some tail =>
          rw [encodeCompletions?, actionEncoded, tailEncoded] at encoded
          cases encoded
          simp only [decodeCompletions, List.filterMap_cons]
          rw [decodeEventAction_encodeEventAction?_eq_some program event action
            graphAction actionEncoded]
          change action :: decodeCompletions program tail = action :: actions
          congr 1
          exact decodeCompletions_encodeCompletions?_eq program events actions
            tail tailEncoded
  | _, _, _, [], _ :: _, _, encoded => by
      simp [encodeCompletions?] at encoded
  | _, _, _, _ :: _, [], _, encoded => by
      simp [encodeCompletions?] at encoded

/-- A completion list containing only strategic events is reconstructed exactly
from its source-ranked event identities and decoded original actions. -/
theorem encodeCompletions?_decodeCompletions_eq_some
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (completions : List (toEventGraph program).Completion)
    (strategic : ∀ completion ∈ completions,
      ∃ sourceAction,
        decodeEventAction program completion.event completion.action =
          some sourceAction) :
    encodeCompletions? program (completions.map (·.event))
        (decodeCompletions program completions) = some completions := by
  induction completions with
  | nil => rfl
  | cons completion completions ih =>
      obtain ⟨sourceAction, decoded⟩ := strategic completion (by simp)
      have tailStrategic : ∀ candidate ∈ completions,
          ∃ sourceAction,
            decodeEventAction program candidate.event candidate.action =
              some sourceAction := by
        intro candidate member
        exact strategic candidate (by simp [member])
      have tailEncoded := ih tailStrategic
      simp only [decodeCompletions, List.filterMap_cons, decoded]
      change encodeCompletions? program
          (completion.event :: completions.map (·.event))
          (sourceAction :: decodeCompletions program completions) =
        some (completion :: completions)
      rw [encodeCompletions?,
        encodeEventAction?_decodeEventAction_eq_some program completion.event
          completion.action sourceAction decoded,
        tailEncoded]
      rfl

end Vegas.SourceProgram.EventLowering
