/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFreshSlots
import Vegas.Pending.ReactiveAcceptedOutput
import Vegas.Pending.ReactiveCompletion

/-! # Source actions and accepted packet certificates for owned completions -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source action that commits a failed binding or does not disclose. -/
def Failing (choice : Option (OwnAction Player L)) : Prop :=
  (∀ owner name payload result, choice = some (.commit owner name payload result) →
    result = .failure) ∧ OwnAction.disclosure choice = false

/-- The decoded action of a binding event completed with a failed binding is
failing. -/
theorem decodeEventAction_failing_binding {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {owner : Player} {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .binding owner payload),
      Failing (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero =>
          change EventGraph.EventField.binding commitOwner _ = _ at outputEq
          obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj outputEq
          refine ⟨fun actor actorName actorPayload result chosen => ?_, rfl⟩
          cases chosen
          rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

/-- The decoded action of a publication event completed with withholding is
failing. -/
theorem decodeEventAction_failing_publication {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .publication payload),
      Failing (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound payload outputEq
      cases count with
      | zero =>
          refine ⟨fun actor actorName actorPayload result chosen => ?_, rfl⟩
          cases Option.some.inj chosen
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))

/-- **The content of a call** at a contract state: at a binding event, the
commitment of the value its handle binds there; at a resolve event, the
disclosure; nothing otherwise. -/
def callContent (state : EventGraphRuntime.State (graph setup))
    (call : Payload (graph setup)) : Option (OwnAction Player L) :=
  match call with
  | .commitment event handle =>
      match nodeView (graph setup) event with
      | .bind _ payload outputEq _ =>
          decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (state.bindingResult handle payload))
      | _ => none
  | .opening event _ _ =>
      match nodeView (graph setup) event with
      | .resolve _ _ _ _ outputEq _ =>
          decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      | _ => none
  | .malformed _ => none

variable {setup runtime}

/-- The source action a transmission decodes to is the content of its call at
the state after the submission. -/
theorem sentSourceAction_eq_callContent
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (after : (application setup runtime leaks).Execution)
    (material : (application setup runtime leaks).Submission) :
    sentSourceAction setup runtime leaks after ⟨some material⟩ =
      callContent setup after.application material.call.packet := by
  unfold sentSourceAction callContent
  rfl

/-- **Content stays while meanings stay.** If a later state keeps every fixed
meaning, and a commitment's handle has a fixed meaning, the content of the
call is the same at both states. -/
theorem callContent_keep {before after : EventGraphRuntime.State (graph setup)}
    (kept : KeepsFixedCandidates before after) (call : Payload (graph setup))
    (fixed : ∀ event handle, call = .commitment event handle →
      before.candidates.lookup handle ≠ .fresh) :
    callContent setup after call = callContent setup before call := by
  cases call with
  | commitment event handle =>
      have same : after.bindingResult handle = before.bindingResult handle := by
        funext payload
        unfold State.bindingResult
        rw [kept handle (fixed event handle rfl)]
      simp only [callContent, same]
  | opening => rfl
  | malformed => rfl

/-- An accepted commitment completes its event with the binding result of its
handle at the state it is included at, and its handle belongs to its sender. -/
theorem handle_commitment_action (state next : EventGraphRuntime.State (graph setup))
    (id : MessageId Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    candidate.1 = id.1 ∧ ∃ (ready : state.config.cut.Ready event) (owner : Player)
      (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind owner payload),
      nodeView (graph setup) event = .bind owner payload outputEq codeEq ∧
      next.config = state.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (state.bindingResult candidate payload))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (state.bindingResult candidate payload)) := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView (graph setup) event with
      | resolve | sample => simp [handle, ready, timely, view] at accepted
      | bind owner payload outputEq codeEq =>
          simp only [handle, dite_eq_left ready, dite_eq_left timely, view] at accepted
          split at accepted
          · rename_i sender
            split at accepted
            · rename_i handleOwner
              split at accepted
              · split at accepted
                · cases accepted
                  exact ⟨handleOwner.trans sender.symm, ready, owner, payload, outputEq, codeEq,
                    rfl, rfl⟩
                · cases accepted
              · cases accepted
            · cases accepted
          · cases accepted
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

/-- An expired owned completion has a failing source action. -/
theorem expiredAction_failing {event : (graph setup).EventId}
    {action : (graph setup).Action event} (expired : ExpiredAction event action) :
    Failing (decodeEventAction setup.program event action) := by
  cases expired with
  | binding owner payload outputEq =>
      exact decodeEventAction_failing_binding setup.program event.val event.isLt outputEq
  | publication payload outputEq =>
      exact decodeEventAction_failing_publication setup.program event.val event.isLt outputEq

/-- A single actual message supplies every accepted-completion observation. -/
structure AcceptedSourceCompletion
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup runtime leaks).Execution)
    (event : (graph setup).EventId) (action : (graph setup).Action event) (actor : Player) where
  message : Message Player (WitnessedPacket (graph setup))
  pending : message ∈ execution.network.pending
  ledger : message ∈ next.network.ledger
  receipt : (message.id, true) ∈ next.receipts
  named : message.payload.call.event? (graph setup) = some event
  sender : message.sender = actor
  content : decodeEventAction setup.program event action =
    callContent setup execution.application message.payload.call
  candidateOwner : ∀ named candidate, message.payload.call = .commitment named candidate →
    candidate.1 = actor
  bindingAccepted : ∀ owner payload, (graph setup).outputLayout event = .binding owner payload →
    next.application.accepted (.inr event) ≠ none

/-- An owned completion either has one accepted-message certificate or is a
due expiry. Its receipt and decoded content refer to that same accepted message. -/
theorem owned_completion_cases
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor) :
    Nonempty (AcceptedSourceCompletion (runtime := runtime) execution next event action actor) ∨
      (command = .application (.expire event) ∧
        ∃ entered, execution.application.activatedAt event = some entered ∧
          runtime.deadline event ≤ execution.application.clock - entered ∧
          next.application.accepted = execution.application.accepted ∧
          ExpiredAction event action) := by
  rcases reactive_completion_cases runtime leaks execution next command reached ready
      action member with accepted | expired | ownerless
  · obtain ⟨message, pending, ledger, receipt, named, sender, call⟩ := accepted
    have senderEq : message.sender = actor := Option.some.inj (sender.symm.trans acts)
    have packetData : decodeEventAction setup.program event action =
          callContent setup execution.application message.payload.call ∧
        (∀ named candidate, message.payload.call = .commitment named candidate →
          candidate.1 = actor) ∧
        ∀ owner payload, (graph setup).outputLayout event = .binding owner payload →
          next.application.accepted (.inr event) ≠ none := by
      cases packet : message.payload.call with
      | malformed raw => rw [packet] at call; simp [handle] at call
      | commitment other candidate =>
          rw [packet] at call
          obtain ⟨owned, otherReady, owner, payload, outputEq, codeEq, view, configEq⟩ :=
            handle_commitment_action (runtime := runtime) execution.application next.application
              message.id other
              candidate call
          have otherMember : next.application.config ∈ (execution.application.config.step other
              otherReady (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (execution.application.bindingResult candidate payload))).support := by
            rw [commit_step _ other otherReady outputEq codeEq, configEq]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          cases step_completion_unique otherMember member
          have table := (handle_commitment_tables runtime execution.application
            next.application message.id _ candidate call).2.1
          refine ⟨?_, ?_, fun _ _ _ => ?_⟩
          · simp only [callContent, view]
          · intro named' candidate' same
            cases same
            exact owned.trans senderEq
          · rw [table, Function.update_self]
            exact Option.some_ne_none _
      | opening other candidate raw =>
          rw [packet] at call
          obtain ⟨otherReady, otherAction, otherMember, _, _, owner, payload, binding,
            checks, outputEq, codeEq, view, actionEq⟩ :=
            handle_opening_config_step runtime execution.application next.application
              message.id other candidate raw call
          cases step_completion_unique otherMember member
          refine ⟨?_, ?_, fun _ _ layout => ?_⟩
          · rw [actionEq]
            simp only [callContent, view]
          · intro named candidate same
            cases same
          · rw [outputEq] at layout
            cases layout
    exact Or.inl ⟨⟨message, pending, ledger, receipt, named, senderEq,
      packetData.1, packetData.2.1, packetData.2.2⟩⟩
  · exact Or.inr expired
  · rw [acts] at ownerless
    cases ownerless

end Vegas
