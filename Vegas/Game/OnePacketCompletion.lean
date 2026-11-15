module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourcePrefixPublications
public import Vegas.Pending.ReactiveAcceptedOutput
public import Vegas.Pending.ReactiveCompletion
public import Vegas.Pending.ReactiveOnePacketMenu

@[expose] public section

/-! # Source actions and accepted packet certificates for owned completions -/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts setup.informationGraph)

/-- **The content of a call** at a contract state: at a binding event, the
commitment of the value its handle binds there; at a resolve event, the
disclosure; nothing otherwise. -/
def callContent (state : EventGraphRuntime.State setup.informationGraph)
    (call : Payload setup.informationGraph) : Option (OwnAction Player L) :=
  match call with
  | .commitment event handle =>
      match nodeView setup.informationGraph event with
      | .bind _ payload outputEq _ =>
          decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (some (state.bindingResult handle payload)))
      | _ => none
  | .opening event _ _ =>
      match nodeView setup.informationGraph event with
      | .resolve _ _ _ _ outputEq _ =>
          decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      | _ => none
  | .malformed _ => none

/-- Decode the source content of the material actually transmitted, using its
binding meaning after submission. -/
def sentSourceAction
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (after : (application setup timeouts leaks).Execution)
    (action : (application setup timeouts leaks).Action) : Option (OwnAction Player L) :=
  action.transmission.bind fun material => callContent setup after.application material.call.packet

variable {setup timeouts}

/-- The source action a transmission decodes to is the content of its call at
the state after the submission. -/
theorem sentSourceAction_eq_callContent
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (after : (application setup timeouts leaks).Execution)
    (material : (application setup timeouts leaks).Submission) :
    sentSourceAction setup timeouts leaks after ⟨some material⟩ =
      callContent setup after.application material.call.packet := by
  unfold sentSourceAction callContent
  rfl

/-- **Content stays while meanings stay.** If a later state keeps every fixed
meaning, and a commitment's handle has a fixed meaning, the content of the
call is the same at both states. -/
theorem callContent_keep {before after : EventGraphRuntime.State setup.informationGraph}
    (kept : KeepsFixedCandidates before after) (call : Payload setup.informationGraph)
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
theorem handle_commitment_action (state next : EventGraphRuntime.State setup.informationGraph)
    (id : MessageId Player) (event : setup.informationGraph.EventId) (candidate : Handle
      setup.informationGraph)
    (accepted : handle timeouts state ⟨id, .commitment event candidate⟩ = some next) :
    candidate.1 = id.1 ∧ ∃ (ready : state.config.cut.Ready event) (owner : Player)
      (payload : L.Ty) (outputEq : setup.informationGraph.outputLayout event = .binding owner
        payload)
      (codeEq : cast (congrArg (EventGraph.EventCode setup.informationGraph.layout) outputEq)
        (setup.informationGraph.nodes event) = .bind owner payload),
      nodeView setup.informationGraph event = .bind owner payload outputEq codeEq ∧
      next.config = state.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (some (state.bindingResult candidate payload)))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (state.bindingResult candidate payload)) := by
  obtain ⟨_active, ready, _timely, owner, payload, outputEq, codeEq, view, sender,
    handleOwner, _vacant, _unused, nextEq⟩ :=
    (handle_commitment_iff timeouts state next id event candidate).mp accepted
  refine ⟨handleOwner.trans sender.symm, ready, owner, payload, outputEq, codeEq, view, ?_⟩
  rw [nextEq]
  rfl

/-- An expired owned completion has a failing source action. -/
theorem expiredAction_failing {event : setup.informationGraph.EventId}
    {action : setup.informationGraph.Action event} (expired : ExpiredAction event action) :
    Failing (decodeEventAction setup.program event action) := by
  cases expired with
  | binding owner payload outputEq =>
      exact decodeEventAction_failing_binding setup.program event.val event.isLt outputEq none rfl
  | publication payload outputEq =>
      exact decodeEventAction_failing_publication setup.program event.val event.isLt outputEq

/-- Suppressing an expired action contributes no successful binding or disclosure. -/
theorem expired_record_failing (config : setup.informationGraph.Config)
    {event : setup.informationGraph.EventId} {action : setup.informationGraph.Action event}
    (expired : ExpiredAction event action) :
    Failing ((config.actualDecision event action).bind
      (decodeEventAction setup.program event)) := by
  unfold EventGraph.Config.actualDecision EventGraph.EventCode.actualDecision
  cases (setup.informationGraph.nodes event).actor with
  | none => simp [Failing, OwnAction.disclosure]
  | some owner =>
      by_cases inactive : owner ∈ config.defaulted
      · simp [inactive, Failing, OwnAction.disclosure]
      · simpa only [ite_eq_right inactive, Option.bind_some] using expiredAction_failing expired

/-- One actual packet certifies the source content of a newly recorded
completion, through its raw native result and the following automatic drain. -/
structure AcceptedSourceCompletion
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    (execution next : (application setup timeouts leaks).Execution)
    (record : setup.informationGraph.Completion) (actor : Player) where
  message : Message Player (WitnessedPacket setup.informationGraph)
  pending : message ∈ execution.network.pending
  ledger : message ∈ next.network.ledger
  receipt : (message.id, true) ∈ next.receipts
  named : message.payload.call.event? setup.informationGraph = some record.event
  sender : message.sender = actor
  native : EventGraphRuntime.State setup.informationGraph
  handled : handle timeouts execution.application ⟨message.id, message.payload.call⟩ = some native
  drained : native.drain = next.application
  recorded : record ∈ native.config.history
  content : record.decision.bind (decodeEventAction setup.program record.event) =
    callContent setup execution.application message.payload.call
  candidateOwner : ∀ named candidate, message.payload.call = .commitment named candidate →
    candidate.1 = actor
  bindingAccepted : ∀ owner payload,
    setup.informationGraph.outputLayout record.event = .binding owner payload →
      next.application.accepted (.inr record.event) ≠ none

private theorem record_eq_of_complete
    (state native : EventGraphRuntime.State setup.informationGraph)
    (record : setup.informationGraph.Completion) (fresh : record ∉ state.config.history)
    (present : record ∈ native.config.history) (ready : state.config.cut.Ready record.event)
    (action : setup.informationGraph.Action record.event)
    (value : (setup.informationGraph.outputLayout record.event).Value)
    (complete : native.config = state.config.complete record.event ready action value) :
    record = EventGraph.completion setup.informationGraph record.event
      (state.config.actualDecision record.event action) value := by
  rw [complete, EventGraph.Config.complete_history] at present
  exact List.mem_singleton.mp ((List.mem_append.mp present).resolve_left fresh)

private theorem accepted_record_content
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    (execution next : (application setup timeouts leaks).Execution)
    (message : Message Player (WitnessedPacket setup.informationGraph))
    (native : EventGraphRuntime.State setup.informationGraph)
    (record : setup.informationGraph.Completion) (fresh : record ∉
      execution.application.config.history)
    (present : record ∈ native.config.history)
    (named : message.payload.call.event? setup.informationGraph = some record.event)
    (handled : handle timeouts execution.application ⟨message.id, message.payload.call⟩ =
      some native)
    (drained : native.drain = next.application) :
    record.decision.bind (decodeEventAction setup.program record.event) =
        callContent setup execution.application message.payload.call ∧
      (∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = message.sender) ∧
      ∀ owner payload, setup.informationGraph.outputLayout record.event = .binding owner payload →
        next.application.accepted (.inr record.event) ≠ none := by
  cases packet : message.payload.call with
  | malformed raw => rw [packet] at handled; simp [handle] at handled
  | commitment event candidate =>
      rw [packet] at named
      change some event = some record.event at named
      cases Option.some.inj named
      rw [packet] at handled
      obtain ⟨active, ready, _timely, owner, payload, outputEq, codeEq, view, sender,
        handleOwner, _vacant, _unused, nativeEq⟩ :=
        (handle_commitment_iff timeouts execution.application native message.id record.event
          candidate).mp handled
      have actor := nodeView_bind_actor outputEq codeEq
      have activeOwner : owner ∉ execution.application.config.defaulted := by
        simpa only [sender] using active
      have recorded := record_eq_of_complete execution.application native record fresh present
        ready (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (some (execution.application.bindingResult candidate payload)))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (execution.application.bindingResult candidate payload)) (by rw [nativeEq]; rfl)
      rw [execution.application.config.actualDecision_of_active record.event owner actor
        activeOwner] at recorded
      have decision := eq_of_heq (EventCompletion.mk.inj recorded).2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [decision, Option.bind_some]
        simp only [callContent, view]
      · intro named' candidate' same
        cases same
        exact handleOwner.trans sender.symm
      · intro _owner _payload _layout
        rw [← drained, native.drain_tables.1, nativeEq]
        change Function.update execution.application.accepted (.inr record.event)
          (some candidate) (.inr record.event) ≠ none
        rw [Function.update_self]
        exact Option.some_ne_none _
  | opening event candidate raw =>
      rw [packet] at named
      change some event = some record.event at named
      cases Option.some.inj named
      rw [packet] at handled
      obtain ⟨active, ready, _timely, owner, payload, binding, checks, outputEq, codeEq,
        _value, result, view, sender, _handleOwner, _associated, _rawEq, _fixed, _stored,
        _resolved, nativeEq⟩ :=
        (handle_opening_iff timeouts execution.application native message.id record.event
          candidate raw).mp handled
      have actor := nodeView_resolve_actor outputEq codeEq
      have activeOwner : owner ∉ execution.application.config.defaulted := by
        simpa only [sender] using active
      have recorded := record_eq_of_complete execution.application native record fresh present
        ready (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) result)
        (by rw [nativeEq]; rfl)
      rw [execution.application.config.actualDecision_of_active record.event owner actor
        activeOwner] at recorded
      have decision := eq_of_heq (EventCompletion.mk.inj recorded).2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [decision, Option.bind_some]
        simp only [callContent, view]
      · intro named' candidate' same
        cases same
      · intro _owner _payload layout
        rw [outputEq] at layout
        cases layout

/-- An owned newly recorded completion has an accepted packet certificate,
an exact due-expiry record, or an actual automatic origin at an inherited default. -/
theorem owned_completion_cases
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    (execution next : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (record : setup.informationGraph.Completion) (fresh : record ∉
      execution.application.config.history)
    (present : record ∈ next.application.config.history)
    {actor : Player} (acts : setup.informationGraph.actor? record.event = some actor) :
    Nonempty (AcceptedSourceCompletion (timeouts := timeouts) execution next record actor) ∨
    (command = .application (.expire record.event) ∧
      ∃ entered, execution.application.activatedAt record.event = some entered ∧
        timeouts.duration record.event ≤ execution.application.clock - entered ∧
        ∃ (action : setup.informationGraph.Action record.event)
          (value : (setup.informationGraph.outputLayout record.event).Value),
          ExpiredAction record.event action ∧ record = EventGraph.completion setup.informationGraph
            record.event (execution.application.config.actualDecision record.event action) value) ∨
    (∃ native, native.drain = next.application ∧ record ∉ native.config.history ∧
      ((∃ message ∈ execution.network.pending, command = .include message.id ∧
          handle timeouts execution.application ⟨message.id, message.payload.call⟩ = some native) ∨
        ∃ operation, command = .application operation ∧
          native ∈ (environmentStep timeouts execution.application operation).support) ∧
      record.decision = none ∧ record.defaultEvent = none ∧ actor ∈ native.config.defaulted) := by
  rcases reactive_new_completion_cases timeouts leaks execution next command reached record fresh
    present with accepted | expired | ownerless | automatic
  · obtain ⟨message, pending, native, ledger, receipt, named, sender, handled, drained,
      recorded⟩ := accepted
    have senderEq : message.sender = actor := Option.some.inj (sender.symm.trans acts)
    have data := accepted_record_content execution next message native record fresh recorded named
      handled drained
    left
    exact ⟨{
      message := message
      pending := pending
      ledger := ledger
      receipt := receipt
      named := named
      sender := senderEq
      native := native
      handled := handled
      drained := drained
      recorded := recorded
      content := data.1
      candidateOwner := fun named candidate same => (data.2.1 named candidate same).trans senderEq
      bindingAccepted := data.2.2 }⟩
  · exact Or.inr (Or.inl expired)
  · rw [acts] at ownerless
    cases ownerless
  · obtain ⟨native, drained, freshNative, trigger, silent, unchanged, owner, owned, inactive⟩ :=
      automatic
    have same : owner = actor := Option.some.inj (owned.symm.trans acts)
    subst owner
    exact Or.inr (Or.inr ⟨native, drained, freshNative, trigger, silent, unchanged, inactive⟩)

section Stopping

variable [Fintype Player] (setup timeouts)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
  (bounds : MessageBounds setup.informationGraph) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

/-- The event of the requested source rank has completed, possibly together
with later events through automatic completion. -/
def LateStopped (rank : Nat) (history : ((bounds.onePacketMenu timeouts leaks).protocol
    (initialLaw setup) horizon scheduler).History) : Prop :=
  ∃ control : (application setup timeouts leaks).Control, history.state = some control ∧
    ∃ event ∈ control.execution.application.config.cut.completed, event.val = rank

end Stopping

end Vegas
