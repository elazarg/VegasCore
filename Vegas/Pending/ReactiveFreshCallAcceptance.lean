/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveServiceConformance
import Vegas.Pending.ReactiveEventStability

/-! # Native-acceptable fresh calls

The native predicate admits opaque binding handles and authentic typed openings.
An opening need not pass its public guards: the handler computes the publication
result and records default if it fails. The stricter `freshServiceEnvelope`
continues to certify successful content for the settled audit.
While a ready event is unfinished, retained public receipts and an authentic
certificate supply the handler's association and private binding conditions.
Initialized-history quiescence supplies activity of its owner; the deadline is
checked at inclusion. No client predicts a successful guarded result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)

/-- Native acceptance permits authentic openings independently of their guarded result.
A binding's candidate need not be the author's canonical serial. -/
def freshServiceAcceptable (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  match message.payload.call with
  | .commitment event _ => view.BindingIncludable runtime ⟨message.id, message.payload.call⟩ ∧
      message.payload.token = some ⟨event⟩
  | .opening event candidate raw =>
      view.EventReady event ∧
      (match view.activatedAt event with
        | none => False
        | some entered => view.clock - entered < runtime.deadline event) ∧
      certifiedOpening message.payload = true ∧
      (match nodeView graph event with
        | .resolve owner payload binding _ _ _ =>
            message.sender = owner ∧ candidate.1 = owner ∧
              view.accepted binding.field = some candidate ∧ raw.ty = payload ∧
              message.payload.token = some ⟨event⟩
        | .bind .. | .sample .. => False)
  | .malformed _ => False

/-- The native opening format does not require successful public guards. -/
theorem freshServiceAcceptable_opening_iff (view : PublicView graph) (id : MessageId Player)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L) (evidence : Option (OpeningFact graph))
    (token : Option (ReadinessToken graph)) :
    runtime.freshServiceAcceptable view ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩ ↔
      view.EventReady event ∧
      (match view.activatedAt event with
        | none => False
        | some entered => view.clock - entered < runtime.deadline event) ∧
      certifiedOpening (⟨.opening event candidate raw, evidence, token⟩ :
        WitnessedPacket graph) = true ∧
      id.1 = owner ∧ candidate.1 = owner ∧ view.accepted binding.field = some candidate ∧
        raw.ty = payload ∧ token = some ⟨event⟩ := by
  simp only [freshServiceAcceptable, node, Message.sender]

/-- A conforming packet is acceptable. -/
theorem freshServiceEnvelope.acceptable {view : PublicView graph}
    {message : Message Player (WitnessedPacket graph)}
    (conforming : runtime.freshServiceEnvelope view message) :
    runtime.freshServiceAcceptable view message := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | commitment event candidate => exact ⟨conforming.1, conforming.2.2.2⟩
  | opening event candidate raw =>
      exact ⟨conforming.1, conforming.2.1, conforming.2.2.1, conforming.2.2.2.2⟩
  | malformed raw => exact conforming

/-- An acceptable fresh call carries the readiness token of its event. -/
theorem freshServiceAcceptable.tokenValid {view : PublicView graph}
    {message : Message Player (WitnessedPacket graph)}
    (conforming : runtime.freshServiceAcceptable view message) :
    message.payload.tokenValid = true := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | commitment event candidate =>
      obtain ⟨_, tokened⟩ := conforming
      change token = some ⟨event⟩ at tokened
      subst tokened
      exact WitnessedPacket.tokenValid_commitment _ _ _
  | opening event candidate raw =>
      cases node : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨_, _, _, _, _, _, _, tokened⟩ :=
            (runtime.freshServiceAcceptable_opening_iff view id event owner payload binding checks
              outputEq codeEq node candidate raw evidence token).mp conforming
          subst tokened
          exact WitnessedPacket.tokenValid_opening _ _ _ _
      | bind _ _ _ _ =>
          simp only [freshServiceAcceptable, node] at conforming
          exact conforming.2.2.2.elim
      | sample _ _ _ _ =>
          simp only [freshServiceAcceptable, node] at conforming
          exact conforming.2.2.2.elim
  | malformed raw => exact conforming.elim

/-- Native-acceptable fresh packets name publicly ready events. -/
theorem freshServiceAcceptable_ready (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph))
    (permitted : runtime.freshServiceAcceptable view message) :
    ∃ event, message.payload.call.event? graph = some event ∧ view.EventReady event := by
  cases call : message.payload.call with
  | commitment event candidate =>
      simp only [freshServiceAcceptable, call, PublicView.BindingIncludable] at permitted
      exact ⟨event, rfl, permitted.1.2.1⟩
  | opening event candidate raw =>
      simp only [freshServiceAcceptable, call] at permitted
      exact ⟨event, rfl, permitted.1⟩
  | malformed => simp only [freshServiceAcceptable, call] at permitted

/-- Native-acceptable packets name events owned by their authenticated senders. -/
theorem freshServiceAcceptable_owned (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph))
    (permitted : runtime.freshServiceAcceptable view message) :
    ∃ event, message.payload.call.event? graph = some event ∧ view.EventReady event ∧
      graph.actor? event = some message.sender := by
  cases call : message.payload.call with
  | commitment event candidate =>
      simp only [freshServiceAcceptable, call] at permitted
      have bound := permitted.1
      simp only [PublicView.BindingIncludable] at bound
      cases node : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          simp only [node] at bound
          have authored : message.sender = owner := bound.2.2.2.1
          have actor := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
          exact ⟨event, rfl, bound.2.1, authored ▸ actor⟩
      | sample payload kernel outputEq codeEq => simp only [node, and_false] at bound
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [node, and_false] at bound
  | opening event candidate raw =>
      simp only [freshServiceAcceptable, call] at permitted
      cases node : nodeView graph event with
      | bind owner payload outputEq codeEq => simp only [node, and_false] at permitted
      | sample payload kernel outputEq codeEq => simp only [node, and_false] at permitted
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [node] at permitted
          have authored : message.sender = owner := permitted.2.2.2.1
          have actor := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
          exact ⟨event, rfl, permitted.1, authored ▸ actor⟩
  | malformed => simp only [freshServiceAcceptable, call] at permitted

/-- Native acceptance determines the authentic opening format, without a guard-success claim. -/
theorem freshServiceAcceptable_resolution_shape
    (view : PublicView graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (message : Message Player (WitnessedPacket graph))
    (named : message.payload.call.event? graph = some event)
    (permitted : runtime.freshServiceAcceptable view message) :
    ∃ candidate raw, message.sender = owner ∧ candidate.1 = owner ∧
      view.accepted binding.field = some candidate ∧ raw.ty = payload ∧
      message.payload = ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩ := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      simp only [freshServiceAcceptable, PublicView.BindingIncludable, node, and_false] at permitted
      exact permitted.1.elim
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨_ready, _timely, certified, sender, owned, associated, typed, tokened⟩ :=
        (runtime.freshServiceAcceptable_opening_iff view id event owner payload binding checks
          outputEq codeEq node candidate raw evidence token).mp permitted
      have evidenceEq : evidence = some ⟨candidate, raw⟩ := by
        cases evidence with
        | none => simp only [certifiedOpening, Bool.false_eq_true] at certified
        | some fact =>
            simp only [certifiedOpening, decide_eq_true_eq] at certified
            exact congrArg some certified
      exact ⟨candidate, raw, sender, owned, associated, typed, by rw [evidenceEq, tokened]⟩
  | malformed raw => exact permitted.elim

/-- **A commitment stays includable.** On a graph whose simultaneously ready
events have different actors, a commitment includable on a recorded view of its
ready event is accepted at a later state where the event is unfinished and
within its deadline, when the events completed since were ready together with
it and accepted handles changed only at their vacant output fields. -/
theorem bindingIncludable_accepted_of_extends (relaxed : graph.RevealRelaxedOrdered)
    (state : State graph) (view : PublicView graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph)
    (includable : view.BindingIncludable runtime ⟨id, .commitment event candidate⟩)
    {extra : List graph.EventId}
    (order : state.publicView.observation.completionOrder =
      view.observation.completionOrder ++ extra)
    (together : ∀ other ∈ extra, graph.ReadyTogether other event)
    (acceptedChanged : ∀ field, state.accepted field ≠ view.accepted field →
      view.accepted field = none ∧ ∃ other ∈ extra, field = .inr other)
    (unfinished : event ∉ state.config.cut.completed)
    (timely : state.WithinDeadline runtime event)
    (quiescent : ∀ event, ¬ state.AutomaticReady event)
    (invariant : state.BindingInvariant) :
    ∃ next, handle runtime state ⟨id, .commitment event candidate⟩ = some next := by
  obtain ⟨_active, ready, _, owned⟩ := includable
  have readyNow := ready_of_eventReady_extends order ready unfinished
  have completedExtra : ∀ other ∈ extra, other ∈ state.config.cut.completed := by
    intro other inside
    apply (state.config.history_exact other).mp
    change other ∈ state.publicView.observation.completionOrder
    rw [order]
    exact List.mem_append_right _ inside
  cases node : nodeView graph event with
  | resolve _ _ _ _ _ _ => rw [node] at owned; exact owned.elim
  | sample _ _ _ _ => rw [node] at owned; exact owned.elim
  | bind owner payload outputEq codeEq =>
      rw [node] at owned
      obtain ⟨sender, handleOwner, vacant, unused⟩ := owned
      have eventActor := graph.actor?_of_outputLayout_binding outputEq
      have vacantNow : state.accepted (.inr event) = none := by
        by_contra occupied
        have changed : state.accepted (.inr event) ≠ view.accepted (.inr event) := by
          rw [vacant]
          exact occupied
        obtain ⟨_, other, inside, same⟩ := acceptedChanged _ changed
        cases Sum.inr.inj same
        exact unfinished (completedExtra _ inside)
      have unusedNow : state.HandleUnused candidate := by
        intro field stored
        by_cases kept : state.accepted field = view.accepted field
        · exact unused field (kept ▸ stored)
        · obtain ⟨_, other, inside, rfl⟩ := acceptedChanged field kept
          obtain ⟨otherPayload, layoutEq⟩ := invariant.accepted_typed _ candidate stored
          have otherActor := graph.actor?_of_outputLayout_binding (owner := candidate.1)
            (payload := otherPayload) layoutEq
          have different : other ≠ event := fun same =>
            unfinished (same ▸ completedExtra other inside)
          obtain ⟨cut, otherReady, eventReady⟩ := together other inside
          obtain ⟨otherOwner, eventOwner, otherIs, eventIs, owners⟩ :=
            relaxed.ready_pair_actors otherReady eventReady different
          rw [otherActor] at otherIs
          rw [eventActor] at eventIs
          exact owners ((Option.some.inj otherIs).symm.trans
            (handleOwner.trans (Option.some.inj eventIs)))
      have active : id.1 ∉ state.config.defaulted := by
        change id.1 = owner at sender
        intro inactive
        apply quiescent event
        refine ⟨readyNow, ?_⟩
        rw [eventActor]
        simpa only [sender] using inactive
      exact ⟨_, runtime.handle_commitment_eq state id event candidate owner payload outputEq
        codeEq node readyNow timely active sender handleOwner vacantNow unusedNow⟩

/-- An authentic fresh call is accepted while its event is unfinished and timely.
Other completions must retain its receipt association, and automatic service
must be quiescent. The guarded result may be either success or public failure. -/
theorem freshServiceAcceptable_accepted_of_extends (relaxed : graph.RevealRelaxedOrdered)
    (state : State graph) (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph))
    (conforming : runtime.freshServiceAcceptable view message)
    (event : graph.EventId) (named : message.payload.call.event? graph = some event)
    {extra : List graph.EventId}
    (order : state.publicView.observation.completionOrder =
      view.observation.completionOrder ++ extra)
    (together : ∀ other ∈ extra, graph.ReadyTogether other event)
    (acceptedChanged : ∀ field, state.accepted field ≠ view.accepted field →
      view.accepted field = none ∧ ∃ other ∈ extra, field = .inr other)
    (unfinished : event ∉ state.config.cut.completed)
    (timely : state.WithinDeadline runtime event)
    (certified : ∀ fact ∈ message.payload.evidence.toList, fact.Holds state)
    (quiescent : ∀ event, ¬ state.AutomaticReady event)
    (invariant : state.BindingInvariant) :
    ∃ next, handle runtime state ⟨message.id, message.payload.call⟩ = some next := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | malformed raw => exact conforming.elim
  | commitment actual candidate =>
      change some actual = some event at named
      have actualEq : actual = event := Option.some.inj named
      subst actualEq
      exact bindingIncludable_accepted_of_extends runtime relaxed state view
        id actual candidate conforming.1 order together acceptedChanged unfinished timely
        quiescent invariant
  | opening actual candidate raw =>
      change some actual = some event at named
      have actualEq : actual = event := Option.some.inj named
      subst actualEq
      cases node : nodeView graph actual with
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨ready, _, certifiedPacket, sender, owned, associated, typed, _⟩ :=
            (runtime.freshServiceAcceptable_opening_iff view id actual owner payload binding checks
              outputEq codeEq node candidate raw evidence token).mp conforming
          have readyNow := ready_of_eventReady_extends order ready unfinished
          obtain ⟨value, rfl⟩ : ∃ value : L.Val payload, raw = ⟨payload, value⟩ := by
            rcases raw with ⟨kind, value⟩
            change kind = payload at typed
            cases typed
            exact ⟨value, rfl⟩
          have evidenceEq : evidence = some ⟨candidate, ⟨payload, value⟩⟩ := by
            cases evidence with
            | none => simp only [certifiedOpening, Bool.false_eq_true] at certifiedPacket
            | some fact =>
                simp only [certifiedOpening, decide_eq_true_eq] at certifiedPacket
                exact congrArg some certifiedPacket
          have verified : state.candidates.lookup candidate = .openable ⟨payload, value⟩ :=
            certified ⟨candidate, ⟨payload, value⟩⟩ (by simp [evidenceEq])
          have associatedNow : state.accepted binding.field = some candidate := by
            by_contra changed
            have vacant := (acceptedChanged binding.field
              (fun same => changed (same.trans associated))).1
            rw [associated] at vacant
            cases vacant
          have stored := invariant.opening_stored binding candidate value associatedNow verified
          have defined := EventCode.resolveOutput?_isSome binding checks true state.config.store
            (fun field read => state.config.read_available readyNow (by
              rw [← EventCode.readFields_cast outputEq (graph.nodes actual), codeEq]
              exact read))
          let result :=
            (EventCode.resolveOutput? binding checks true state.config.store).get defined
          have resolved : EventCode.resolveOutput? binding checks true state.config.store =
              some result := (Option.some_get defined).symm
          have eventActor : graph.actor? actual = some owner :=
            (EventCode.actor_cast outputEq (graph.nodes actual)).symm.trans
              (congrArg EventCode.actor codeEq)
          have active : id.1 ∉ state.config.defaulted := by
            intro inactive
            apply quiescent actual
            refine ⟨readyNow, ?_⟩
            rw [eventActor]
            simpa only [sender] using inactive
          exact ⟨_, runtime.handle_opening_eq state id actual candidate owner payload binding
            checks outputEq codeEq node readyNow timely active sender owned associatedNow value
            verified stored result resolved⟩
      | bind _ _ _ _ =>
          have absent := conforming.2.2.2
          rw [node] at absent
          exact absent.elim
      | sample _ _ _ _ =>
          have absent := conforming.2.2.2
          rw [node] at absent
          exact absent.elim

end Vegas.EventGraphRuntime
