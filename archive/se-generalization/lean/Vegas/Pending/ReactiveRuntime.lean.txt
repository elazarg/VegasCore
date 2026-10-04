/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import Vegas.Pending.EventPlayerAction
import Vegas.Pending.EventBindingAction
import Vegas.Pending.OpeningEvidence
import Vegas.Pending.EventPublicState
import Interaction.MessageNetworkCounters

/-! # The event application under explicit network scheduling

One activation optionally transmits one packet. Private strategy memory is
absent from game actions. Fresh commitment material is fixed by submission. The
scheduler receives the authored envelope, while the player retains its own output.
No private staging command is a strategic action of this protocol.
An independent observation rule supplies partial knowledge of foreign pending
packets at activation; its samples are hidden from scheduling.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The semantic application observation used at an activation. -/
structure ReactivePlayerView (graph : Vegas.EventGraph Player L) where
  who : Player
  publicView : PublicView graph
  observation : graph.PlayerObservation who
  candidates : CandidateSlot graph → CommitmentCandidate (Raw L)

def reactiveApplication (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) : ReactiveApplication
      Player where
  State := State graph
  Payload := WitnessedPacket graph
  Submission := WitnessedSubmission graph
  EnvironmentCommand := EnvironmentCommand graph
  LocalObservation := ReactivePlayerView graph
  PublicObservation := PublicView graph
  packet state who known submission := submission.emit state who known
  submit state who submission :=
    submitStep (submission.call.register state who) who submission.call.packet
  handle state message := if message.payload.tokenValid then
      handle runtime state ⟨message.id, message.payload.call⟩ else none
  environment := environmentStep runtime
  observePlayer state who := ⟨who, state.publicView, graph.playerObserve who state.config,
    fun slot => state.candidates.lookup (who, slot)⟩
  observePublic := State.publicView
  observePending := leaks

/-- Inclusion first checks the packet's readiness token, then runs the
contract's call handler. A missing or foreign token is rejected. -/
theorem reactiveApplication_handle (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).handle state message =
      if message.payload.tokenValid then
        handle runtime state ⟨message.id, message.payload.call⟩ else none := rfl

theorem reactiveApplication_handle_of_tokenValid (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph))
    (valid : message.payload.tokenValid = true) :
    (runtime.reactiveApplication leaks).handle state message =
      handle runtime state ⟨message.id, message.payload.call⟩ := by
  simp only [reactiveApplication_handle, valid, ite_true]

theorem reactiveApplication_handle_eq_some (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (message : Message Player (WitnessedPacket graph))
    (accepted : (runtime.reactiveApplication leaks).handle state message = some next) :
    message.payload.tokenValid = true ∧
      handle runtime state ⟨message.id, message.payload.call⟩ = some next := by
  rw [reactiveApplication_handle] at accepted
  split at accepted
  · exact ⟨by assumption, accepted⟩
  · cases accepted

/-- An accepted inclusion ran the contract's call handler. -/
theorem reactiveHandle_call {runtime : EventGraphRuntime graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {state next : State graph} {message : Message Player (WitnessedPacket graph)}
    (accepted : (runtime.reactiveApplication leaks).handle state message = some next) :
    handle runtime state ⟨message.id, message.payload.call⟩ = some next :=
  (reactiveApplication_handle_eq_some runtime leaks state next message accepted).2

/-- A call the contract rejects is rejected whatever its token. -/
theorem reactiveHandle_none {runtime : EventGraphRuntime graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {state : State graph} {message : Message Player (WitnessedPacket graph)}
    (rejected : handle runtime state ⟨message.id, message.payload.call⟩ = none) :
    (runtime.reactiveApplication leaks).handle state message = none := by
  rw [reactiveApplication_handle]
  split
  · exact rejected
  · rfl

theorem reactiveApplication_handle_of_not_tokenValid (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph))
    (invalid : message.payload.tokenValid = false) :
    (runtime.reactiveApplication leaks).handle state message = none := by
  simp only [reactiveApplication_handle, invalid, Bool.false_eq_true, ite_false]

/-- Submission does not change the public contract state, so the emitted
token is the one issued in the state the sender saw. -/
theorem reactiveApplication_submit_publicView (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player) (submission : WitnessedSubmission graph) :
    ((runtime.reactiveApplication leaks).submit state who submission).publicView =
      state.publicView := by
  change (submitStep (submission.call.register state who) who
    submission.call.packet).publicView = _
  rw [submitStep_publicView]
  exact (Submission.register_facts _ who state).2.2

theorem reactiveApplication_packet_token (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) :
    ((runtime.reactiveApplication leaks).packet
      ((runtime.reactiveApplication leaks).submit state who submission) who known
        submission).token = state.publicView.tokenFor submission.call.packet := by
  change (submission.emit _ who known).token = _
  rw [WitnessedSubmission.emit_token, reactiveApplication_submit_publicView]

/-- An evidence-free submission emits its call with the token issued in the
state the sender saw. -/
theorem reactiveApplication_packet_none (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (call : Submission graph) :
    (runtime.reactiveApplication leaks).packet
      ((runtime.reactiveApplication leaks).submit state who ⟨call, .none⟩) who known
        ⟨call, .none⟩ = ⟨call.packet, none, state.publicView.tokenFor call.packet⟩ := by
  have token := reactiveApplication_packet_token runtime leaks state who known ⟨call, .none⟩
  change WitnessedPacket.mk _ _ _ = _
  exact congrArg _ token

omit [DecidableEq Player] in
/-- A finitely branching leak rule makes every reactive environment law finite:
the graph's own environment steps already are. -/
instance reactiveApplication_finiteEnvironment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) [leaks.FiniteSupport] :
    (runtime.reactiveApplication leaks).FiniteEnvironment where
  observePending_finite :=
    MessageNetwork.ObservationRule.FiniteSupport.support_finite (leaks := leaks)
  environment_finite := runtime.environmentStep_support_finite

/-- Atomically fix a fresh candidate and transmit its handle. Only the packet
field enters the network; the opening is private submission material. -/
def reactiveBinding (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload)) (serial : Nat) :
    (runtime.reactiveApplication leaks).Action where
  transmission := some ⟨⟨.commitment event (who, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩

/-- A call the contract accepts at a state is ready there, so a packet
emitted from that public view carries a valid token. -/
theorem tokenFor_tokenValid_of_handle (runtime : EventGraphRuntime graph)
    (state next : State graph) (id : MessageId Player) (call : Payload graph)
    (evidence : Option (OpeningFact graph))
    (accepted : handle runtime state ⟨id, call⟩ = some next) :
    (WitnessedPacket.mk call evidence (state.publicView.tokenFor call)).tokenValid = true := by
  obtain ⟨event, named, ready, _⟩ := handle_config_mem_step runtime state next _ accepted
  rw [state.publicView_tokenFor_of_ready call event named ready]
  exact WitnessedPacket.tokenValid_of_event call evidence event named

/-- A packet whose token was issued in the state it is included at is handled
exactly as its call: the contract accepts only ready calls, whose tokens are
issued there. -/
theorem reactiveApplication_handle_of_current_token (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph))
    (current : message.payload.token = state.publicView.tokenFor message.payload.call) :
    (runtime.reactiveApplication leaks).handle state message =
      handle runtime state ⟨message.id, message.payload.call⟩ := by
  cases accepted : handle runtime state ⟨message.id, message.payload.call⟩ with
  | none => exact reactiveHandle_none accepted
  | some next =>
      have valid := tokenFor_tokenValid_of_handle runtime state next message.id
        message.payload.call message.payload.evidence accepted
      rw [← current] at valid
      rw [reactiveApplication_handle_of_tokenValid runtime leaks state message valid, accepted]

/-- An evidence-free submission enters the network as its call with the token
issued in the state the sender saw. -/
theorem respond_submit_lookup (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (call : Submission graph) (serials : execution.network.SerialsBeforeNext) :
    (execution.respond (runtime.reactiveApplication leaks) who
      ⟨some ⟨call, .none⟩⟩).network.lookup (who, execution.network.nextSerial who) =
      some ⟨(who, execution.network.nextSerial who),
        ⟨call.packet, none, execution.application.publicView.tokenFor call.packet⟩⟩ := by
  simpa only [ReactiveApplication.Execution.respond, reactiveApplication_packet_none] using
    serials.lookup_submit who
      ⟨call.packet, none, execution.application.publicView.tokenFor call.packet⟩

/-- An evidence-free submission for a ready event enters the network with that
event's readiness token. -/
theorem respond_submit_lookup_of_ready (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (call : Submission graph) (serials : execution.network.SerialsBeforeNext)
    (event : graph.EventId) (named : call.packet.event? graph = some event)
    (ready : execution.application.config.cut.Ready event) :
    (execution.respond (runtime.reactiveApplication leaks) who
      ⟨some ⟨call, .none⟩⟩).network.lookup (who, execution.network.nextSerial who) =
      some ⟨(who, execution.network.nextSerial who), ⟨call.packet, none, some ⟨event⟩⟩⟩ := by
  rw [← execution.application.publicView_tokenFor_of_ready call.packet event named ready]
  exact respond_submit_lookup runtime leaks execution who call serials

/-- A compiled binding response at a ready event enters the network with the
event's readiness token. -/
theorem reactiveBinding_lookup (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (serials : execution.network.SerialsBeforeNext)
    (ready : execution.application.config.cut.Ready event) :
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload result serial)).network.lookup
        (who, execution.network.nextSerial who) =
      some ⟨(who, execution.network.nextSerial who),
        ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩⟩ := by
  rw [← execution.application.publicView_tokenFor_of_ready
    (.commitment event (who, .prepared serial)) event rfl ready]
  exact respond_submit_lookup runtime leaks execution who _ serials

theorem reactiveBinding_result (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let next := execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload result serial)
    next.application.bindingResult (who, .prepared serial) payload = result := by
  cases result with
  | failure =>
      change (submitStep execution.application who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh]
  | success value =>
      change (submitStep
        (Submission.register ⟨.commitment event (who, .prepared serial), some ⟨payload, value⟩⟩
          execution.application who) who (.commitment event (who, .prepared
            serial))).bindingResult
            (who, .prepared serial) payload = .success value
      simp only [Submission.register, ↓reduceIte]
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, CommitmentCandidates.lookup_prepare_self,
        fresh, Raw.as?_mk, Option.elim_some]

/-- The environment receives the same envelope and public application state
for all private binding meanings, including an unopenable candidate. -/
theorem reactiveBinding_observation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload first serial)).observeEnvironment
        (runtime.reactiveApplication leaks) =
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload second serial)).observeEnvironment
        (runtime.reactiveApplication leaks) := by
  have unchanged (result : PublicationResult (L.Val payload)) :
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload result serial)).application.publicView =
          execution.application.publicView := by
    change (submitStep (Submission.register _ execution.application who) who _).publicView = _
    rw [submitStep_publicView]
    exact (Submission.register_facts _ who execution.application).2.2
  change ReactiveApplication.EnvironmentView.mk (app := (runtime.reactiveApplication leaks)) _
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload first serial)).application.publicView _ =
    ReactiveApplication.EnvironmentView.mk (app := (runtime.reactiveApplication leaks)) _
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload second serial)).application.publicView _
  rw [unchanged first, unchanged second]
  simp only [ReactiveApplication.Execution.respond, reactiveBinding,
    reactiveApplication_packet_none]

end Vegas.EventGraphRuntime
