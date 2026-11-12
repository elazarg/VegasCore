module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveRecall
public import Vegas.Pending.OpeningEvidence
public import Vegas.Pending.ExclusionCompletion

@[expose] public section

/-! # The event application under explicit network scheduling

One activation optionally transmits one packet. Private strategy memory is
absent from game actions. Fresh commitment material is fixed by submission. The
scheduler receives the authored envelope, while the player retains its own output.
No private staging command is a strategic action of this protocol.
Public default triggers bounded automatic completion in the same transition;
the graph configuration is the sole authority for default status.
An independent observation rule supplies partial knowledge of foreign pending
packets at activation; its samples are hidden from scheduling.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def reactiveApplication (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) : ReactiveApplication
      Player where
  State := State graph
  Payload := WitnessedPacket graph
  Submission := WitnessedSubmission graph
  EnvironmentCommand := EnvironmentCommand graph
  LocalObservation := PlayerView graph
  PublicObservation := PublicView graph
  packet state who known submission := submission.emit state who known
  submit state who submission :=
    submitStep (submission.call.register state who) who submission.call.packet
  handle state message := if message.payload.tokenValid then
      (handle timeouts state ⟨message.id, message.payload.call⟩).map State.drain else none
  environment state command := (environmentStep timeouts state command).map State.drain
  observePlayer := State.playerView
  observePublic := State.publicView
  observePending := leaks

/-- Pending observation samples change only private network knowledge. Every
supported activation has the same scheduler observation and recall entry. -/
theorem reactiveApplication_activation_schedulerInput (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (supported : next ∈ (execution.environmentStep
      ((reactiveApplication timeouts) leaks) (.activate who)).support) :
    (next.environmentRecall, next.observeEnvironment ((reactiveApplication timeouts) leaks)) =
      (execution.environmentRecall ++
        [⟨execution.observeEnvironment ((reactiveApplication timeouts) leaks), .activate who⟩],
        execution.observeEnvironment ((reactiveApplication timeouts) leaks)) := by
  obtain ⟨updated, sampled, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ sampled
  rfl

/-- Scheduling after an activation cannot distinguish its private pending
observation samples, for any scheduler law. -/
theorem reactiveApplication_activation_scheduler (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (execution left right : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (leftSupported : left ∈ (execution.environmentStep
      ((reactiveApplication timeouts) leaks) (.activate who)).support)
    (rightSupported : right ∈ (execution.environmentStep
      ((reactiveApplication timeouts) leaks) (.activate who)).support) :
    scheduler left.environmentRecall (left.observeEnvironment ((reactiveApplication timeouts)
      leaks)) =
      scheduler right.environmentRecall
        (right.observeEnvironment ((reactiveApplication timeouts) leaks)) := by
  have same := (reactiveApplication_activation_schedulerInput timeouts leaks execution left who
    leftSupported).trans (reactiveApplication_activation_schedulerInput timeouts leaks execution
      right who rightSupported).symm
  exact congrArg (fun input => scheduler input.1 input.2) same

/-- Inclusion first checks the packet's readiness token, then runs the
contract's call handler. A missing or foreign token is rejected. -/
theorem reactiveApplication_handle (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph)) :
    ((reactiveApplication timeouts) leaks).handle state message =
      if message.payload.tokenValid then
        (handle timeouts state ⟨message.id, message.payload.call⟩).map State.drain else none := rfl

theorem reactiveApplication_handle_of_tokenValid (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph))
    (valid : message.payload.tokenValid = true) :
    ((reactiveApplication timeouts) leaks).handle state message =
      (handle timeouts state ⟨message.id, message.payload.call⟩).map State.drain := by
  simp only [reactiveApplication_handle, valid, ite_true]

theorem reactiveApplication_handle_eq_some (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (message : Message Player (WitnessedPacket graph))
    (accepted : ((reactiveApplication timeouts) leaks).handle state message = some next) :
    message.payload.tokenValid = true ∧
      ∃ native, handle timeouts state ⟨message.id, message.payload.call⟩ = some native ∧
        native.drain = next := by
  rw [reactiveApplication_handle] at accepted
  split at accepted
  · exact ⟨by assumption, Option.map_eq_some_iff.mp accepted⟩
  · cases accepted

/-- An accepted inclusion runs the call handler followed by automatic completion. -/
theorem reactiveHandle_call {timeouts : EventTimeouts graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {state next : State graph} {message : Message Player (WitnessedPacket graph)}
    (accepted : ((reactiveApplication timeouts) leaks).handle state message = some next) :
    ∃ native, handle timeouts state ⟨message.id, message.payload.call⟩ = some native ∧
      native.drain = next :=
  (reactiveApplication_handle_eq_some timeouts leaks state next message accepted).2

/-- A call the contract rejects is rejected whatever its token. -/
theorem reactiveHandle_none {timeouts : EventTimeouts graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {state : State graph} {message : Message Player (WitnessedPacket graph)}
    (rejected : handle timeouts state ⟨message.id, message.payload.call⟩ = none) :
    ((reactiveApplication timeouts) leaks).handle state message = none := by
  rw [reactiveApplication_handle]
  split
  · simp only [rejected, Option.map_none]
  · rfl

theorem reactiveApplication_handle_of_not_tokenValid (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (message : Message Player (WitnessedPacket graph))
    (invalid : message.payload.tokenValid = false) :
    ((reactiveApplication timeouts) leaks).handle state message = none := by
  simp only [reactiveApplication_handle, invalid, Bool.false_eq_true, ite_false]

/-- Automatic service preserves both tables after native environment service. -/
theorem reactiveApplication_environment_tables (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (command : EnvironmentCommand graph)
    (supported : next ∈ (((reactiveApplication timeouts) leaks).environment state
      command).support) :
    next.accepted = state.accepted ∧ next.candidates = state.candidates := by
  change next ∈ ((environmentStep timeouts state command).map State.drain).support at supported
  obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ supported
  have prior := environmentStep_tables timeouts state native command moved
  exact ⟨native.drain_tables.1.trans prior.1, native.drain_tables.2.1.trans prior.2⟩

/-- A clock tick preserves a quiescent graph and its activation timestamps. -/
theorem reactiveApplication_tick_eq_pure (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (quiescent : ∀ query, ¬ state.AutomaticReady query) :
    ((reactiveApplication timeouts) leaks).environment state .advanceClock =
      PMF.pure { state with clock := state.clock + 1 } := by
  change (environmentStep timeouts state .advanceClock).map State.drain = _
  rw [environmentStep, PMF.pure_map]
  rw [State.drain_eq_of_clear]
  exact quiescent

/-- Sampling a completed event preserves a quiescent application, including automatic service. -/
theorem reactiveApplication_sample_eq_pure_of_completed
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (event : graph.EventId)
    (completed : event ∈ state.config.cut.completed)
    (quiescent : ∀ query, ¬ state.AutomaticReady query) :
    ((reactiveApplication timeouts) leaks).environment state (.executeSample event) =
      PMF.pure state := by
  change (environmentStep timeouts state (.executeSample event)).map State.drain = _
  rw [environmentStep_executeSample_of_not_ready timeouts state event
    (fun ready => ready.1 completed), PMF.pure_map, state.drain_eq_of_clear quiescent]

/-- Expiry of a completed event preserves a quiescent application, including automatic service. -/
theorem reactiveApplication_expire_eq_pure_of_completed
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (event : graph.EventId)
    (completed : event ∈ state.config.cut.completed)
    (quiescent : ∀ query, ¬ state.AutomaticReady query) :
    ((reactiveApplication timeouts) leaks).environment state (.expire event) = PMF.pure state := by
  change (environmentStep timeouts state (.expire event)).map State.drain = _
  rw [environmentStep_expire_of_not_ready timeouts state event
    (fun ready => ready.1 completed), PMF.pure_map, state.drain_eq_of_clear quiescent]

/-- Submission does not change the public contract state, so the emitted
token is the one issued in the state the sender saw. -/
theorem reactiveApplication_submit_publicView (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player) (submission : WitnessedSubmission graph) :
    (((reactiveApplication timeouts) leaks).submit state who submission).publicView =
      state.publicView := by
  change (submitStep (submission.call.register state who) who
    submission.call.packet).publicView = _
  rw [submitStep_publicView]
  exact (Submission.register_facts _ who state).2

theorem reactiveApplication_packet_token (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) :
    (((reactiveApplication timeouts) leaks).packet
      (((reactiveApplication timeouts) leaks).submit state who submission) who known
        submission).token = state.publicView.tokenFor submission.call.packet := by
  change (submission.emit _ who known).token = _
  rw [WitnessedSubmission.emit_token, reactiveApplication_submit_publicView]

/-- An evidence-free submission emits its call with the token issued in the
state the sender saw. -/
theorem reactiveApplication_packet_none (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (call : Submission graph) :
    ((reactiveApplication timeouts) leaks).packet
      (((reactiveApplication timeouts) leaks).submit state who ⟨call, .none⟩) who known
        ⟨call, .none⟩ = ⟨call.packet, none, state.publicView.tokenFor call.packet⟩ := by
  have token := reactiveApplication_packet_token timeouts leaks state who known ⟨call, .none⟩
  change WitnessedPacket.mk _ _ _ = _
  exact congrArg _ token

/-- A finitely branching leak rule makes every reactive environment law finite:
the graph's own environment steps already are. -/
instance reactiveApplication_finiteEnvironment (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) [leaks.FiniteSupport] :
    ((reactiveApplication timeouts) leaks).FiniteEnvironment where
  observePending_finite :=
    MessageNetwork.ObservationRule.FiniteSupport.support_finite (leaks := leaks)
  environment_finite state command := by
    change ((environmentStep timeouts state command).map State.drain).support.Finite
    rw [PMF.support_map]
    exact (environmentStep_support_finite timeouts state command).image _

/-- Atomically fix a fresh candidate and transmit its handle. Only the packet
field enters the network; the opening is private submission material. -/
def reactiveBinding (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload)) (serial : Nat) :
    ((reactiveApplication timeouts) leaks).Action where
  transmission := some ⟨⟨.commitment event (who, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩

theorem reactiveBinding_result (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : ((reactiveApplication timeouts) leaks).Execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let next := execution.respond ((reactiveApplication timeouts) leaks) who
      ((reactiveBinding timeouts) leaks who event payload result serial)
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

/-- **Complete play.** Every legal terminal state has completed every event:
the scheduler eventually samples, includes or expires each one. -/
def CompletesPlay (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) : Prop :=
  ∀ (control : ((reactiveApplication timeouts) leaks).Control),
    (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control) →
    (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).terminal
      (some control) →
    control.execution.application.config.cut.Terminal

end Vegas.EventGraphRuntime
