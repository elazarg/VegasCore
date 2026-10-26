/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseRequestWindow
import Vegas.Pending.PhaseCountedRequestResolution
import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseOwnCount
import Vegas.Pending.PhaseCountUniqueness
import Interaction.ReactiveOwnerSelection
import Interaction.ReactiveReceiptBoundary
import Interaction.ReactiveTrafficIdentity

/-! # Protected binding delivery along actual stopped windows

Actual count-clean packets remain pending while their request survives. The
inclusion contract bounds every pending prefix; the original readiness stamp
and the first-response inclusion margin then force timely acceptance at the
request window endpoint, including phase retirement and rollback.
-/

noncomputable section
namespace Vegas.EventGraphRuntime.PhaseService
open EventGraph Interaction GameTheory.Math.Probability GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
local notation "app" => phaseApplication runtime leaks

/-- A genuine pending, count-clean response cannot outlive its protected
inclusion budget while its original request remains active. -/
theorem pending_response_clock_bound (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some current))
    (bound : graph.EventId → Nat)
    (inclusion : ProtectedInclusionAt runtime leaks current.execution bound)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : current.execution.application.SeedRequest owner coordinate)
    (clean : PhaseCount.OwnCountClean runtime leaks owner current.execution)
    (earlier later : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (recalled : current.execution.recall owner = earlier ++ entry :: later)
    (message : Message Player (CommitAttemptPacket graph))
    (sent : entry.emitted = some message) (sender : message.sender = owner)
    (address : message.payload.attempt = coordinate.attempt)
    (named : message.payload.packet.call.event? graph = some coordinate.event)
    (ready : entry.beforeView.application.1.publicView.EventReady coordinate.event)
    (pending : message ∈ current.execution.network.pending) :
    current.execution.application.current.native.clock ≤
      entry.beforeView.application.1.publicView.clock + bound coordinate.event := by
  by_contra late
  have elapsed : entry.beforeView.application.1.publicView.clock + bound coordinate.event <
      current.execution.application.current.native.clock := Nat.lt_of_not_ge late
  have inputs := (app).history_inputRecall initial horizon scheduler trace
  have input : message ∈ current.execution.network.inputs :=
    ((app).retained_envelopes_mem_inputs current.execution
      ((app).history_provenance initial horizon scheduler trace) inputs).pending message pending
  have unique : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor runtime leaks other coordinate message.id := by
    intro other member emitted
    obtain ⟨packet, packetSent, author, attempt, event, different⟩ := emitted
    have remembered : other ∈ current.execution.recall owner := by
      rw [recalled]
      rcases List.mem_append.mp member with left | right
      · exact List.mem_append_left _ left
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
    have output : packet ∈ (app).outputs (current.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨other, remembered, packetSent⟩
    rw [← inputs owner] at output
    have packetInput := (List.mem_filter.mp output).1
    have authored : packet.sender = owner := author.trans sender
    have sameEvent : PhaseCount.event? message.payload = PhaseCount.event? packet.payload := by
      simp only [PhaseCount.event?, address, named, attempt, event, Option.map_some]
    have equal := PhaseCount.Permits.eq_of_same_event
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input sender))
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 packet packetInput authored))
      input packetInput
      (fun left leftInput right rightInput same =>
        (app).input_identifier_injective_history initial horizon scheduler current trace
          left right leftInput rightInput same)
      (sender.trans authored.symm) sameEvent
    exact different (congrArg Message.id equal.symm)
  obtain ⟨accepted, received⟩ := inclusion coordinate owner request.2.2.2.1 earlier later entry
    message recalled sent sender address named ready unique request.1.symm request.2.2.1.1 elapsed
  exact (app).pending_identifier_not_receipted initial horizon scheduler current trace message
    pending accepted received

/-- Removing a genuine timely counted binding resolves its own attempt-event
coordinate, including the phase retirement caused by that inclusion. -/
theorem pending_binding_environment (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some current))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = owner)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (request : current.execution.application.SeedRequest owner ⟨message.payload.attempt, event⟩)
    (clean : PhaseCount.OwnCountClean runtime leaks owner current.execution)
    (timely : current.execution.application.current.native.WithinDeadline runtime event)
    (pending : message ∈ current.execution.network.pending)
    (next : (app).Execution) (command : (app).Command)
    (moved : next ∈ (current.execution.environmentStep app command).support) :
    message ∈ next.network.pending ∨
      (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph).Resolved next.application := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have retained := (app).retained_envelopes_mem_inputs current.execution
    ((app).history_provenance initial horizon scheduler trace)
    ((app).history_inputRecall initial horizon scheduler trace)
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_ordered plan draw) trace
  obtain ⟨_native, after, _handled, _complete, _accepted, _normalized, handled⟩ :=
    PhaseCount.binding_accepted_of_own_history runtime leaks plan inputs horizon scheduler trace
      owner clean.2 message (retained.pending message pending) sender event candidate call
        (by rwa [sender]) timely
  have named : message.payload.packet.call.event? graph = some event := by rw [call]; rfl
  have resolved := PhaseRuntimeState.handle_event_resolved runtime leaks
    current.execution.application after ordered message event named handled
  apply (app).environmentStep_cases current.execution next command moved
    (predicate := fun _ next => message ∈ next.network.pending ∨
      (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph).Resolved next.application)
  · exact Or.inl pending
  · intro who selected _
    exact Or.inl pending
  · intro id
    rcases MessagePool.mem_removeFirst_or_found id current.execution.network.pending message pending
      with kept | found
    · apply Or.inl
      change message ∈ (current.execution.includePending app id).network.pending
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases current.execution.network.lookup id with
      | none => exact pending
      | some packet => exact kept
    · apply Or.inr
      change (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph).Resolved
        (current.execution.includePending app id).application
      change current.execution.network.lookup id = some message at found
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      simp only [found, handled, Option.getD_some]
      exact resolved
  · intro command state _
    exact Or.inl pending

/-- A protected binding remains pending through every proper prefix of its
request window. The original readiness timestamp survives the same interval. -/
theorem pending_binding_prefix [Fintype Player] (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (bound : graph.EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler bound)
    (start : (app).Control)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = owner) (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (entry : (app).PlayerEntry) (earlier later : List (app).PlayerEntry)
    (recalled : start.execution.recall owner = earlier ++ entry :: later)
    (sent : entry.emitted = some message)
    (ready : entry.beforeView.application.1.publicView.EventReady event)
    (entered : Nat)
    (stamp : start.execution.application.current.native.activatedAt event = some entered)
    (deadlineMargin : entry.beforeView.application.1.publicView.clock - entered + bound event <
      runtime.deadline event)
    (pending : message ∈ start.execution.network.pending)
    {target : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).State}
    (final : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace target)
    (kept : TracePrefix prior final)
    (requests : ∀ {state} (middle : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      TracePrefix prior middle → TracePrefix middle final →
        ∃ control, state = some control ∧ control.execution.application.SeedRequest owner
          ⟨message.payload.attempt, event⟩) :
    ∃ current, target = some current ∧ message ∈ current.execution.network.pending ∧
      current.execution.application.current.native.activatedAt event = some entered := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  revert requests
  induction kept with
  | refl => intro _; exact ⟨start, rfl, pending, stamp⟩
  | @extend source target middle kept joint legal moved ih =>
      intro requests
      obtain ⟨before, atBefore, wasPending, wasActivated⟩ := ih (fun history retained suffix =>
        requests history retained (.extend suffix joint legal moved))
      subst source
      obtain ⟨after, atAfter, requestAfter⟩ := requests _ (.extend kept joint legal moved) .refl
      subst target
      have requestBefore := (requests middle kept (.extend .refl joint legal moved)).choose_spec
      have beforeEq := Option.some.inj requestBefore.1
      have requested : before.execution.application.SeedRequest owner
          ⟨message.payload.attempt, event⟩ := beforeEq ▸ requestBefore.2
      have raw := menu.toRawTrace initial horizon scheduler middle
      have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
        initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) middle
      have ownClean : PhaseCount.OwnCountClean runtime leaks owner before.execution :=
        ⟨clean.1, fun packet member _ => clean.2 packet member⟩
      obtain ⟨tail, tailEq⟩ := (app).reaches_recall_prefix initial horizon scheduler
        (menu.reaches_raw initial horizon scheduler kept.reachesWithin) start before rfl rfl owner
      have remembered : before.execution.recall owner = earlier ++ entry :: (later ++ tail) := by
        rw [← tailEq, recalled, List.append_assoc, List.cons_append]
      have named : message.payload.packet.call.event? graph = some event := by rw [call]; rfl
      have clockBound := pending_response_clock_bound runtime leaks initial horizon scheduler
        before raw bound (inclusion before raw) owner ⟨message.payload.attempt, event⟩ requested
          ownClean earlier (later ++ tail) entry remembered message sent sender rfl named ready
            wasPending
      change before.execution.application.current.native.clock ≤
        entry.beforeView.application.1.publicView.clock + bound event at clockBound
      have timely : before.execution.application.current.native.WithinDeadline runtime event := by
        simp only [State.WithinDeadline, wasActivated]
        omega
      have valid := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler raw
      obtain ⟨draw, valid⟩ := valid
      have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
        (fun state supported => by
          obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact PhaseRuntimeState.initial_ordered plan draw) raw
      have actual : some after ∈ ((app).transition initial horizon scheduler (some before)
          joint).support := moved
      obtain ⟨_ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).transition
        initial horizon scheduler before after joint actual draw valid ordered
          (requested.1.symm.trans requestAfter.1)
      refine ⟨after, rfl, ?_, progress.activated event entered wasActivated requestAfter.2.2.1.1⟩
      cases actor : before.actor with
      | some who =>
          simp only [ReactiveApplication.transition, actor, PMF.mem_support_pure_iff] at actual
          have same := congrArg ReactiveApplication.Control.execution (Option.some.inj actual)
          rw [same]
          exact (app).respond_pending_mono before.execution who _ wasPending
      | none =>
          cases rounds : before.remaining with
          | zero =>
              simp only [ReactiveApplication.transition, actor, rounds,
                PMF.mem_support_pure_iff] at actual
              cases Option.some.inj actual
              exact wasPending
          | succ remaining =>
              simp only [ReactiveApplication.transition, actor, rounds,
                PMF.mem_support_bind_iff] at actual
              obtain ⟨command, _selected, supported⟩ := actual
              obtain ⟨execution, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
              have same : after.execution = execution :=
                congrArg ReactiveApplication.Control.execution (Option.some.inj equal).symm
              rcases pending_binding_environment runtime leaks plan inputs horizon scheduler before
                raw owner message sender event candidate call requested ownClean timely wasPending
                  execution command reached with stays | resolved
              · rwa [same]
              · exact (CommitAttemptEvent.Resolved.not_request _ _ resolved owner
                  (by rwa [← same])).elim

end Vegas.EventGraphRuntime.PhaseService

namespace Vegas.EventGraphRuntime.PhaseService
open EventGraph Interaction GameTheory.Math.Probability GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol
variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
local notation "app" => phaseApplication runtime leaks

/-- Actual stopped counted play accepts its protected binding packet at the
first request loss. Completion rules out truncation; inclusion supplies the
endpoint's deadline bound instead of assuming it. -/
theorem protected_binding_window_accepts (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler bound)
    (completes : CompletesPlay runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler)
    (profile : ∀ who, ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).BehavioralPolicy who)
    (start : (app).Control)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = owner) (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (entry : (app).PlayerEntry) (earlier later : List (app).PlayerEntry)
    (recalled : start.execution.recall owner = earlier ++ entry :: later)
    (sent : entry.emitted = some message)
    (ready : entry.beforeView.application.1.publicView.EventReady event)
    (entered : Nat)
    (stamp : start.execution.application.current.native.activatedAt event = some entered)
    (deadlineMargin : entry.beforeView.application.1.publicView.clock - entered + bound event <
      runtime.deadline event)
    (pending : message ∈ start.execution.network.pending)
    (requested : start.execution.application.SeedRequest owner ⟨message.payload.attempt, event⟩)
    (final : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).History)
    (last : (app).Control) (atFinal : final.state = some last)
    (supported : final ∈ (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).runBehavioralUntil
        ((PhaseCount.onePacketMenu runtime leaks bounds).bounded
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).wellFoundedHistories
        profile (fun history => ∀ current, history.state = some current →
          ¬ current.execution.application.SeedRequest owner ⟨message.payload.attempt, event⟩)
        ⟨some start, prior⟩).support) :
    (message.id, true) ∈ last.execution.receipts ∧
      ∃ (before : (app).Control)
        (beforeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before)),
        TracePrefix prior beforeTrace ∧ TracePrefix beforeTrace final.trace ∧
        before.actor = none ∧ before.execution.application.SeedRequest owner
          ⟨message.payload.attempt, event⟩ ∧ message ∈ before.execution.network.pending ∧
        before.execution.application.current.native.activatedAt event = some entered ∧
        before.execution.application.current.native.WithinDeadline runtime event ∧
        last.execution ∈ (before.execution.environmentStep app (.include message.id)).support := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let model := menu.information initial horizon scheduler
  let stopped : (menu.protocol initial horizon scheduler).History → Prop := fun history =>
    ∀ current, history.state = some current →
      ¬ current.execution.application.SeedRequest owner ⟨message.payload.attempt, event⟩
  let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
  obtain ⟨before, beforeTrace, retained, toFinal, _idle, requestBefore, lost, command,
      _selected, moved, _remaining, _actor⟩ := request_window_last_environment runtime leaks
    menu initial horizon scheduler completes profile ⟨some start, prior⟩ start rfl owner
      ⟨message.payload.attempt, event⟩ requested final last atFinal supported
  have shorter : beforeTrace.length < final.trace.length := by
    apply lt_of_le_of_ne toFinal.length_le
    intro same
    have equal := toFinal.eq_of_length same
    have states := congrArg History.state equal
    change some before = final.state at states
    rw [atFinal] at states
    exact lost (Option.some.inj states ▸ requestBefore)
  have requests : ∀ {state} (middle : (menu.protocol initial horizon scheduler).Trace state),
      TracePrefix prior middle → TracePrefix middle beforeTrace →
        ∃ control, state = some control ∧ control.execution.application.SeedRequest owner
          ⟨message.payload.attempt, event⟩ := by
    intro state middle kept ending
    have unhalted := model.runBehavioralUntil_support_first certificate profile stopped
      ⟨some start, prior⟩ final supported ⟨state, middle⟩ kept (ending.trans toFinal)
        (lt_of_le_of_lt ending.length_le shorter)
    change ¬ ∀ current, state = some current →
      ¬ current.execution.application.SeedRequest owner ⟨message.payload.attempt, event⟩ at unhalted
    push Not at unhalted
    exact unhalted
  obtain ⟨current, equal, pendingBefore, stampBefore⟩ := pending_binding_prefix runtime leaks bounds
    plan inputs horizon scheduler bound inclusion start prior owner message sender event candidate
      call entry earlier later recalled sent ready entered stamp deadlineMargin pending beforeTrace
        retained requests
  cases Option.some.inj equal
  have raw := menu.toRawTrace initial horizon scheduler beforeTrace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) beforeTrace
  have ownClean : PhaseCount.OwnCountClean runtime leaks owner before.execution :=
    ⟨clean.1, fun packet member _ => clean.2 packet member⟩
  obtain ⟨tail, tailEq⟩ := (app).reaches_recall_prefix initial horizon scheduler
    (menu.reaches_raw initial horizon scheduler retained.reachesWithin) start before rfl rfl owner
  have remembered : before.execution.recall owner = earlier ++ entry :: (later ++ tail) := by
    rw [← tailEq, recalled, List.append_assoc, List.cons_append]
  have named : message.payload.packet.call.event? graph = some event := by rw [call]; rfl
  have clockBound := pending_response_clock_bound runtime leaks initial horizon scheduler before
    raw bound (inclusion before raw) owner ⟨message.payload.attempt, event⟩ requestBefore ownClean
      earlier (later ++ tail) entry remembered message sent sender rfl named ready pendingBefore
  change before.execution.application.current.native.clock ≤
    entry.beforeView.application.1.publicView.clock + bound event at clockBound
  have timely : before.execution.application.current.native.WithinDeadline runtime event := by
    simp only [State.WithinDeadline, stampBefore]
    omega
  have input := ((app).retained_envelopes_mem_inputs before.execution
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)).pending message pendingBefore
  have accepted := PhaseCount.timely_request_loss_accepts runtime leaks plan ordered inputs horizon
    scheduler before raw owner ⟨message.payload.attempt, event⟩
      (fun packet member authored => (PhaseCount.permits_eq_true_iff _ _).mp
        (ownClean.2 packet member authored)) requestBefore timely message input sender rfl named
      last.execution command moved lost
  refine ⟨accepted.2.2.2.1, before, beforeTrace, retained, toFinal, _idle, requestBefore,
    pendingBefore, stampBefore, timely, ?_⟩
  rwa [← accepted.1]

end Vegas.EventGraphRuntime.PhaseService
