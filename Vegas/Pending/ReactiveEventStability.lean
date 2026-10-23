/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveEntryStability
import Vegas.Pending.ReactiveFreshCallAcceptance
import Vegas.EventGraph.RevealRelaxation
import Vegas.EventGraph.BarrierInformation
import Vegas.EventGraph.Commutation

/-! # What a recorded view of a ready event keeps while the event is unfinished

When several events can be ready at once, a recorded response's public view
does not stay current: other ready events may complete in the meantime. Each
completion is a step at an event that was ready together with every event
still unfinished and ready before it. So, for an event a recorded view saw
ready and that is still unfinished, every event completed since was ready
together with it, its activation time is unchanged, and accepted handles have
changed only at the outputs of those events, which had none before
(`Vegas.EventGraphRuntime.EntryEventStable`, at every legal history by
`Vegas.EventGraphRuntime.entryEventStable_history`). This holds for every
graph, scheduler and arbitrary responses; graph certificates then say which
events can be ready together.

On a graph whose simultaneously ready events have different actors, a
commitment that was includable on the view its author saw stays includable
while its event is unfinished and within its deadline
(`Vegas.EventGraphRuntime.bindingIncludable_accepted_of_extends`): the other
completed events belong to other owners, so its event's output field stays
vacant and no other event can have consumed the author's handle. On a
reveal, the events completed since are independent reveals, which its guards
do not read, so every acceptable fresh call is accepted at such a state
(`Vegas.EventGraphRuntime.freshServiceAcceptable_accepted_of_extends`).
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

/-- Two events are ready together at some cut. -/
def ReadyTogether (graph : Vegas.EventGraph Player L) (first second : graph.EventId) : Prop :=
  ∃ cut : graph.order.Cut, cut.Ready first ∧ cut.Ready second

/-- A binding node's actor is its output's owner. -/
theorem EventCode.actor_eq_of_binding {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} :
    ∀ {output : EventField Player L} (code : EventCode layout output) {owner : Player}
      {payload : L.Ty}, output = .binding owner payload → code.actor = some owner
  | _, .bind _ _, _, _, same => by cases same; rfl
  | _, .resolve .., _, _, same => by cases same
  | _, .sample .., _, _, same => by cases same

/-- An event with a binding output is acted on by the binding's owner. -/
theorem actor?_of_outputLayout_binding (graph : Vegas.EventGraph Player L)
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    (binding : graph.outputLayout event = .binding owner payload) :
    graph.actor? event = some owner :=
  EventCode.actor_eq_of_binding (graph.nodes event) binding

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

omit [DecidableEq Player] in
/-- Either the configuration, accepted handles and activation times are
unchanged, or one ready event completes, activation times are refreshed around
it, and accepted handles change at most at its output. -/
def CompletionStep (before after : State graph) : Prop :=
  (after.config = before.config ∧ after.accepted = before.accepted ∧
      after.activatedAt = before.activatedAt) ∨
    ∃ event, ∃ (ready : before.config.cut.Ready event) (action : graph.Action event),
      after.config ∈ (before.config.step event ready action).support ∧
      after.activatedAt = State.refreshActivated after.config before.clock before.activatedAt ∧
      ∀ field, after.accepted field ≠ before.accepted field →
        before.accepted field = none ∧ field = .inr event

omit [DecidableEq Player] in
theorem CompletionStep.refl (state : State graph) : CompletionStep state state :=
  Or.inl ⟨rfl, rfl, rfl⟩

/-- An accepted commitment fills a vacant output field. -/
theorem handle_commitment_vacant (state next : State graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    state.accepted (.inr event) = none := by
  by_contra occupied
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event with
      | resolve | sample => simp [handle, ready, timely, view] at accepted
      | bind owner payload outputEq codeEq =>
          simp [handle, ready, timely, view, occupied] at accepted
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

theorem completionStep_handle (state next : State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) : CompletionStep state next := by
  obtain ⟨event, named, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  refine Or.inr ⟨event, ready, action, member,
    (handle_clock_activated runtime state next message accepted).2, ?_⟩
  intro field changed
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment actual candidate =>
      have actualEq : actual = event := Option.some.inj named
      subst actualEq
      have tables := (handle_commitment_tables runtime state next id actual candidate accepted).2.1
      by_cases other : field = .inr actual
      · subst other
        exact ⟨handle_commitment_vacant runtime state next id actual candidate accepted, rfl⟩
      · exact (changed (by rw [tables, Function.update_of_ne other])).elim
  | opening actual candidate raw =>
      have tables := (handle_resolution_tables runtime state next _ (by intros; simp)
        accepted).1
      exact (changed (by rw [tables])).elim

omit [DecidableEq Player] in
theorem completionStep_environmentStep (state next : State graph)
    (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    CompletionStep state next := by
  have accepted := (environmentStep_tables runtime state next command member).1
  have unchanged : ∀ field, next.accepted field ≠ state.accepted field → False :=
    fun field changed => changed (by rw [accepted])
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at member
      subst next
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | executeSample event =>
      rcases (environmentStep_executeSample_config_activated runtime state next event member).2
        with ⟨configEq, activatedEq⟩ | ⟨ready, action, stepped, activatedEq⟩
      · exact Or.inl ⟨configEq, accepted, activatedEq⟩
      · exact Or.inr ⟨event, ready, action, stepped, activatedEq,
          fun field changed => (unchanged field changed).elim⟩
  | expire event =>
      rcases (environmentStep_expire_config_activated runtime state next event member).2
        with ⟨configEq, activatedEq⟩ | ⟨ready, action, stepped, activatedEq⟩
      · exact Or.inl ⟨configEq, accepted, activatedEq⟩
      · exact Or.inr ⟨event, ready, action, stepped, activatedEq,
          fun field changed => (unchanged field changed).elim⟩

/-- Every scheduler command takes one completion step of the application. -/
theorem completionStep_reactive_environmentStep
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    CompletionStep execution.application next.application := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact CompletionStep.refl _
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact CompletionStep.refl _
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change CompletionStep execution.application
        (execution.includePending (runtime.reactiveApplication leaks) id).application
      unfold ReactiveApplication.Execution.includePending
      cases execution.network.includePending id with
      | mk envelope network =>
          cases envelope with
          | none => exact CompletionStep.refl _
          | some envelope =>
              change CompletionStep execution.application
                (((runtime.reactiveApplication leaks).handle execution.application
                  envelope).getD execution.application)
              cases accepted : (runtime.reactiveApplication leaks).handle execution.application
                  envelope with
              | none => exact CompletionStep.refl _
              | some next =>
                  exact completionStep_handle runtime _ next _ (reactiveHandle_call accepted)
  | application command =>
      rw [PMF.support_map] at supported
      obtain ⟨state, changed, rfl⟩ := supported
      exact completionStep_environmentStep runtime _ state command changed

/-- A recorded response that saw `event` ready, while `event` is unfinished:
the events completed since were ready together with it, its activation time is
unchanged, and accepted handles changed only at the outputs of those events. -/
def EntryEventStable (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ event,
    entry.beforeView.application.publicView.EventReady event →
    event ∉ execution.application.config.cut.completed →
    ∃ extra, execution.application.publicView.observation.completionOrder =
        entry.beforeView.application.publicView.observation.completionOrder ++ extra ∧
      (∀ other ∈ extra, graph.ReadyTogether other event) ∧
      (∀ owner, graph.actor? event = some owner → ∀ entered,
        entry.beforeView.application.publicView.activatedAt event = some entered →
        execution.application.activatedAt event = some entered) ∧
      ∀ field, execution.application.accepted field ≠
          entry.beforeView.application.publicView.accepted field →
        entry.beforeView.application.publicView.accepted field = none ∧
          ∃ other ∈ extra, field = .inr other

omit [DecidableEq Player] in
/-- A view's ready event that is unfinished at a state whose completion order
extends the view's is ready at that state. -/
theorem ready_of_eventReady_extends {view : PublicView graph} {state : State graph}
    {event : graph.EventId} {extra : List graph.EventId}
    (order : state.publicView.observation.completionOrder =
      view.observation.completionOrder ++ extra)
    (ready : view.EventReady event) (unfinished : event ∉ state.config.cut.completed) :
    state.config.cut.Ready event := by
  refine (state.publicView_eventReady event).mp ⟨fun member => unfinished
    ((state.config.history_exact event).mp member), fun predecessor inside => ?_⟩
  rw [order]
  exact List.mem_append_left _ (ready.2 predecessor inside)

/-- Recorded views of ready events keep these facts, for every scheduler and
arbitrary responses. -/
theorem entryEventStable_serviceInvariant
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (EntryEventStable runtime leaks) where
  respond execution who action valid := by
    let app := runtime.reactiveApplication leaks
    have configEq := (runtime.reactive_respond_application leaks execution who action).1
    have publicEq := (runtime.reactive_respond_application leaks execution who action).2
    intro observer entry member event ready unfinished
    have acceptedEq : (execution.respond app who action).application.accepted =
        execution.application.accepted := congrArg PublicView.accepted publicEq
    have activatedEq : (execution.respond app who action).application.activatedAt =
        execution.application.activatedAt := congrArg PublicView.activatedAt publicEq
    rw [publicEq, acceptedEq, activatedEq]
    rw [configEq] at unfinished
    rcases app.respond_entry_origin execution who observer action entry member with
      prior | ⟨_, fresh⟩
    · exact valid observer entry prior event ready unfinished
    · rw [fresh]
      refine ⟨[], (List.append_nil _).symm, fun _ member => (List.not_mem_nil member).elim,
        fun _ _ _ same => same, ?_⟩
      intro field changed
      exact (changed rfl).elim
  environment execution next command valid _ reached := by
    let app := runtime.reactiveApplication leaks
    have recallEq := app.environmentStep_recall execution next command reached
    intro observer entry member event ready unfinished
    rw [recallEq] at member
    have stepped := completionStep_reactive_environmentStep runtime leaks execution next command
      reached
    have unfinishedBefore : event ∉ execution.application.config.cut.completed := by
      intro completed
      rcases stepped with ⟨configEq, _, _⟩ | ⟨completedEvent, completedReady, action, member,
          _, _⟩
      · exact unfinished (configEq ▸ completed)
      · rw [execution.application.config.step_cut completedEvent completedReady action _ member,
          EventOrder.Cut.mem_complete] at unfinished
        exact unfinished (Or.inr completed)
    obtain ⟨extra, order, together, activated, acceptedChanged⟩ :=
      valid observer entry member event ready unfinishedBefore
    rcases stepped with ⟨configEq, acceptedEq, activatedEq⟩ |
        ⟨completed, completedReady, action, member, activatedEq, acceptedOnly⟩
    · refine ⟨extra, ?_, together, fun owner owned entered seen => ?_,
        fun field changed => ?_⟩
      · change next.application.config.history.map Completion.event = _
        rw [configEq]
        exact order
      · rw [activatedEq]
        exact activated owner owned entered seen
      · rw [acceptedEq] at changed
        exact acceptedChanged field changed
    · have readyBefore : execution.application.config.cut.Ready event :=
        ready_of_eventReady_extends order ready unfinishedBefore
      have historyEq := execution.application.config.step_history completed completedReady
        action _ member
      refine ⟨extra ++ [completed], ?_, fun other inside => ?_,
        fun owner owned entered seen => ?_, fun field changed => ?_⟩
      · change next.application.config.history.map Completion.event = _
        rw [historyEq, List.map_append, List.map_singleton, ← List.append_assoc]
        exact congrArg (· ++ [completed]) order
      · rcases List.mem_append.mp inside with old | new
        · exact together other old
        · cases List.mem_singleton.mp new
          exact ⟨execution.application.config.cut, completedReady, readyBefore⟩
      · have readyNow : next.application.config.cut.Ready event := by
          rw [execution.application.config.step_cut completed completedReady action _ member]
          exact readyBefore.after_complete completedReady (fun same => unfinished (by
            rw [execution.application.config.step_cut completed completedReady action _ member,
              EventOrder.Cut.mem_complete]
            exact Or.inl same))
        rw [activatedEq]
        simp [State.refreshActivated, readyNow, owned, activated owner owned entered seen]
      · by_cases same : next.application.accepted field = execution.application.accepted field
        · rw [same] at changed
          obtain ⟨vacant, other, inside, fieldEq⟩ := acceptedChanged field changed
          exact ⟨vacant, other, List.mem_append_left _ inside, fieldEq⟩
        · obtain ⟨vacantBefore, fieldEq⟩ := acceptedOnly field same
          by_cases kept : execution.application.accepted field =
              entry.beforeView.application.publicView.accepted field
          · exact ⟨kept ▸ vacantBefore, completed,
              List.mem_append_right _ (List.mem_singleton_self _), fieldEq⟩
          · obtain ⟨vacant, _⟩ := acceptedChanged field kept
            exact ⟨vacant, completed, List.mem_append_right _ (List.mem_singleton_self _),
              fieldEq⟩

/-- Recorded views of ready events keep these facts at every legal history. -/
theorem entryEventStable_history (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      state) :
    ReactiveApplication.serviceInvariant (EntryEventStable runtime leaks) state :=
  (entryEventStable_serviceInvariant runtime leaks scheduler).history initial horizon
    (fun state _ who entry member => by
      simp [ReactiveApplication.Execution.initial] at member) trace

omit [DecidableEq Player] in
/-- A graph step leaves every store field in place except the completed
event's output, which was unavailable before. -/
theorem step_store_eq_or_output {config next : graph.Config} {event : graph.EventId}
    {ready : config.cut.Ready event} {action : graph.Action event}
    (member : next ∈ (config.step event ready action).support) (field : graph.Field) :
    next.store field = config.store field ∨ (field = .inr event ∧ config.store field = none) := by
  rw [Config.step, PMF.support_map] at member
  obtain ⟨value, _, rfl⟩ := member
  rw [EventGraph.store_complete]
  by_cases same : field = .inr event
  · subst same
    right
    refine ⟨rfl, ?_⟩
    rw [Config.store_output]
    cases output : config.outputs event with
    | none => rfl
    | some _ =>
        exact (ready.1 ((config.output_available event).mp (by rw [output]; rfl))).elim
  · left
    exact Function.update_of_ne same _ _

/-- A recorded response's public view: its completion order is a prefix of the
current one, and a public field it saw now differs only if it was unavailable
then and is the output of an event that had not completed then. -/
def EntryStoreStable (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who,
    entry.beforeView.application.publicView.observation.completionOrder <+:
        execution.application.publicView.observation.completionOrder ∧
      ∀ field, execution.application.publicView.observation.store field ≠
          entry.beforeView.application.publicView.observation.store field →
        entry.beforeView.application.publicView.observation.store field = none ∧
          ∃ event, field = .inr event ∧
            event ∉ entry.beforeView.application.publicView.observation.completionOrder

/-- Recorded public views keep these facts, for every scheduler and arbitrary
responses. -/
theorem entryStoreStable_serviceInvariant
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (EntryStoreStable runtime leaks) where
  respond execution who action valid := by
    let app := runtime.reactiveApplication leaks
    have publicEq := (runtime.reactive_respond_application leaks execution who action).2
    intro observer entry member
    rw [publicEq]
    rcases app.respond_entry_origin execution who observer action entry member with
      prior | ⟨_, fresh⟩
    · exact valid observer entry prior
    · rw [fresh]
      exact ⟨List.prefix_refl _, fun field changed => (changed rfl).elim⟩
  environment execution next command valid _ reached := by
    let app := runtime.reactiveApplication leaks
    have recallEq := app.environmentStep_recall execution next command reached
    intro observer entry member
    rw [recallEq] at member
    obtain ⟨prefixBefore, changedBefore⟩ := valid observer entry member
    rcases completionStep_reactive_environmentStep runtime leaks execution next command reached
      with ⟨configEq, _, _⟩ | ⟨completed, completedReady, action, stepped, _, _⟩
    · have publicEq : next.application.publicView.observation =
          execution.application.publicView.observation := by
        change graph.publicObserve next.application.config =
          graph.publicObserve execution.application.config
        rw [configEq]
      rw [publicEq]
      exact ⟨prefixBefore, changedBefore⟩
    · have historyEq := execution.application.config.step_history completed completedReady
        action _ stepped
      have orderEq : next.application.publicView.observation.completionOrder =
          execution.application.publicView.observation.completionOrder ++ [completed] := by
        change next.application.config.history.map Completion.event = _
        rw [historyEq, List.map_append, List.map_singleton]
        rfl
      refine ⟨orderEq ▸ prefixBefore.trans (List.prefix_append _ _), fun field changed => ?_⟩
      by_cases kept : next.application.publicView.observation.store field =
          execution.application.publicView.observation.store field
      · exact changedBefore field (kept ▸ changed)
      · have stepEq := step_store_eq_or_output stepped field
        change graph.publicStore next.application.config.store field ≠
          graph.publicStore execution.application.config.store field at kept
        unfold EventGraph.publicStore at kept
        split at kept
        · rcases stepEq with same | ⟨fieldEq, absent⟩
          · exact (kept same).elim
          · have unseen : completed ∉
                entry.beforeView.application.publicView.observation.completionOrder := by
              intro seen
              apply completedReady.1
              apply (execution.application.config.history_exact completed).mp
              obtain ⟨rest, split⟩ := prefixBefore
              change completed ∈ execution.application.publicView.observation.completionOrder
              rw [← split]
              exact List.mem_append_left _ seen
            have beforeNone : execution.application.publicView.observation.store field =
                none := by
              change graph.publicStore execution.application.config.store field = none
              unfold EventGraph.publicStore
              rw [absent]
              split <;> rfl
            refine ⟨?_, completed, fieldEq, unseen⟩
            by_cases same : execution.application.publicView.observation.store field =
                entry.beforeView.application.publicView.observation.store field
            · rw [← same]
              exact beforeNone
            · exact (changedBefore field same).1
        · exact (kept rfl).elim

/-- Recorded public stores are retained at every legal history. -/
theorem entryStoreStable_history (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      state) :
    ReactiveApplication.serviceInvariant (EntryStoreStable runtime leaks) state :=
  (entryStoreStable_serviceInvariant runtime leaks scheduler).history initial horizon
    (fun state _ who entry member => by
      simp [ReactiveApplication.Execution.initial] at member) trace

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
    (invariant : state.BindingInvariant) :
    ∃ next, handle runtime state ⟨id, .commitment event candidate⟩ = some next := by
  obtain ⟨ready, _, owned⟩ := includable
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
      exact ⟨_, runtime.handle_commitment_eq state id event candidate owner payload outputEq
        codeEq node readyNow timely sender handleOwner vacantNow unusedNow⟩

/-- **An acceptable fresh call stays acceptable.** On a graph whose
simultaneously ready events have different actors and reveals ready together
are independent, a packet acceptable on a recorded view of its ready event is
accepted at a later state where the event is unfinished and within its
deadline, when the events completed since were ready together with it,
accepted handles changed only at their vacant output fields, and public fields
changed only at outputs of events that had not completed then. -/
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
    (storeChanged : ∀ field, state.publicView.observation.store field ≠
        view.observation.store field →
      view.observation.store field = none ∧
        ∃ other, field = .inr other ∧ other ∉ view.observation.completionOrder)
    (unfinished : event ∉ state.config.cut.completed)
    (timely : state.WithinDeadline runtime event)
    (certified : ∀ fact ∈ message.payload.evidence.toList, fact.Holds state)
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
        invariant
  | opening actual candidate raw =>
      change some actual = some event at named
      have actualEq : actual = event := Option.some.inj named
      subst actualEq
      cases node : nodeView graph actual with
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨ready, _, certifiedPacket, guards, sender, owned, associated, _, _⟩ :=
            (runtime.freshServiceEnvelope_opening_iff view id actual owner payload binding checks
              outputEq codeEq node candidate raw evidence token).mp conforming
          have readyNow := ready_of_eventReady_extends order ready unfinished
          obtain ⟨value, rawEq, publicChecks⟩ :=
            (view.openingGuardsAccepted_iff owner actual payload binding checks outputEq codeEq
              node candidate raw evidence).mp guards
          subst raw
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
          have readsOf : ∀ field ∈ GuardCheck.listReadFields checks,
              field ∈ (graph.nodes actual).readFields := by
            intro field member
            rw [← EventCode.readFields_cast outputEq (graph.nodes actual), codeEq]
            exact Finset.mem_insert_of_mem member
          have agree : Store.AgreeOn view.observation.store state.publicView.observation.store
              (GuardCheck.listReadFields checks) := by
            intro field member
            by_contra different
            obtain ⟨_, other, rfl, unseen⟩ := storeChanged _ (Ne.symm different)
            exact unseen (ready.2 other
              (graph.reads_available actual (.inr other) (readsOf _ member)))
          have acceptedChecks : GuardCheck.allAccepted? checks state.config.store
              (.success value) = some true := by
            rw [GuardCheck.allAccepted?_congr checks _ _ _ agree] at publicChecks
            change GuardCheck.allAccepted? checks (graph.publicStore state.config.store)
              (.success value) = some true at publicChecks
            rwa [GuardCheck.allAccepted?_publicStore] at publicChecks
          have resolved : EventCode.resolveOutput? binding checks true state.config.store =
              some (.success value) := by
            simp only [EventCode.resolveOutput?, stored, Option.bind_eq_bind, Option.bind_some,
              ↓reduceIte, acceptedChecks, Option.pure_def]
          exact ⟨_, runtime.handle_opening_eq state id actual candidate owner payload binding
            checks outputEq codeEq node readyNow timely sender owned associatedNow value
            verified stored (.success value) resolved⟩
      | bind _ _ _ _ =>
          have absent := conforming.2.2.2.2
          rw [node] at absent
          exact absent.elim
      | sample _ _ _ _ =>
          have absent := conforming.2.2.2.2
          rw [node] at absent
          exact absent.elim

end Vegas.EventGraphRuntime
