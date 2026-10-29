/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveEntryStability
import Vegas.Pending.EventAssociationInvariant
import Vegas.Pending.EventBindingInvariant
import Vegas.Pending.PublicFailureEvidence

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

private theorem ready_view_completion_step (saved : PublicView graph)
    (before after : State graph) (moved : CompletionStep before after)
    (valid : ∀ event, saved.EventReady event → event ∉ before.config.cut.completed →
      ∃ extra, before.publicView.observation.completionOrder =
          saved.observation.completionOrder ++ extra ∧
        (∀ other ∈ extra, graph.ReadyTogether other event) ∧
        (∀ owner, graph.actor? event = some owner → ∀ entered,
          saved.activatedAt event = some entered → before.activatedAt event = some entered) ∧
        ∀ field, before.accepted field ≠ saved.accepted field →
          saved.accepted field = none ∧ ∃ other ∈ extra, field = .inr other) :
    ∀ event, saved.EventReady event → event ∉ after.config.cut.completed →
      ∃ extra, after.publicView.observation.completionOrder =
          saved.observation.completionOrder ++ extra ∧
        (∀ other ∈ extra, graph.ReadyTogether other event) ∧
        (∀ owner, graph.actor? event = some owner → ∀ entered,
          saved.activatedAt event = some entered → after.activatedAt event = some entered) ∧
        ∀ field, after.accepted field ≠ saved.accepted field →
          saved.accepted field = none ∧ ∃ other ∈ extra, field = .inr other := by
  intro event ready unfinished
  have unfinishedBefore : event ∉ before.config.cut.completed :=
    fun completed => unfinished (moved.completed_mono completed)
  obtain ⟨extra, order, together, activated, acceptedChanged⟩ :=
    valid event ready unfinishedBefore
  rcases moved with ⟨configEq, acceptedEq, activatedEq⟩ |
      ⟨completed, completedReady, action, member, activatedEq, acceptedOnly⟩
  · refine ⟨extra, ?_, together, fun owner owned entered seen => ?_,
      fun field changed => ?_⟩
    · change after.config.history.map Completion.event = _
      rw [configEq]
      exact order
    · rw [activatedEq]
      exact activated owner owned entered seen
    · rw [acceptedEq] at changed
      exact acceptedChanged field changed
  · have readyBefore : before.config.cut.Ready event :=
      ready_of_eventReady_extends order ready unfinishedBefore
    have historyEq := before.config.step_history_events completed completedReady
      action _ member
    refine ⟨extra ++ [completed], ?_, fun other inside => ?_,
      fun owner owned entered seen => ?_, fun field changed => ?_⟩
    · change after.config.history.map Completion.event = _
      rw [historyEq, ← List.append_assoc]
      exact congrArg (· ++ [completed]) order
    · rcases List.mem_append.mp inside with old | new
      · exact together other old
      · cases List.mem_singleton.mp new
        exact ⟨before.config.cut, completedReady, readyBefore⟩
    · have readyNow : after.config.cut.Ready event := by
        rw [before.config.step_cut completed completedReady action _ member]
        exact readyBefore.after_complete completedReady (fun same => unfinished (by
          rw [before.config.step_cut completed completedReady action _ member,
            EventOrder.Cut.mem_complete]
          exact Or.inl same))
      rw [activatedEq]
      simp [State.refreshActivated, readyNow, owned, activated owner owned entered seen]
    · by_cases same : after.accepted field = before.accepted field
      · rw [same] at changed
        obtain ⟨vacant, other, inside, fieldEq⟩ := acceptedChanged field changed
        exact ⟨vacant, other, List.mem_append_left _ inside, fieldEq⟩
      · obtain ⟨vacantBefore, fieldEq⟩ := acceptedOnly field same
        by_cases kept : before.accepted field =
            saved.accepted field
        · exact ⟨kept ▸ vacantBefore, completed,
            List.mem_append_right _ (List.mem_singleton_self _), fieldEq⟩
        · obtain ⟨vacant, _⟩ := acceptedChanged field kept
          exact ⟨vacant, completed, List.mem_append_right _ (List.mem_singleton_self _),
            fieldEq⟩

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
    intro observer entry member
    rw [recallEq] at member
    let saved := entry.beforeView.application.publicView
    let retained (current : State graph) : Prop :=
      ∀ event, saved.EventReady event → event ∉ current.config.cut.completed →
      ∃ extra, current.publicView.observation.completionOrder =
          saved.observation.completionOrder ++ extra ∧
        (∀ other ∈ extra, graph.ReadyTogether other event) ∧
        (∀ owner, graph.actor? event = some owner → ∀ entered,
          saved.activatedAt event = some entered → current.activatedAt event = some entered) ∧
        ∀ field, current.accepted field ≠ saved.accepted field →
          saved.accepted field = none ∧ ∃ other ∈ extra, field = .inr other
    have preserved : ∀ {before after : State graph},
        Relation.ReflTransGen CompletionStep before after → retained before → retained after := by
      intro before after path
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl => exact id
      | @head before middle moved _ ih =>
          exact fun prior => ih (ready_view_completion_step saved before middle moved prior)
    exact preserved (completionPath_reactive_environmentStep runtime leaks execution next command
      reached) (valid observer entry member)

/-- Recorded views of ready events keep these facts at every legal history. -/
theorem entryEventStable_history (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      state) :
    ReactiveApplication.serviceInvariant (EntryEventStable runtime leaks) state :=
  (entryEventStable_serviceInvariant runtime leaks scheduler).history initial horizon
    (fun state _ who entry member => by
      simp [ReactiveApplication.Execution.initial] at member) trace

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

private theorem store_view_completion_step (saved : PublicView graph)
    (before after : State graph) (moved : CompletionStep before after)
    (valid : saved.observation.completionOrder <+:
        before.publicView.observation.completionOrder ∧
      ∀ field, before.publicView.observation.store field ≠ saved.observation.store field →
        saved.observation.store field = none ∧
          ∃ event, field = .inr event ∧ event ∉ saved.observation.completionOrder) :
    saved.observation.completionOrder <+:
        after.publicView.observation.completionOrder ∧
      ∀ field, after.publicView.observation.store field ≠ saved.observation.store field →
        saved.observation.store field = none ∧
          ∃ event, field = .inr event ∧ event ∉ saved.observation.completionOrder := by
  obtain ⟨prefixBefore, changedBefore⟩ := valid
  rcases moved with ⟨configEq, _, _⟩ | ⟨completed, completedReady, action, stepped, _, _⟩
  · have publicEq : after.publicView.observation =
        before.publicView.observation := by
      change graph.publicObserve after.config =
        graph.publicObserve before.config
      rw [configEq]
    rw [publicEq]
    exact ⟨prefixBefore, changedBefore⟩
  · have historyEq := before.config.step_history_events completed completedReady
      action _ stepped
    have orderEq : after.publicView.observation.completionOrder =
        before.publicView.observation.completionOrder ++ [completed] := by
      change after.config.history.map Completion.event = _
      rw [historyEq]
      rfl
    refine ⟨orderEq ▸ prefixBefore.trans (List.prefix_append _ _), fun field changed => ?_⟩
    by_cases kept : after.publicView.observation.store field =
        before.publicView.observation.store field
    · exact changedBefore field (kept ▸ changed)
    · have stepEq := step_store_eq_or_output stepped field
      change graph.publicStore after.config.store field ≠
        graph.publicStore before.config.store field at kept
      unfold EventGraph.publicStore at kept
      split at kept
      · rcases stepEq with same | ⟨fieldEq, absent⟩
        · exact (kept same).elim
        · have unseen : completed ∉
              saved.observation.completionOrder := by
            intro seen
            apply completedReady.1
            apply (before.config.history_exact completed).mp
            obtain ⟨rest, split⟩ := prefixBefore
            change completed ∈ before.publicView.observation.completionOrder
            rw [← split]
            exact List.mem_append_left _ seen
          have beforeNone : before.publicView.observation.store field =
              none := by
            change graph.publicStore before.config.store field = none
            unfold EventGraph.publicStore
            rw [absent]
            split <;> rfl
          refine ⟨?_, completed, fieldEq, unseen⟩
          by_cases same : before.publicView.observation.store field =
              saved.observation.store field
          · rw [← same]
            exact beforeNone
          · exact (changedBefore field same).1
      · exact (kept rfl).elim

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
    let saved := entry.beforeView.application.publicView
    let retained (current : State graph) : Prop :=
      saved.observation.completionOrder <+:
        current.publicView.observation.completionOrder ∧
      ∀ field, current.publicView.observation.store field ≠ saved.observation.store field →
        saved.observation.store field = none ∧
          ∃ event, field = .inr event ∧ event ∉ saved.observation.completionOrder
    have preserved : ∀ {before after : State graph},
        Relation.ReflTransGen CompletionStep before after → retained before → retained after := by
      intro before after path
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl => exact id
      | @head before middle moved _ ih =>
          exact fun prior => ih (store_view_completion_step saved before middle moved prior)
    exact preserved (completionPath_reactive_environmentStep runtime leaks execution next command
      reached) (valid observer entry member)

/-- Recorded public stores are retained at every legal history. -/
theorem entryStoreStable_history (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      state) :
    ReactiveApplication.serviceInvariant (EntryStoreStable runtime leaks) state :=
  (entryStoreStable_serviceInvariant runtime leaks scheduler).history initial horizon
    (fun state _ who entry member => by
      simp [ReactiveApplication.Execution.initial] at member) trace

end Vegas.EventGraphRuntime
