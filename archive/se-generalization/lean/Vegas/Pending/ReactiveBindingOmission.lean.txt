/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPublicState
import Vegas.Pending.ReactiveDisclosureStability
import Vegas.Pending.ReactiveDecisionMiss

/-! # Public evidence of an omitted required binding

Completion without an accepted handle is visible in the application state.
This detector needs no inference from absent partial traffic records. An
accepted opaque handle does not trigger it, even if its hidden meaning is
unusable. Once present, the evidence survives arbitrary native continuations.

Using this evidence as a sanction additionally requires a backend guarantee
that a timely permitted submission is included before expiry. The detector
alone does not attribute censorship or prove that an earlier silent response
will miss the eventual deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def PublicView.missedBinding (view : PublicView graph) (event : graph.EventId) : Bool :=
  match graph.outputLayout event with
  | .binding _ _ => decide (event ∈ view.observation.completionOrder) &&
      (view.accepted (.inr event)).isNone
  | .publicData _ | .privateInput _ _ | .publication _ => false

theorem State.publicView_missedBinding (state : State graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    state.publicView.missedBinding event = true ↔
      event ∈ state.config.cut.completed ∧ state.accepted (.inr event) = none := by
  simp only [PublicView.missedBinding, binding, Bool.and_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨completed, absent⟩
    exact ⟨(state.config.history_exact event).mp completed, absent⟩
  · rintro ⟨completed, absent⟩
    exact ⟨(state.config.history_exact event).mpr completed, absent⟩

theorem PublicView.missedBinding_of_accepted (view : PublicView graph)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : view.accepted (.inr event) = some candidate) :
    view.missedBinding event = false := by
  unfold missedBinding
  cases graph.outputLayout event <;> simp only [accepted, Option.isNone_some, Bool.and_false]

theorem State.missedBinding_complete (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (absent : state.accepted (.inr event) = none) :
    (state.complete event ready action value).publicView.missedBinding event = true := by
  classical
  apply (State.publicView_missedBinding _ event owner payload binding).mpr
  exact ⟨by simp [State.complete, EventOrder.Cut.complete], absent⟩

/-- Actual binding expiry produces publicly persistent omission evidence.
The accepted-handle premise is about ledger state, not a watcher's sample. -/
theorem missedBinding_expire (runtime : EventGraphRuntime graph) (state next : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (absent : state.accepted (.inr event) = none)
    (reached : next ∈ (environmentStep runtime state (.expire event)).support) :
    next.publicView.missedBinding event = true := by
  classical
  rw [environmentStep_expire_bind_eq runtime state event ready entered activated due owner payload
    outputEq codeEq node] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  exact state.missedBinding_complete event ready _ _ owner payload outputEq absent

/-- Native submissions, packet handling, public chance and service commands
cannot erase a completed binding omission, even after further deviations. -/
theorem reactiveMissedBindingInvariant [DecidableEq Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    (runtime.reactiveApplication leaks).Invariant
      (fun state => state.publicView.missedBinding event = true) where
  submit state who material missed := by
    have same := (runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩).2
    exact (congrArg (fun view : PublicView graph => view.missedBinding event) same).trans missed
  handle state message next missed handled := by
    obtain ⟨completed, absent⟩ :=
      (state.publicView_missedBinding event owner payload binding).mp missed
    have present : (state.config.store (.inr event)).isSome = true :=
      (state.config.output_available event).mpr completed
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    have retained := handle_store_of_some runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call handled) (.inr event) value stored
    apply (next.publicView_missedBinding event owner payload binding).mpr
    refine ⟨(next.config.output_available event).mp ?_, ?_⟩
    · change (next.config.store (.inr event)).isSome = true
      rw [retained]
      rfl
    · exact (handle_accepted_of_present runtime state next (.inr event) present
        ⟨message.id, message.payload.call⟩
          (reactiveHandle_call handled)).trans absent
  environment state command next missed reached := by
    obtain ⟨completed, absent⟩ :=
      (state.publicView_missedBinding event owner payload binding).mp missed
    have present : (state.config.store (.inr event)).isSome = true :=
      (state.config.output_available event).mpr completed
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    have retained := environmentStep_store_of_some runtime state next command reached
      (.inr event) value stored
    apply (next.publicView_missedBinding event owner payload binding).mpr
    refine ⟨(next.config.output_available event).mp ?_, ?_⟩
    · change (next.config.store (.inr event)).isSome = true
      rw [retained]
      rfl
    · exact (congrFun (environmentStep_tables runtime state next command reached).1
        (.inr event)).trans absent

/-- The binding-specific absence detector agrees with the actual expiry marker.
This is an invariant of initialized executions, not an arbitrary-state identity. -/
def State.BindingMissesExact (state : State graph) : Prop :=
  ∀ event owner payload, graph.outputLayout event = .binding owner payload →
    (event ∈ state.missedEvents ↔
      event ∈ state.config.cut.completed ∧ state.accepted (.inr event) = none)

private theorem State.BindingMissesExact.complete_markMissed
    (state : State graph) (valid : state.BindingMissesExact)
    (binding : state.BindingInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    ((state.complete event ready action value).markMissed event).BindingMissesExact := by
  intro query owner payload layout
  by_cases same : query = event
  · subst query
    have absent : state.accepted (.inr event) = none := by
      cases accepted : state.accepted (.inr event) with
      | none => rfl
      | some candidate =>
          exact (ready.1 (binding.toAssociationInvariant.accepted_complete event candidate
            accepted)).elim
    simp only [State.markMissed, State.complete, EventGraph.Config.complete, absent,
      EventOrder.Cut.mem_complete, Finset.mem_insert_self, true_or, and_self]
  · change query ∈ insert event state.missedEvents ↔
      query ∈ (state.config.cut.complete event ready).completed ∧
        state.accepted (.inr query) = none
    simp only [Finset.mem_insert, same, false_or, EventOrder.Cut.mem_complete]
    exact valid query owner payload layout

private theorem bindingMissesExact_handle [DecidableEq Player]
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (valid : state.BindingMissesExact)
    (message : Message Player (Payload graph))
    (handled : handle runtime state message = some next) : next.BindingMissesExact := by
  intro event owner payload layout
  have markers := handle_missedEvents runtime state next message handled
  by_cases completed : event ∈ state.config.cut.completed
  · have available := (state.config.output_available event).mpr completed
    have accepted := handle_accepted_of_present runtime state next (.inr event) available message
      handled
    rw [markers, accepted]
    have completedNext := handle_completed_subset runtime state next message handled completed
    simpa only [completed, completedNext, true_and] using valid event owner payload layout
  · have clear : event ∉ state.missedEvents := fun marked =>
      completed ((valid event owner payload layout).mp marked).1
    rw [markers]
    constructor
    · exact fun marked => (clear marked).elim
    · rintro ⟨finished, absent⟩
      obtain ⟨addressed, named, ready, action, stepped⟩ := handle_config_mem_step runtime state
        next message handled
      rw [state.config.step_cut addressed ready action next.config stepped,
        EventOrder.Cut.mem_complete] at finished
      have same := finished.resolve_right completed
      subst addressed
      rcases message with ⟨id, packet⟩
      cases packet with
      | malformed raw => simp only [Payload.event?, reduceCtorEq] at named
      | commitment actual candidate =>
          cases Option.some.inj named
          rw [(handle_commitment_tables runtime state next id event candidate handled).2.1,
            Function.update_self] at absent
          cases absent
      | opening actual candidate raw | withhold actual =>
          cases Option.some.inj named
          cases node : nodeView graph event with
          | bind => simp [handle, ready, node] at handled
          | sample sampled law outputEq codeEq
          | resolve actor sampled ref checks outputEq codeEq =>
              rw [outputEq] at layout
              cases layout

private theorem bindingMissesExact_environment
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (command : EnvironmentCommand graph) (binding : state.BindingInvariant)
    (valid : state.BindingMissesExact)
    (reached : next ∈ (environmentStep runtime state command).support) :
    next.BindingMissesExact := by
  classical
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | executeSample addressed =>
      intro event owner payload layout
      rw [environmentStep_executeSample_missedEvents runtime state next addressed reached,
        (environmentStep_tables runtime state next (.executeSample addressed) reached).1]
      rcases (environmentStep_executeSample_config_activated runtime state next addressed
          reached).2 with unchanged | ⟨ready, action, stepped, _⟩
      · rw [unchanged.1]
        exact valid event owner payload layout
      · have different : event ≠ addressed := by
          rintro rfl
          rw [environmentStep_executeSample_of_nonsample runtime state event ready
            (fun sampled law outputEq _codeEq _node => by rw [outputEq] at layout; cases layout),
              PMF.mem_support_pure_iff _ _] at reached
          subst next
          have impossible := state.config.step_cut event ready action state.config stepped
          have member : event ∈ state.config.cut.completed := by
            rw [impossible, EventOrder.Cut.mem_complete]
            exact Or.inl rfl
          exact ready.1 member
        rw [state.config.step_cut addressed ready action next.config stepped]
        simpa only [EventOrder.Cut.mem_complete, different, false_or] using
          valid event owner payload layout
  | expire event =>
      by_cases ready : state.config.cut.Ready event
      · cases activated : state.activatedAt event with
        | none =>
            rw [environmentStep_expire_of_not_activated runtime state event ready activated,
              PMF.mem_support_pure_iff _ _] at reached
            subst next
            exact valid
        | some entered =>
            by_cases due : runtime.deadline event ≤ state.clock - entered
            · cases node : nodeView graph event with
              | sample payload law outputEq codeEq =>
                  rw [environmentStep_expire_sample_eq runtime state event ready entered
                    activated due payload law outputEq codeEq node,
                    PMF.mem_support_pure_iff _ _] at reached
                  subst next
                  exact valid
              | bind owner payload outputEq codeEq =>
                  rw [environmentStep_expire_bind_eq runtime state event ready entered activated
                    due owner payload outputEq codeEq node, PMF.mem_support_pure_iff _ _]
                    at reached
                  subst next
                  exact State.BindingMissesExact.complete_markMissed state valid binding event
                    ready _ _
              | resolve owner payload ref checks outputEq codeEq =>
                  rw [environmentStep_expire_resolve_eq runtime state event ready entered
                    activated due owner payload ref checks outputEq codeEq node,
                    PMF.mem_support_pure_iff _ _] at reached
                  subst next
                  exact State.BindingMissesExact.complete_markMissed state valid binding event
                    ready _ _
            · rw [environmentStep_expire_of_not_due runtime state event ready entered activated
                due, PMF.mem_support_pure_iff _ _] at reached
              subst next
              exact valid
      · rw [environmentStep_expire_of_not_ready runtime state event ready,
          PMF.mem_support_pure_iff _ _] at reached
        subst next
        exact valid

/-- The actual binding miss marker is exactly completion without acceptance at
every initialized raw history, including arbitrary deviations and scheduling. -/
theorem bindingMissesExact_history [DecidableEq Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    control.execution.application.BindingMissesExact :=
  (show (runtime.reactiveApplication leaks).Invariant (fun state =>
    state.BindingInvariant ∧ state.BindingMissesExact) from {
      submit := fun state who material valid =>
        ⟨(runtime.reactiveBindingInvariant leaks).submit state who material valid.1, by
          have same := runtime.reactive_respond_application leaks
            (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩
          intro event owner payload layout
          have marked := congrArg PublicView.missedEvents same.2
          have accepted := congrArg PublicView.accepted same.2
          change ((runtime.reactiveApplication leaks).submit state who material).missedEvents =
            state.missedEvents at marked
          change ((runtime.reactiveApplication leaks).submit state who material).accepted =
            state.accepted at accepted
          have configEq := same.1
          change ((runtime.reactiveApplication leaks).submit state who material).config =
            state.config at configEq
          rw [marked, accepted, configEq]
          exact valid.2 event owner payload layout⟩
      handle := fun state message next valid handled =>
        ⟨(runtime.reactiveBindingInvariant leaks).handle state message next valid.1 handled,
          bindingMissesExact_handle runtime state next valid.2
            ⟨message.id, message.payload.call⟩ (reactiveHandle_call handled)⟩
      environment := fun state command next valid reached =>
        ⟨(runtime.reactiveBindingInvariant leaks).environment state command next valid.1 reached,
          bindingMissesExact_environment runtime state next command valid.1 valid.2
            reached⟩ }).history
    (inputs.map State.initial) horizon scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨State.initial_bindingInvariant initial, ?_⟩
      intro event owner payload _layout
      constructor
      · intro missed
        exact (Finset.notMem_empty event missed).elim
      · rintro ⟨completed, _⟩
        exact (Finset.notMem_empty event completed).elim) trace |>.2

theorem missedBinding_iff_marker_history [DecidableEq Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (layout : graph.outputLayout event = .binding owner payload) :
    control.execution.application.publicView.missedBinding event = true ↔
      event ∈ control.execution.application.missedEvents := by
  rw [State.publicView_missedBinding _ event owner payload layout]
  exact (bindingMissesExact_history runtime leaks inputs horizon scheduler trace
    event owner payload layout).symm

end Vegas.EventGraphRuntime
