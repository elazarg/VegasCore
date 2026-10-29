/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionInvariant
import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveInvariant

/-! # Public failure and receipt provenance along native completion traces

One native call or environment command may complete an event and drain further
automatic events. Each elementary footprint preserves prior public failures
and accepted-handle provenance, and the same facts hold along the finite trace.
Public default membership is derived from the authoritative graph history.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

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

theorem CompletionStep.refl (state : State graph) : CompletionStep state state :=
  Or.inl ⟨rfl, rfl, rfl⟩

/-- An accepted commitment fills a vacant output field. -/
theorem handle_commitment_vacant (state next : State graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    state.accepted (.inr event) = none := by
  obtain ⟨_active, _ready, _timely, _owner, _payload, _outputEq, _codeEq, _view, _sender,
    _handleOwner, vacant, _unused, _nextEq⟩ :=
    (handle_commitment_iff runtime state next id event candidate).mp accepted
  exact vacant

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


/-- Every native completion step preserves all previously completed events. -/
theorem CompletionStep.completed_mono {before after : State graph}
    (step : CompletionStep before after) :
    before.config.cut.completed ⊆ after.config.cut.completed := by
  rcases step with ⟨same, _accepted, _activated⟩ |
    ⟨event, ready, action, supported, _activated, _accepted⟩
  · rw [same]
  · intro query completed
    rw [before.config.step_cut event ready action _ supported, EventOrder.Cut.mem_complete]
    exact Or.inr completed

/-- Accepted handles cannot change along a completion step that leaves the
compiled configuration unchanged. -/
theorem CompletionStep.accepted_eq_of_config_eq {before after : State graph}
    (step : CompletionStep before after) (same : after.config = before.config) :
    after.accepted = before.accepted := by
  rcases step with ⟨_config, accepted, _activated⟩ |
    ⟨event, ready, action, supported, _activated, _accepted⟩
  · exact accepted
  · have completed : event ∈ after.config.cut.completed := by
      rw [before.config.step_cut event ready action _ supported, EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    rw [same] at completed
    exact (ready.1 completed).elim

namespace State

/-- Inspect a public publication result, without reading hidden binding values. -/
def publicationFailed (state : State graph) (event : graph.EventId) : Bool :=
  match nodeView graph event with
  | .resolve _owner _payload _binding _checks outputEq _ =>
      match state.config.outputs event with
      | none => false
      | some result =>
          match cast (congrArg EventField.Value outputEq) result with
          | .failure => true
          | .success _ => false
  | .bind .. | .sample .. => false


/-- Public failure means a completed binding lacking an accepted handle or a
failed public resolution. Hidden binding values are irrelevant. -/
def PublicFailure (state : State graph) (event : graph.EventId) : Prop :=
  state.publicView.missedBinding event = true ∨
    State.publicationFailed state event = true

/-- Accepted event handles belong only to completed events. -/
def ReceiptsComplete (state : State graph) : Prop :=
  ∀ event candidate, state.accepted (.inr event) = some candidate →
    event ∈ state.config.cut.completed

theorem ReceiptsComplete.initial (inputs : graph.Inputs) :
    (State.initial inputs).ReceiptsComplete := by
  intro event candidate accepted
  obtain ⟨input, _, _, impossible, _, _⟩ := initial_accepted_eq_some inputs _ candidate accepted
  cases impossible

/-- Completion footprints preserve the public receipt's completed-event provenance. -/
theorem ReceiptsComplete.step {before after : State graph}
    (valid : before.ReceiptsComplete) (step : CompletionStep before after) :
    after.ReceiptsComplete := by
  classical
  rcases step with ⟨same, acceptedEq, _⟩ | ⟨event, ready, action, member, _, acceptedOnly⟩
  · intro query candidate accepted
    rw [acceptedEq] at accepted
    rw [same]
    exact valid query candidate accepted
  · intro query candidate accepted
    rw [before.config.step_cut event ready action after.config member,
      EventOrder.Cut.mem_complete]
    by_cases same : after.accepted (.inr query) = before.accepted (.inr query)
    · exact Or.inr (valid query candidate (same ▸ accepted))
    · obtain ⟨_, named⟩ := acceptedOnly (.inr query) same
      exact Or.inl (Sum.inr.inj named)

omit [DecidableEq Player] in
theorem ReceiptsComplete.vacant {state : State graph} (valid : state.ReceiptsComplete)
    {event : graph.EventId} (unfinished : event ∉ state.config.cut.completed) :
    state.accepted (.inr event) = none := by
  cases accepted : state.accepted (.inr event) with
  | none => rfl
  | some candidate => exact (unfinished (valid event candidate accepted)).elim

omit [DecidableEq Player] in
theorem PublicFailure.completed {state : State graph} {event : graph.EventId}
    (failed : state.PublicFailure event) : event ∈ state.config.cut.completed := by
  rcases failed with missed | publication
  · cases kind : graph.outputLayout event with
    | binding owner payload =>
        exact ((state.publicView_missedBinding event owner payload kind).mp missed).1
    | publicData payload | privateInput owner payload | publication payload =>
        simp only [PublicView.missedBinding, kind, Bool.false_eq_true] at missed
  · cases output : state.config.outputs event with
    | some value => exact (state.config.output_available event).mp (by rw [output]; rfl)
    | none =>
        unfold State.publicationFailed at publication
        cases view : nodeView graph event <;>
          simp only [view, output, Bool.false_eq_true] at publication

omit [DecidableEq Player] in
theorem PublicFailure.congr {before after : State graph} (event : graph.EventId)
    (completed : event ∈ after.config.cut.completed ↔ event ∈ before.config.cut.completed)
    (output : after.config.outputs event = before.config.outputs event)
    (accepted : after.accepted (.inr event) = before.accepted (.inr event)) :
    after.PublicFailure event ↔ before.PublicFailure event := by
  unfold PublicFailure
  have omitted : after.publicView.missedBinding event = true ↔
      before.publicView.missedBinding event = true := by
    cases kind : graph.outputLayout event with
    | binding owner payload =>
        rw [after.publicView_missedBinding event owner payload kind,
          before.publicView_missedBinding event owner payload kind, completed, accepted]
    | publicData payload | privateInput owner payload | publication payload =>
        simp only [PublicView.missedBinding, kind]
  have publication : State.publicationFailed after event =
      State.publicationFailed before event := by
    unfold State.publicationFailed
    cases nodeView graph event <;> simp only [output]
  rw [omitted, publication]

/-- Every publicly failed event is already complete, so future completions at
other events preserve its exact failure verdict. -/
theorem PublicFailure.of_step_of_ne {before after : State graph}
    {event : graph.EventId} {ready : before.config.cut.Ready event}
    {action : graph.Action event} (member : after.config ∈
      (before.config.step event ready action).support)
    (acceptedOnly : ∀ field, after.accepted field ≠ before.accepted field →
      field = .inr event) {query : graph.EventId} (different : query ≠ event) :
    after.PublicFailure query ↔ before.PublicFailure query := by
  apply PublicFailure.congr query
  · rw [before.config.step_cut event ready action after.config member,
      EventOrder.Cut.mem_complete]
    simp only [different, false_or]
  · rw [EventGraph.Config.step, PMF.support_map] at member
    obtain ⟨value, _, same⟩ := member
    rw [← same, EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]
  · by_contra changed
    exact different (Sum.inr.inj (acceptedOnly _ changed))

omit [DecidableEq Player] in
/-- Equal native public views carry the same exclusion evidence. -/
theorem PublicFailure.of_publicView_eq {before after : State graph}
    (same : after.publicView = before.publicView) (event : graph.EventId) :
    after.PublicFailure event ↔ before.PublicFailure event := by
  unfold PublicFailure
  have omitted := congrArg (fun view : PublicView graph => view.missedBinding event) same
  rw [omitted]
  suffices State.publicationFailed after event =
      State.publicationFailed before event by rw [this]
  cases view : nodeView graph event with
  | bind | sample => simp only [State.publicationFailed, view]
  | resolve owner payload binding checks outputEq codeEq =>
      have publicField : graph.fieldPublic (.inr event) := by
        change (graph.outputLayout event).IsPublic
        rw [outputEq]
        trivial
      have storeEq := congrArg (fun view : PublicView graph =>
        view.observation.store (.inr event)) same
      change graph.publicStore after.config.store (.inr event) =
        graph.publicStore before.config.store (.inr event) at storeEq
      rw [graph.publicStore_of_public _ _ publicField,
        graph.publicStore_of_public _ _ publicField] at storeEq
      change after.config.outputs event = before.config.outputs event at storeEq
      simp only [State.publicationFailed, view, storeEq]

theorem completed_event_eq_of_step {before after : State graph} {event : graph.EventId}
    {ready : before.config.cut.Ready event} {action : graph.Action event}
    (member : after.config ∈ (before.config.step event ready action).support)
    {query : graph.EventId} (unfinished : query ∉ before.config.cut.completed)
    (completed : query ∈ after.config.cut.completed) : query = event := by
  rw [before.config.step_cut event ready action after.config member,
    EventOrder.Cut.mem_complete] at completed
  exact completed.resolve_right unfinished

/-- A failure completion refreshes activation metadata around its actual graph step. -/
theorem completeFailure_activated (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (state.completeFailure event ready).activatedAt =
      refreshActivated (state.completeFailure event ready).config
        state.clock state.activatedAt := by
  cases view : nodeView graph event with
  | bind actor payload outputEq codeEq => simp only [completeFailure, view, complete]
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [completeFailure, view, complete]
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at acting
      cases acting

theorem completeFailure_completionStep (native : State graph) (event : graph.EventId)
    (ready : native.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    CompletionStep native (native.completeFailure event ready) := by
  obtain ⟨action, member⟩ := native.completeFailure_step event ready acting
  refine Or.inr ⟨event, ready, action, member,
    native.completeFailure_activated event ready acting, ?_⟩
  intro field changed
  exact (changed (congrFun (native.completeFailure_tables event ready).1 field)).elim

theorem completeFailure_publicFailure (native : State graph)
    (valid : native.ReceiptsComplete) (event : graph.EventId)
    (ready : native.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (native.completeFailure event ready).PublicFailure event := by
  cases view : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have notOwned : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [notOwned] at acting
      cases acting
  | bind actor payload outputEq codeEq =>
      left
      simp only [State.completeFailure, view]
      apply (State.publicView_missedBinding _ event actor payload outputEq).mpr
      constructor
      · change event ∈ insert event native.config.cut.completed
        exact Finset.mem_insert_self _ _
      · exact valid.vacant ready.1
  | resolve actor payload binding checks outputEq codeEq =>
      right
      simp [State.publicationFailed, State.completeFailure, view, State.complete]

end State

/-- A completion step retains the exact failure verdict of every event that
was already completed. No record or initialization assumption is required. -/
theorem CompletionStep.publicFailure_iff_of_completed {before after : State graph}
    (step : CompletionStep before after) {event : graph.EventId}
    (completed : event ∈ before.config.cut.completed) :
    after.PublicFailure event ↔ before.PublicFailure event := by
  rcases step with ⟨same, acceptedEq, _⟩ |
    ⟨changed, ready, action, supported, _, acceptedOnly⟩
  · exact State.PublicFailure.congr event (by rw [same]) (by rw [same])
      (congrFun acceptedEq _)
  · exact State.PublicFailure.of_step_of_ne supported
      (fun field different => (acceptedOnly field different).2)
      (fun same => ready.1 (same ▸ completed))

/-- Finite completion traces preserve every already completed event. -/
theorem CompletionStep.completed_mono_path {before after : State graph}
    (path : Relation.ReflTransGen CompletionStep before after) :
    before.config.cut.completed ⊆ after.config.cut.completed := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact Finset.Subset.refl _
  | @head before middle moved _ ih => exact moved.completed_mono.trans ih

/-- An elementary native footprint cannot restore a defaulted player. -/
theorem CompletionStep.defaulted_mono {before after : State graph}
    (moved : CompletionStep before after) :
    before.config.defaulted ⊆ after.config.defaulted := by
  rcases moved with ⟨same, _⟩ | ⟨event, ready, action, supported, _⟩
  · rw [same]
  · exact before.config.defaulted_step event ready action after.config supported

/-- A finite native completion trace cannot restore a defaulted player. -/
theorem CompletionStep.defaulted_mono_path {before after : State graph}
    (path : Relation.ReflTransGen CompletionStep before after) :
    before.config.defaulted ⊆ after.config.defaulted := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact Finset.Subset.refl _
  | @head before middle moved _ ih => exact moved.defaulted_mono.trans ih

/-- Receipt provenance is stable through finite native completion traces. -/
theorem State.ReceiptsComplete.path {before after : State graph}
    (valid : before.ReceiptsComplete)
    (path : Relation.ReflTransGen CompletionStep before after) : after.ReceiptsComplete := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact valid
  | @head before middle moved _ ih => exact ih (valid.step moved)

/-- A completion trace retains the exact failure verdict of every prior completed event. -/
theorem CompletionStep.publicFailure_iff_of_completed_path {before after : State graph}
    (path : Relation.ReflTransGen CompletionStep before after) {event : graph.EventId}
    (completed : event ∈ before.config.cut.completed) :
    after.PublicFailure event ↔ before.PublicFailure event := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head before middle moved _ ih =>
      exact (ih (moved.completed_mono completed)).trans
        (moved.publicFailure_iff_of_completed completed)

/-- Public failure evidence persists along every finite completion trace. -/
theorem State.PublicFailure.of_completionPath {before after : State graph}
    (path : Relation.ReflTransGen CompletionStep before after) {event : graph.EventId}
    (failed : before.PublicFailure event) : after.PublicFailure event :=
  (CompletionStep.publicFailure_iff_of_completed_path path failed.completed).mpr failed

/-- The native automatic routine is a finite trace of elementary completion footprints. -/
theorem State.drain_completionPath (state : State graph) :
    Relation.ReflTransGen CompletionStep state state.drain := by
  apply Relation.ReflTransGen.lift (fun current : State graph => current) _
    state state.drain state.drain_trace
  intro before after moved
  obtain ⟨event, eligible, rfl⟩ := moved
  obtain ⟨owner, acting, _inactive⟩ := eligible.owned
  exact State.completeFailure_completionStep before event eligible.1 acting

/-- Every application operation has a finite native completion footprint. -/
theorem reactiveApplication_completionPath :
    (runtime.reactiveApplication leaks).StepRelation
      (Relation.ReflTransGen CompletionStep) where
  refl := fun _ => .refl
  submit := by
    intro state who submission
    have publicEq := reactiveApplication_submit_publicView runtime leaks state who submission
    apply Relation.ReflTransGen.single
    refine Or.inl ⟨?_, congrArg PublicView.accepted publicEq,
      congrArg PublicView.activatedAt publicEq⟩
    change (submitStep (submission.call.register state who) who _).config = _
    rw [submitStep_config, (submission.call.register_facts who state).1]
  handle := by
    intro state message next accepted
    obtain ⟨native, handled, rfl⟩ := reactiveHandle_call accepted
    exact (Relation.ReflTransGen.single
      (completionStep_handle runtime state native _ handled)).trans native.drain_completionPath
  environment := by
    intro state command next reached
    change next ∈ ((environmentStep runtime state command).map State.drain).support at reached
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    exact (Relation.ReflTransGen.single
      (completionStep_environmentStep runtime state native command moved)).trans
        native.drain_completionPath

/-- Every scheduler command has a finite native completion footprint. -/
theorem completionPath_reactive_environmentStep
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    Relation.ReflTransGen CompletionStep execution.application next.application :=
  (reactiveApplication_completionPath runtime leaks).environmentStep execution next command reached

end Vegas.EventGraphRuntime
