/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionInvariant
import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.ReactiveEventStability

/-! # Public failure evidence under native completion

Completed omissions and failed publications are public facts. Native completion
preserves every earlier event's exact failure verdict, and automatic excluded
service supplies a typed failure completion with complete receipt provenance.
These local facts are independent of a saved exclusion frontier.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

/-- Public failure means a completed binding lacking an accepted handle or a
failed public resolution. Hidden binding values are irrelevant. -/
def PublicFailure (state : State graph) (event : graph.EventId) : Prop :=
  state.publicView.missedBinding event = true ∨
    RecoveryState.publicationFailed state event = true

/-- Accepted event handles belong only to completed events. -/
def ReceiptsComplete (state : State graph) : Prop :=
  ∀ event candidate, state.accepted (.inr event) = some candidate →
    event ∈ state.config.cut.completed

theorem ReceiptsComplete.initial (inputs : graph.Inputs) :
    (State.initial inputs).ReceiptsComplete := by
  intro event candidate accepted
  obtain ⟨input, _, _, impossible, _, _⟩ := initial_accepted_eq_some inputs _ candidate accepted
  cases impossible

omit [DecidableEq Player] in
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
        unfold RecoveryState.publicationFailed at publication
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
  have publication : RecoveryState.publicationFailed after event =
      RecoveryState.publicationFailed before event := by
    unfold RecoveryState.publicationFailed
    cases nodeView graph event <;> simp only [output]
  rw [omitted, publication]

omit [DecidableEq Player] in
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
  suffices RecoveryState.publicationFailed after event =
      RecoveryState.publicationFailed before event by rw [this]
  cases view : nodeView graph event with
  | bind | sample => simp only [RecoveryState.publicationFailed, view]
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
      simp only [RecoveryState.publicationFailed, view, storeEq]

omit [DecidableEq Player] in
theorem completed_event_eq_of_step {before after : State graph} {event : graph.EventId}
    {ready : before.config.cut.Ready event} {action : graph.Action event}
    (member : after.config ∈ (before.config.step event ready action).support)
    {query : graph.EventId} (unfinished : query ∉ before.config.cut.completed)
    (completed : query ∈ after.config.cut.completed) : query = event := by
  rw [before.config.step_cut event ready action after.config member,
    EventOrder.Cut.mem_complete] at completed
  exact completed.resolve_right unfinished

omit [DecidableEq Player] in
theorem completeFailure_completionStep (native : State graph) (event : graph.EventId)
    (ready : native.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    CompletionStep native (native.completeFailure event ready) := by
  obtain ⟨action, member⟩ := native.completeFailure_step event ready acting
  refine Or.inr ⟨event, ready, action, member,
    native.completeFailure_activated event ready acting, ?_⟩
  intro field changed
  exact (changed (congrFun (native.completeFailure_tables event ready).1 field)).elim

omit [DecidableEq Player] in
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
      simpa only [State.completeFailure, view] using
        native.missedBinding_complete event ready _ _ actor payload outputEq
          (valid.vacant ready.1)
  | resolve actor payload binding checks outputEq codeEq =>
      right
      simp [RecoveryState.publicationFailed, State.completeFailure, view, State.complete]

end State

omit [DecidableEq Player] in
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

end Vegas.EventGraphRuntime
