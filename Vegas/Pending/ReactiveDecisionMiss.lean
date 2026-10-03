/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveProvenance

/-! # Actual public missed decisions

The contract marks strategic events completed by expiry. Accepted decisions,
including explicit withholding, leave the marker unchanged. The public audit
uses this marker for every owned event; partial network observations never
create or remove it. Its completion and packet-origin properties below concern
actual initialized histories, rather than arbitrary uses of
`Vegas.EventGraphRuntime.State.complete`.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
/-- A publicly marked decision is attributed to its declared actor. -/
def PublicView.missedDecisionBy (view : PublicView graph) (who : Player) : Bool :=
  decide (∃ event ∈ view.missedEvents, graph.actor? event = some who)

theorem PublicView.missedDecisionBy_of_event (view : PublicView graph) (who : Player)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (missed : event ∈ view.missedEvents) : view.missedDecisionBy who = true := by
  classical
  exact decide_eq_true ⟨event, missed, owned⟩

theorem PublicView.missedDecisionBy_eq_false_iff (view : PublicView graph) (who : Player) :
    view.missedDecisionBy who = false ↔
      ∀ event, graph.actor? event = some who → event ∉ view.missedEvents := by
  classical
  simp only [missedDecisionBy, decide_eq_false_iff_not, not_exists, not_and]
  constructor
  · intro clear event owned missed
    exact clear event missed owned
  · intro clear event missed owned
    exact clear event owned missed

theorem PublicView.missedDecisionBy_clear (view : PublicView graph)
    (clear : view.missedEvents = ∅) (who : Player) : view.missedDecisionBy who = false := by
  rw [view.missedDecisionBy_eq_false_iff who]
  intro event _owned
  rw [clear]
  exact Finset.notMem_empty event

omit [DecidableEq Player] in
/-- Application commands can only add public missed-decision markers. -/
theorem environmentStep_missedEvents_subset (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (reached : next ∈ (environmentStep runtime state command).support) :
    state.missedEvents ⊆ next.missedEvents := by
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Finset.Subset.rfl
  | executeSample event =>
      rw [environmentStep_executeSample_missedEvents runtime state next event reached]
  | expire event =>
      rw [environmentStep_expire_missedEvents runtime state next event reached]
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.rfl

/-- Every raw response and environment command preserves an existing marker. -/
theorem reactiveMissedDecisionInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) : (runtime.reactiveApplication leaks).Invariant
      (fun state => event ∈ state.missedEvents) where
  submit state who material missed := by
    have same := congrArg PublicView.missedEvents
      (runtime.reactiveApplication_submit_publicView leaks state who material)
    change ((runtime.reactiveApplication leaks).submit state who material).missedEvents =
      state.missedEvents at same
    rw [same]
    exact missed
  handle state message next missed accepted := by
    rw [handle_missedEvents runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)]
    exact missed
  environment state command next missed reached :=
    environmentStep_missedEvents_subset runtime state next command reached missed

omit [DecidableEq Player] in
/-- A new marker identifies the exact due strategic expiry that created it. -/
theorem environmentStep_new_missedEvent (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (reached : next ∈ (environmentStep runtime state command).support)
    (event : graph.EventId) (clear : event ∉ state.missedEvents)
    (missed : event ∈ next.missedEvents) :
    command = .expire event ∧ state.config.cut.Ready event ∧
      (∃ entered, state.activatedAt event = some entered ∧
        runtime.deadline event ≤ state.clock - entered) ∧ graph.actor? event ≠ none := by
  classical
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (clear missed).elim
  | executeSample addressed =>
      rw [environmentStep_executeSample_missedEvents runtime state next addressed reached]
        at missed
      exact (clear missed).elim
  | expire addressed =>
      rw [environmentStep_expire_missedEvents runtime state next addressed reached] at missed
      split at missed
      · rename_i actual
        have same := (Finset.mem_insert.mp missed).resolve_right clear
        subst addressed
        exact ⟨rfl, actual⟩
      · exact (clear missed).elim

/-- Network inclusion and passive observations cannot create a marker. -/
theorem reactive_new_missedEvent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {before after : (runtime.reactiveApplication leaks).Execution}
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : after ∈ (before.environmentStep (runtime.reactiveApplication leaks)
      command).support) (event : graph.EventId)
    (clear : event ∉ before.application.missedEvents)
    (missed : event ∈ after.application.missedEvents) :
    command = .application (.expire event) ∧ before.application.config.cut.Ready event ∧
      (∃ entered, before.application.activatedAt event = some entered ∧
        runtime.deadline event ≤ before.application.clock - entered) ∧
      graph.actor? event ≠ none := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  cases command with
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact (clear missed).elim
  | activate who =>
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact (clear missed).elim
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending at missed
      cases found : before.network.lookup id with
      | none => simp only [found] at missed; exact (clear missed).elim
      | some message =>
          simp only [found] at missed
          cases handled : (runtime.reactiveApplication leaks).handle before.application message
          with
          | none =>
              simp only [handled, Option.getD_none] at missed
              exact (clear missed).elim
          | some state =>
              simp only [handled, Option.getD_some] at missed
              rw [handle_missedEvents runtime before.application state
                ⟨message.id, message.payload.call⟩ (reactiveHandle_call handled)] at missed
              exact (clear missed).elim
  | application command =>
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      obtain ⟨rfl, ready, activated, strategic⟩ := environmentStep_new_missedEvent runtime
        before.application state command changed event clear missed
      exact ⟨rfl, ready, activated, strategic⟩

omit [DecidableEq Player] in
private theorem expiry_completes (runtime : EventGraphRuntime graph)
    (state next : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (entered : Nat)
    (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (strategic : graph.actor? event ≠ none)
    (reached : next ∈ (environmentStep runtime state (.expire event)).support) :
    event ∈ next.config.cut.completed := by
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      exact (strategic ((EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
        (congrArg EventCode.actor codeEq))).elim
  | bind owner payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq runtime state event ready entered activated due owner
        payload outputEq codeEq node, PMF.mem_support_pure_iff _ _] at reached
      subst next
      exact Finset.mem_insert_self _ _
  | resolve owner payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq runtime state event ready entered activated due owner
        payload binding checks outputEq codeEq node, PMF.mem_support_pure_iff _ _] at reached
      subst next
      exact Finset.mem_insert_self _ _

/-- Marker wellformedness is preserved by actual application transitions. -/
theorem reactiveMissedEventsWellFormed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant (fun state =>
      ∀ event ∈ state.missedEvents,
        event ∈ state.config.cut.completed ∧ graph.actor? event ≠ none) where
  submit state who material valid := by
    have same := runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩
    intro event missed
    have marked := congrArg PublicView.missedEvents same.2
    change ((runtime.reactiveApplication leaks).submit state who material).missedEvents =
      state.missedEvents at marked
    change event ∈ ((runtime.reactiveApplication leaks).submit state who material).missedEvents
      at missed
    have prior := valid event (marked ▸ missed)
    exact ⟨same.1 ▸ prior.1, prior.2⟩
  handle state message next valid handled := by
    intro event missed
    rw [handle_missedEvents runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call handled)] at missed
    have prior := valid event missed
    exact ⟨handle_completed_subset runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call handled) prior.1, prior.2⟩
  environment state command next valid reached := by
    intro event missed
    by_cases prior : event ∈ state.missedEvents
    · exact ⟨environmentStep_completed_subset runtime state next command reached
        (valid event prior).1, (valid event prior).2⟩
    · obtain ⟨rfl, ready, ⟨entered, activated, due⟩, strategic⟩ :=
        environmentStep_new_missedEvent runtime state next command reached event prior missed
      exact ⟨expiry_completes runtime state next event ready entered activated due strategic
        reached, strategic⟩

/-- Every marker in a legal initialized raw history names a completed strategic event. -/
theorem missedEvents_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    ∀ event ∈ control.execution.application.missedEvents,
      event ∈ control.execution.application.config.cut.completed ∧ graph.actor? event ≠ none :=
  (runtime.reactiveMissedEventsWellFormed leaks).history (inputs.map State.initial) horizon
    scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      simp only [State.initial_missedEvents, Finset.notMem_empty, false_implies, implies_true])
    trace

end Vegas.EventGraphRuntime
