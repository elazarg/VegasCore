/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionMiss
import Vegas.Pending.EventOpponentFrame

/-! # Completed unmarked decisions have an actual owner packet

On initialized raw histories, a completed strategic event either has a public
miss marker or an authenticated packet in its owner's recall. Samples cannot
complete strategic events, and expiry creates the marker. Accepted inclusion
uses actual network provenance. Earlier silent turns are therefore preserved
without manufacturing a source decision or assuming an earlier policy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def CompletedDecisionRecall (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ event who, graph.actor? event = some who →
    event ∈ execution.application.config.cut.completed →
      event ∉ execution.application.missedEvents →
        ∃ message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall who),
          message.sender = who ∧ message.payload.call.event? graph = some event

theorem completedDecisionRecall_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (actor : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (valid : runtime.CompletedDecisionRecall leaks execution) :
    runtime.CompletedDecisionRecall leaks
      (execution.respond (runtime.reactiveApplication leaks) actor response) := by
  let app := runtime.reactiveApplication leaks
  have same := runtime.reactive_respond_application leaks execution actor response
  have marked := congrArg PublicView.missedEvents same.2
  change
    (execution.respond app actor response).application.missedEvents =
      execution.application.missedEvents at marked
  intro event who owned completed clear
  obtain ⟨message, output, authored, named⟩ := valid event who owned (same.1 ▸ completed)
    (marked ▸ clear)
  obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
  exact ⟨message, List.mem_filterMap.mpr ⟨entry,
    (runtime.reactiveApplication leaks).respond_recall_mono execution actor who response member,
      emitted⟩, authored, named⟩

private theorem completedDecisionRecall_handle
    (execution : (runtime.reactiveApplication leaks).Execution) (next : State graph)
    (message : Message Player (WitnessedPacket graph))
    (valid : runtime.CompletedDecisionRecall leaks execution)
    (issued : execution.Issued (runtime.reactiveApplication leaks) message)
    (handled : handle runtime execution.application
      ⟨message.id, message.payload.call⟩ = some next) :
    runtime.CompletedDecisionRecall leaks { execution with application := next } := by
  intro event who owned completed clear
  have markerEq := handle_missedEvents runtime execution.application next
    ⟨message.id, message.payload.call⟩ handled
  by_cases prior : event ∈ execution.application.config.cut.completed
  · exact valid event who owned prior (markerEq ▸ clear)
  · obtain ⟨addressed, named, ready, action, stepped⟩ := handle_config_mem_step runtime
      execution.application next ⟨message.id, message.payload.call⟩ handled
    rw [execution.application.config.step_cut addressed ready action next.config stepped,
      EventOrder.Cut.mem_complete] at completed
    have same := completed.resolve_right prior
    subst addressed
    obtain ⟨actual, actualNamed, actor⟩ := handle_event_actor runtime execution.application next
      ⟨message.id, message.payload.call⟩ handled
    have actualEq := Option.some.inj (actualNamed.symm.trans named)
    subst actual
    have sender : message.sender = who := Option.some.inj (actor.symm.trans owned)
    obtain ⟨entry, member, _, _, emitted, _⟩ := issued
    rw [sender] at member
    exact ⟨message, List.mem_filterMap.mpr ⟨entry, member, emitted⟩, sender, named⟩

private theorem completedDecisionRecall_application
    (execution : (runtime.reactiveApplication leaks).Execution) (next : State graph)
    (command : EnvironmentCommand graph)
    (valid : runtime.CompletedDecisionRecall leaks execution)
    (reached : next ∈ (environmentStep runtime execution.application command).support) :
    runtime.CompletedDecisionRecall leaks { execution with application := next } := by
  intro event who owned completed clear
  have beforeClear : event ∉ execution.application.missedEvents :=
    fun missed => clear (environmentStep_missedEvents_subset runtime execution.application next
      command reached missed)
  by_cases prior : event ∈ execution.application.config.cut.completed
  · exact valid event who owned prior beforeClear
  · cases command with
    | advanceClock =>
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact (prior completed).elim
    | executeSample addressed =>
        rcases (environmentStep_executeSample_config_activated runtime execution.application
            next addressed reached).2 with unchanged | ⟨ready, action, stepped, _⟩
        · exact (prior (unchanged.1 ▸ completed)).elim
        · rw [execution.application.config.step_cut addressed ready action next.config stepped,
            EventOrder.Cut.mem_complete] at completed
          have same := completed.resolve_right prior
          subst addressed
          rw [environmentStep_executeSample_of_nonsample runtime execution.application event
            ready (fun payload law outputEq codeEq _node => by
              have actor : graph.actor? event = none :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                (congrArg EventCode.actor codeEq)
              rw [actor] at owned
              cases owned), PMF.mem_support_pure_iff _ _] at reached
          subst next
          exact (prior (execution.application.config.step_cut event ready action _ stepped ▸
            (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl))).elim
    | expire addressed =>
        rcases environmentStep_expire_config_eq_or_mem_step runtime execution.application next
            addressed reached with unchanged | ⟨ready, action, stepped⟩
        · exact (prior (unchanged ▸ completed)).elim
        · have completedAfter := completed
          rw [execution.application.config.step_cut addressed ready action next.config stepped,
            EventOrder.Cut.mem_complete] at completed
          have same := completed.resolve_right prior
          subst addressed
          cases activated : execution.application.activatedAt event with
          | none =>
              rw [environmentStep_expire_of_not_activated runtime execution.application event
                ready activated, PMF.mem_support_pure_iff _ _] at reached
              subst next
              exact (prior completedAfter).elim
          | some entered =>
              by_cases due : runtime.deadline event ≤ execution.application.clock - entered
              · apply (clear ?_).elim
                rw [environmentStep_expire_missedEvents runtime execution.application next event
                  reached]
                rw [ite_eq_left ⟨ready, ⟨entered, activated, due⟩, by rw [owned]; simp⟩]
                exact Finset.mem_insert_self _ _
              · rw [environmentStep_expire_of_not_due runtime execution.application event ready
                  entered activated due, PMF.mem_support_pure_iff _ _] at reached
                subst next
                exact (prior completedAfter).elim

theorem completedDecisionRecall_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : runtime.CompletedDecisionRecall leaks execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.CompletedDecisionRecall leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid
      | some message =>
          change runtime.CompletedDecisionRecall leaks { execution with
            application := ((runtime.reactiveApplication leaks).handle execution.application
              message).getD execution.application }
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none => exact valid
          | some state =>
              exact completedDecisionRecall_handle runtime leaks execution state message valid
                (origins.lookup id message found) (reactiveHandle_call accepted)
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact completedDecisionRecall_application runtime leaks execution state command valid changed

/-- Arbitrary player policies and authentic partial observation preserve the
completed-unmarked owner packet origin on every initialized raw history. -/
theorem completedDecisionRecall_history (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (runtime.CompletedDecisionRecall leaks) state := by
  have invariant : (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (fun execution => runtime.CompletedDecisionRecall leaks execution ∧
        execution.Provenance (runtime.reactiveApplication leaks)) := {
    respond := fun execution who response valid =>
      ⟨runtime.completedDecisionRecall_respond leaks execution who response valid.1,
        (runtime.reactiveApplication leaks).respond_provenance execution who response valid.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨runtime.completedDecisionRecall_environment leaks execution next command valid.1 valid.2
        reached, (runtime.reactiveApplication leaks).environment_provenance execution next command
          valid.2 reached⟩ }
  intro state trace
  have valid := invariant.history (inputs.map State.initial) horizon (by
    intro state supported
    obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, MessageNetwork.Satisfies.empty⟩
    intro event who _owned completed
    exact (Finset.notMem_empty event completed).elim) trace
  cases state with
  | none => trivial
  | some control => exact valid.1

end Vegas.EventGraphRuntime
