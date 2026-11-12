module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveInvariant
public import Vegas.Pending.ReactiveRuntime
public import Vegas.Pending.EventStore
public import Vegas.Pending.ExclusionInvariant
public import Vegas.Pending.ReactiveGraphSteps

@[expose] public section

/-! # Reachability and stored values in reactive continuations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveStateInvariant (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) :
    ((reactiveApplication timeouts) leaks).Invariant (State.Invariant inputs) where
  submit state who material valid := by
    apply valid.copy
    · exact (submitStep_config _ who material.call.packet).trans
        (material.call.register_facts who state).1
    · exact congrArg PublicView.clock
        ((submitStep_publicView _ who material.call.packet).trans
          (material.call.register_facts who state).2)
    · exact congrArg PublicView.activatedAt
        ((submitStep_publicView _ who material.call.packet).trans
          (material.call.register_facts who state).2)
  handle state message next valid accepted := by
    obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    exact (handle_invariant timeouts state native ⟨message.id, message.payload.call⟩
      valid handled).drain
  environment state command next valid supported := by
    change next ∈ ((environmentStep timeouts state command).map State.drain).support at supported
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ supported
    exact (environmentStep_invariant timeouts state native command valid moved).drain

theorem reactiveStoreInvariant (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (field : graph.Field)
    (value : (graph.layout field).Value) : ((reactiveApplication timeouts) leaks).Invariant
      (fun state => state.config.store field = some value) where
  submit state who material stored := by
    change (submitStep (material.call.register state who) who
      material.call.packet).config.store field = _
    rw [submitStep_config, (material.call.register_facts who state).1]
    exact stored
  handle state message next stored accepted := by
    obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    exact native.drain_store_of_some field value
      (handle_store_of_some timeouts state native ⟨message.id, message.payload.call⟩ handled
        field value stored)
  environment state command next stored supported := by
    change next ∈ ((environmentStep timeouts state command).map State.drain).support at supported
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ supported
    exact native.drain_store_of_some field value
      (environmentStep_store_of_some timeouts state native command moved field value stored)

/-- Every successful application operation leaves automatic service quiescent. -/
theorem reactiveQuiescentInvariant (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    ((reactiveApplication timeouts) leaks).Invariant
      (fun state => ∀ event, ¬ state.AutomaticReady event) where
  submit state who material clear := by
    have same : (((reactiveApplication timeouts) leaks).submit state who material).config =
        state.config :=
      (submitStep_config _ who material.call.packet).trans
        (material.call.register_facts who state).1
    intro event eligible
    apply clear event
    simpa only [State.AutomaticReady, same] using eligible
  handle state message next _clear accepted := by
    obtain ⟨native, _handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    exact native.drain_quiescent
  environment state command next _clear supported := by
    change next ∈ ((environmentStep timeouts state command).map State.drain).support at supported
    obtain ⟨native, _moved, rfl⟩ := PMF.support_map .. ▸ supported
    exact native.drain_quiescent

/-- Initialized physical histories never leave an automatic completion pending. -/
theorem reactive_history_quiescent (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) {state}
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant (fun state : State graph =>
      ∀ event, ¬ state.AutomaticReady event) state := by
  apply (reactiveQuiescentInvariant timeouts leaks).history
    (inputs.map State.initial) horizon scheduler ?_ trace
  intro state supported
  obtain ⟨setup, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
  intro event eligible
  obtain ⟨owner, _, inactive⟩ := eligible.owned
  exact Finset.notMem_empty owner inactive

/-- Every initialized native history satisfies the runtime invariant of some
supported setup: its configuration is reachable by the original graph rules,
exactly the ready strategic events carry an activation timestamp, and no
timestamp lies in the future. This allows arbitrary player responses,
scheduling, and passive observations. -/
theorem reactive_history_invariant (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) {state}
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant (fun state : State graph =>
      ∃ setup ∈ inputs.support, state.Invariant setup) state := by
  let preserved : ((reactiveApplication timeouts) leaks).Invariant
      (fun state : State graph => ∃ setup ∈ inputs.support, state.Invariant setup) := {
    submit := by
      rintro state who material ⟨setup, supported, valid⟩
      exact ⟨setup, supported,
        ((reactiveStateInvariant timeouts) leaks setup).submit state who material valid⟩
    handle := by
      rintro state message next ⟨setup, supported, valid⟩ accepted
      exact ⟨setup, supported,
        ((reactiveStateInvariant timeouts) leaks setup).handle state message next valid accepted⟩
    environment := by
      rintro state command next ⟨setup, supported, valid⟩ reached
      exact ⟨setup, supported,
        ((reactiveStateInvariant timeouts) leaks setup).environment state command next valid
          reached⟩ }
  exact preserved.history (inputs.map State.initial) horizon scheduler (by
    intro state supported
    obtain ⟨setup, chosen, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨setup, chosen, State.initial_invariant setup⟩) trace

end Vegas.EventGraphRuntime
