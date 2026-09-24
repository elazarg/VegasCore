/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMenuInvariant
import Interaction.MessageNetworkInvariant
import Interaction.ReactivePublication
import Vegas.Pending.ReactiveFiniteResponses

/-! # Accepted handles stay inside the finite message domain

Every legal response of the bounded instance obeys the packet bounds. Passive
leaks, replay and inclusion retain those bounds; accepted commitments therefore
reference encodable handles, including after arbitrary earlier deviations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph)

def AcceptedHandles (state : State graph) : Prop :=
  ∀ field candidate, state.accepted field = some candidate → bounds.AllowsHandle candidate

def ExecutionHandles (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  bounds.AcceptedHandles execution.application ∧
    execution.network.Satisfies (fun message => bounds.AllowsPacket message.payload)

theorem acceptedHandles_initial (inputs : graph.Inputs) :
    bounds.AcceptedHandles (State.initial inputs) := by
  intro field candidate accepted
  obtain ⟨input, owner, payload, _, _, rfl⟩ :=
    State.initial_accepted_eq_some inputs field candidate accepted
  trivial

theorem acceptedHandles_handle (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (valid : bounds.AcceptedHandles state) (packet : bounds.AllowsPacket message.payload)
    (accepted : handle runtime state message = some next) : bounds.AcceptedHandles next := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | commitment event candidate =>
      have tables := handle_commitment_tables runtime state next id event candidate accepted
      intro field handle stored
      rw [tables.2.1] at stored
      by_cases current : field = .inr event
      · subst field
        rw [Function.update_self] at stored
        cases Option.some.inj stored
        exact packet
      · rw [Function.update_of_ne current] at stored
        exact valid field handle stored
  | opening event candidate raw | withhold event =>
      have tables := handle_resolution_tables runtime state next _ (by intros; simp) accepted
      simpa only [AcceptedHandles, tables.1] using valid
  | malformed raw => simp [handle] at accepted

theorem executionHandles_respond [Fintype Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (valid : bounds.ExecutionHandles runtime leaks execution)
    (legal : response ∈ (bounds.menu runtime leaks).actions who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)) :
    bounds.ExecutionHandles runtime leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  have allowed := ((bounds.menu_mem runtime leaks who _ _ response).mp legal).1
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some transmission =>
      cases transmission with
      | replay id => exact ⟨valid.1, valid.2.replay who id⟩
      | submit material =>
          refine ⟨?_, valid.2.submit who material.packet allowed.1⟩
          change bounds.AcceptedHandles (submitStep (material.register execution.application who)
            who material.packet)
          have same := congrArg PublicView.accepted
            (material.register_facts who execution.application).2.2
          change (material.register execution.application who).accepted =
            execution.application.accepted at same
          simpa only [AcceptedHandles, submitStep_accepted, same] using valid.1

theorem executionHandles_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (valid : bounds.ExecutionHandles runtime leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : bounds.ExecutionHandles runtime leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact ⟨valid.1, valid.2.learn who selected⟩
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      refine ⟨?_, ?_⟩
      · unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        cases found : execution.network.lookup id with
        | none => exact valid.1
        | some message =>
            change bounds.AcceptedHandles
              ((handle runtime execution.application message).getD execution.application)
            cases accepted : handle runtime execution.application message with
            | none => exact valid.1
            | some state =>
                exact bounds.acceptedHandles_handle runtime execution.application
                  state message valid.1 (valid.2.lookup id message found) accepted
      · change (execution.includePending (runtime.reactiveApplication leaks) id).network.Satisfies _
        rw [ReactiveApplication.includePending_network]
        exact valid.2.includePending id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      refine ⟨?_, valid.2⟩
      simpa only [AcceptedHandles,
        (environmentStep_tables runtime execution.application state command changed).1]
        using valid.1

theorem executionHandles_history [Fintype Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((bounds.menu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant
        (bounds.ExecutionHandles runtime leaks) state := by
  have invariant : (bounds.menu runtime leaks).ServiceInvariant scheduler
      (bounds.ExecutionHandles runtime leaks) := {
    respond := bounds.executionHandles_respond runtime leaks
    environment := fun execution next command valid _ reached =>
      bounds.executionHandles_environment runtime leaks execution next command valid reached }
  intro state trace
  exact invariant.history (inputs.map State.initial) horizon (by
    intro state supported
    obtain ⟨input, _, rfl⟩ := FinDist.support_map .. ▸ supported
    exact ⟨bounds.acceptedHandles_initial input, MessageNetwork.Satisfies.empty⟩) trace

end Vegas.EventGraphRuntime.MessageBounds
