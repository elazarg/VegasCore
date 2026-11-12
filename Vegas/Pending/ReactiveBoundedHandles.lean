module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveMenuInvariant
public import Interaction.ReactivePublication
public import Vegas.Pending.ReactiveFiniteResponses

@[expose] public section

/-! # Accepted handles stay inside the finite message domain

Every legal response of the bounded instance obeys the packet bounds. Passive
leaks and inclusion retain those bounds; accepted commitments therefore
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

def ExecutionHandles (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution) : Prop :=
  bounds.AcceptedHandles execution.application ∧
    execution.network.Satisfies (fun message => bounds.AllowsPacket message.payload.call)

theorem acceptedHandles_initial (inputs : graph.Inputs) :
    bounds.AcceptedHandles (State.initial inputs) := by
  intro field candidate accepted
  obtain ⟨input, owner, payload, _, _, rfl⟩ :=
    State.initial_accepted_eq_some inputs field candidate accepted
  trivial

theorem acceptedHandles_handle (timeouts : EventTimeouts graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (valid : bounds.AcceptedHandles state) (packet : bounds.AllowsPacket message.payload)
    (accepted : handle timeouts state message = some next) : bounds.AcceptedHandles next := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | commitment event candidate =>
      have tables := handle_commitment_tables timeouts state next id event candidate accepted
      intro field handle stored
      rw [tables.2.1] at stored
      by_cases current : field = .inr event
      · subst field
        rw [Function.update_self] at stored
        cases Option.some.inj stored
        exact packet
      · rw [Function.update_of_ne current] at stored
        exact valid field handle stored
  | opening event candidate raw =>
      have tables := handle_resolution_tables timeouts state next _ (by intros; simp) accepted
      simpa only [AcceptedHandles, tables.1] using valid
  | malformed raw => simp [handle] at accepted

theorem executionHandles_respond (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (valid : bounds.ExecutionHandles timeouts leaks execution)
    (allowed : ∀ material, response.transmission = some material →
      bounds.AllowsPacket material.call.packet) :
    bounds.ExecutionHandles timeouts leaks
      (execution.respond ((reactiveApplication timeouts) leaks) who response) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some material =>
      refine ⟨?_, valid.2.submit who
        (material.emit (((reactiveApplication timeouts) leaks).submit execution.application who
          material) who (execution.network.known who)) (allowed material rfl)⟩
      change bounds.AcceptedHandles
        (submitStep (material.call.register execution.application who) who material.call.packet)
      have same := congrArg PublicView.accepted
        (material.call.register_facts who execution.application).2
      change (material.call.register execution.application who).accepted =
        execution.application.accepted at same
      simpa only [AcceptedHandles, submitStep_accepted, same] using valid.1

theorem executionHandles_environment (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (valid : bounds.ExecutionHandles timeouts leaks execution)
    (reached : next ∈ (execution.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) : bounds.ExecutionHandles timeouts leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨valid.1, valid.2.learn who selected⟩
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      refine ⟨?_, ?_⟩
      · unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        cases found : execution.network.lookup id with
        | none => exact valid.1
        | some message =>
            change bounds.AcceptedHandles
              ((((reactiveApplication timeouts) leaks).handle execution.application
                message).getD execution.application)
            cases accepted : ((reactiveApplication timeouts) leaks).handle execution.application
                message with
            | none => exact valid.1
            | some state =>
                change bounds.AcceptedHandles state
                obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
                rw [← drained]
                simpa only [AcceptedHandles, native.drain_tables.1] using
                  bounds.acceptedHandles_handle timeouts execution.application
                    native ⟨message.id, message.payload.call⟩ valid.1
                    (valid.2.lookup id message found) handled
      · change (execution.includePending ((reactiveApplication timeouts) leaks)
        id).network.Satisfies _
        rw [ReactiveApplication.includePending_network]
        exact valid.2.includePending id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨?_, valid.2⟩
      simpa only [AcceptedHandles,
        (reactiveApplication_environment_tables timeouts leaks execution.application state command
          changed).1]
        using valid.1

/-- The same bounds hold before normalization, for every raw response admitted
by the complete finite menu. -/
theorem executionHandles_raw_history [Fintype Player] (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) :
    ∀ {state} (_trace : ((bounds.rawMenu timeouts leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant
        (bounds.ExecutionHandles timeouts leaks) state := by
  have invariant : (bounds.rawMenu timeouts leaks).ServiceInvariant scheduler
      (bounds.ExecutionHandles timeouts leaks) := {
    respond := fun execution who response valid legal =>
      bounds.executionHandles_respond timeouts leaks execution who response valid (by
        intro material submitted
        rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at legal
        rw [submitted] at legal
        exact ((bounds.submissions_mem _ _).mp legal).1.1)
    environment := fun execution next command valid _ reached =>
      bounds.executionHandles_environment timeouts leaks execution next command valid reached }
  intro state trace
  exact invariant.history (inputs.map State.initial) horizon (by
    intro state supported
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨bounds.acceptedHandles_initial input, MessageNetwork.Satisfies.empty⟩) trace

end Vegas.EventGraphRuntime.MessageBounds
