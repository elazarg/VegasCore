/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedBindingService
import Vegas.Pending.ReactiveCountedOpeningAcceptance
import Vegas.Pending.ReactiveTokenReadiness
import Vegas.Pending.ReactiveRiskPersistence
import Interaction.ReactiveOwnerSelection

/-! # Pending authentic packets at unfinished timely events -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem countCallCorrect_owned_event
    (earlier : Message Player (WitnessedPacket graph) → Prop)
    (message : Message Player (WitnessedPacket graph))
    (correct : CountCallCorrect earlier message) {event : graph.EventId}
    (named : message.payload.call.event? graph = some event) :
    graph.actor? event = some message.sender := by
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw => rw [call] at named; cases named
  | commitment named' handle =>
      rw [call] at named correct
      cases named
      have owned := correct.1
      unfold bindingOwnedBy at owned
      cases view : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          rw [outputEq] at owned
          have same : owner = message.sender := of_decide_eq_true owned
          rw [← same]
          exact graph.actor?_of_outputLayout_binding outputEq
      | resolve owner payload binding checks outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
      | sample payload law outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
  | opening named' handle raw =>
      rw [call] at named correct
      cases named
      obtain ⟨_, owned⟩ := correct
      cases view : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at owned
          rw [owned.1]
          exact (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
      | bind _ _ _ _ => rw [view] at owned; exact owned.elim
      | sample _ _ _ _ => rw [view] at owned; exact owned.elim

private theorem counted_call_resolves_of_history
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (clean : runtime.CountClean leaks control.execution)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event)
    (unmissed : control.execution.application.publicView.missedBindingBy message.sender = false)
    (ready : control.execution.application.config.cut.Ready event)
    (timely : control.execution.application.WithinDeadline runtime event) :
    ∃ next, (runtime.reactiveApplication leaks).handle control.execution.application message =
      some next ∧ event ∈ next.config.cut.completed := by
  cases call : message.payload.call with
  | malformed raw => rw [call] at named; cases named
  | commitment addressed candidate =>
      rw [call] at named
      cases named
      exact runtime.counted_binding_resolves_of_history leaks inputs horizon scheduler control
        trace clean message member event candidate call ready timely
  | opening addressed candidate raw =>
      rw [call] at named
      cases named
      obtain ⟨next, accepted⟩ := runtime.counted_opening_accepted leaks (inputs.map State.initial)
        (fun state supported => by
          obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨input, rfl⟩) horizon scheduler trace clean message member event candidate raw call
        unmissed ready timely
      refine ⟨next, accepted, ?_⟩
      obtain ⟨resolved, addressed, _, completed⟩ := handle_completes runtime _ _ _
        (reactiveHandle_call accepted)
      rw [call] at addressed
      change some event = some resolved at addressed
      rwa [Option.some.inj addressed]

private def CountedSurvivors (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, ∀ event,
    message.payload.call.event? graph = some event →
    execution.application.publicView.missedBindingBy message.sender = false →
    event ∉ execution.application.config.cut.completed →
    execution.application.WithinDeadline runtime event → message ∈ execution.network.pending

private theorem countedSurvivors_respond
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : CountedSurvivors runtime leaks execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    CountedSurvivors runtime leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  intro message member event named unmissed unfinished timely
  have same := runtime.reactive_respond_application leaks execution who action
  have unmissedBefore : execution.application.publicView.missedBindingBy message.sender = false :=
    same.2 ▸ unmissed
  have unfinishedBefore : event ∉ execution.application.config.cut.completed :=
    same.1 ▸ unfinished
  have timelyBefore : execution.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    have clock := congrArg PublicView.clock same.2
    have active := congrArg PublicView.activatedAt same.2
    dsimp only [State.publicView] at clock active
    rwa [clock, active] at timely
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact valid message member event named unmissedBefore unfinishedBefore timelyBefore
      | some material =>
          change message ∈ execution.network.inputs ++ [_] at member
          rcases List.mem_append.mp member with old | latest
          · exact (runtime.reactiveApplication leaks).respond_pending_mono execution who
              ⟨some material⟩ (valid message old event named unmissedBefore unfinishedBefore
                timelyBefore)
          · change message ∈ execution.network.pending ++ [_]
            exact List.mem_append_right _ latest

private theorem network_pending_retained_or_selected
    (network : MessageNetwork Player (WitnessedPacket graph)) (id : MessageId Player)
    (message : Message Player (WitnessedPacket graph)) (member : message ∈ network.pending) :
    message ∈ (network.includePending id).2.pending ∨ network.lookup id = some message := by
  let pool : MessagePool Player (WitnessedPacket graph) :=
    ⟨network.pending, network.ledger, fun _ => [], fun _ => [], network.nextSerial⟩
  have retained := pool.pending_retained_or_selected id message member
  cases found : network.pending.find? (fun packet => packet.id = id) <;>
    simpa only [MessagePool.includePending, MessagePool.lookup, MessageNetwork.includePending,
      MessageNetwork.lookup, MessagePool.Result.invalid, pool, found] using retained

private theorem countedSurvivors_environment
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (clean : runtime.CountClean leaks control.execution)
    (valid : CountedSurvivors runtime leaks control.execution)
    (next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (moved : next ∈ (control.execution.environmentStep
      (runtime.reactiveApplication leaks) command).support) :
    CountedSurvivors runtime leaks next := by
  intro message member event named unmissed unfinished timely
  have authentic : message ∈ control.execution.network.inputs := by
    rwa [(runtime.reactiveApplication leaks).environmentStep_inputs control.execution next command
      moved] at member
  have allowed := (countPermits_eq_true_iff _ _).mp (clean.2 message authentic)
  have owned := countCallCorrect_owned_event _ message allowed.2.1 named
  obtain ⟨input, _, invariant⟩ := runtime.reactive_history_invariant leaks inputs horizon scheduler
    trace
  have progress := runtime.reactive_environment_progress leaks input control.execution next command
    invariant moved
  have unfinishedBefore : event ∉ control.execution.application.config.cut.completed :=
    fun completed => unfinished (progress.completed completed)
  have ready := runtime.ready_of_authentic_token leaks (inputs.map State.initial) horizon
    scheduler trace message authentic allowed.1 event named unfinishedBefore
  have timelyBefore := progress.withinDeadline_before runtime invariant event ready
    (by rw [owned]; rfl) unfinished timely
  have unmissedBefore :
      control.execution.application.publicView.missedBindingBy message.sender = false := by
    cases prior : control.execution.application.publicView.missedBindingBy message.sender with
    | false => rfl
    | true =>
        have persists := runtime.publicMiss_environment leaks message.sender prior moved
        rw [unmissed] at persists
        cases persists
  have pending := valid message authentic event named unmissedBefore unfinishedBefore timelyBefore
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact pending
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact pending
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact pending
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rcases network_pending_retained_or_selected control.execution.network id message pending with
        retained | selected
      · change message ∈ (control.execution.includePending
          (runtime.reactiveApplication leaks) id).network.pending
        rw [(runtime.reactiveApplication leaks).includePending_network]
        exact retained
      · obtain ⟨state, accepted, completed⟩ := counted_call_resolves_of_history runtime leaks inputs
          horizon scheduler control trace clean message authentic event named unmissedBefore ready
          timelyBefore
        have contradiction : event ∈ (control.execution.includePending
            (runtime.reactiveApplication leaks) id).application.config.cut.completed := by
          simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            selected, accepted, Option.getD_some] using completed
        exact (unfinished contradiction).elim

variable [Fintype Player]

/-- In the clean one-packet game, authentic calls for unfinished timely events
remain pending while their sender has no public binding miss. Rejected unrelated
packets may still have been consumed by the service. -/
private theorem counted_survivors_history (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    ∀ {state} (_trace : ((bounds.onePacketMenu runtime leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (CountedSurvivors runtime leaks) state
  := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend before after prior joint legal reached valid =>
      change after ∈ ((runtime.reactiveApplication leaks).transition (inputs.map State.initial)
        horizon scheduler before joint).support at reached
      cases before with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro message member
          exact (List.not_mem_nil member).elim
      | some control =>
          have raw := (bounds.onePacketMenu runtime leaks).toRawTrace (inputs.map State.initial)
            horizon scheduler prior
          have clean := (bounds.onePacketMenu_countClean runtime leaks scheduler).history
            (inputs.map State.initial) horizon
            (fun state _ => runtime.countClean_initial leaks state)
            prior
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact countedSurvivors_respond runtime leaks execution valid who _
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, supported⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
                  exact countedSurvivors_environment runtime leaks inputs horizon scheduler _ raw
                    clean valid next command moved

/-- A clean authentic packet cannot have been consumed while its event remains
unfinished and within deadline, unless its sender already has a public binding miss. -/
theorem counted_survivor_pending (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (message : Message Player (WitnessedPacket graph))
    (authentic : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (named : message.payload.call.event? graph = some event)
    (unmissed : control.execution.application.publicView.missedBindingBy message.sender = false)
    (unfinished : event ∉ control.execution.application.config.cut.completed)
    (timely : control.execution.application.WithinDeadline runtime event) :
    message ∈ control.execution.network.pending :=
  counted_survivors_history runtime leaks bounds inputs horizon scheduler trace message authentic
    event named unmissed unfinished timely

end Vegas.EventGraphRuntime
