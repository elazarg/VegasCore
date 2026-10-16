/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCurrentTokens
import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseOpeningAcceptance
import Vegas.Pending.ReactiveTokenReadiness
import Interaction.MessageNetworkSelection
import Interaction.ReactiveOwnerSelection

/-! # Authentic timely packets of a surviving physical attempt remain pending -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private def CountedSurvivors (execution : (app).Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, ∀ event,
    message.payload.packet.call.event? graph = some event →
    execution.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩ →
    execution.application.current.native.WithinDeadline runtime event →
      message ∈ execution.network.pending

omit [Fintype Player] in
private theorem countedSurvivors_respond {inputs : graph.Inputs}
    (execution : (app).Execution) (valid : execution.application.Invariant inputs)
    (survivors : CountedSurvivors runtime leaks execution) (who : Player) (action : (app).Action) :
    CountedSurvivors runtime leaks (execution.respond app who action) := by
  intro message member event named request timely
  have nextValid := (phaseApplication_invariant runtime leaks inputs).respond execution who action
    valid
  have publicEq : (execution.respond app who action).application.publicView =
      execution.application.publicView := by
    obtain ⟨transmission⟩ := action
    cases transmission with
    | none => rfl
    | some material => exact submit_publicView execution.application who material
  have requested := (PhaseRuntimeState.requests_publicView _ nextValid message.sender
    ⟨message.payload.attempt, event⟩).mpr request
  rw [publicEq] at requested
  have beforeRequest := (PhaseRuntimeState.requests_publicView _ valid message.sender
    ⟨message.payload.attempt, event⟩).mp requested
  have progress : State.ServiceProgress inputs 0 execution.application.current.native
      (execution.respond app who action).application.current.native := by
    obtain ⟨transmission⟩ := action
    cases transmission with
    | none => exact State.ServiceProgress.refl valid.active
    | some material =>
        exact execution.application.submit_progress who material valid.active
  have beforeTimely := progress.withinDeadline_before runtime valid.active event beforeRequest.2.2.1
    (by rw [request.2.2.2.1]; rfl) request.2.2.1.1 timely
  obtain ⟨transmission⟩ := action
  cases transmission with
  | none => exact survivors message member event named beforeRequest beforeTimely
  | some material =>
      change message ∈ execution.network.inputs ++ [_] at member
      rcases List.mem_append.mp member with previous | latest
      · exact (app).respond_pending_mono execution who ⟨some material⟩
          (survivors message previous event named beforeRequest beforeTimely)
      · change message ∈ execution.network.pending ++ [_]
        exact List.mem_append_right _ latest

/-- An authentic timely named call of a currently requested counted event
is accepted and completes that event before ordinary phase normalization. -/
theorem counted_call_resolves_of_history (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (named : message.payload.packet.call.event? graph = some event)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event) :
    ∃ native next,
      event ∈ native.config.cut.completed ∧
      next = ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧ (app).handle control.execution.application message =
            some next := by
  cases call : message.payload.packet.call with
  | malformed raw => rw [call] at named; cases named
  | commitment addressed candidate =>
      rw [call] at named
      cases named
      obtain ⟨native, next, _, completed, _, normalized, accepted⟩ :=
        binding_accepted_of_history runtime leaks bounds plan inputs horizon scheduler trace message
          member event candidate call request timely
      refine ⟨native, next, completed, ?_, accepted⟩
      simpa only [call] using normalized
  | opening addressed candidate raw =>
      rw [call] at named
      cases named
      obtain ⟨native, next, _, completed, normalized, accepted⟩ :=
        opening_accepted_of_history runtime leaks bounds plan inputs horizon scheduler trace message
          member event candidate raw call request timely
      refine ⟨native, next, completed, ?_, accepted⟩
      simpa only [call] using normalized

private theorem countedSurvivors_environment (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (survivors : CountedSurvivors runtime leaks control.execution)
    (next : (app).Execution) (command : (app).Command)
    (moved : next ∈ (control.execution.environmentStep app command).support) :
    CountedSurvivors runtime leaks next := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := (onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace
  have clean := (onePacketMenu_countClean runtime leaks bounds scheduler).history initial horizon
    (fun state _ => countClean_initial runtime leaks state) trace
  obtain ⟨input, valid, namespaces, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  have geometry := (phaseApplication_quiescent runtime leaks ordered).history initial horizon
    scheduler (fun state supported => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact phaseApplication_initial_quiescent plan ordered maximal input) raw
  have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan input,
        PhaseRuntimeState.initial_live plan input⟩) raw
  intro message member event named request timely
  have authentic : message ∈ control.execution.network.inputs := by
    rwa [(app).environmentStep_inputs control.execution next command moved] at member
  have allowed := (permits_eq_true_iff _ _).mp (clean.2 message authentic)
  have current : message.payload.attempt = next.application.attempt := request.1
  have same := InputNamespaces.current_before runtime leaks namespaces command moved message
    authentic current
  obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).environmentStep
    control.execution next command moved input valid namespaces.ordered same
  have unfinishedBefore :
      event ∉ control.execution.application.current.native.config.cut.completed :=
    fun complete => request.2.2.1.1 (progress.completed complete)
  have ready := ready_of_current_authentic_token runtime leaks plan inputs horizon scheduler raw
    message authentic (current.trans same.symm) allowed.1 event named unfinishedBefore
  have currentBefore : message.payload.attempt = control.execution.application.attempt :=
    current.trans same.symm
  have requestBefore : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩ := by
    simpa only [currentBefore] using control.execution.application.request_of_ready ordered
      geometry.1 living.2 geometry.2.1 geometry.2.2 event ready message.sender request.2.2.2.1
  have timelyBefore := progress.withinDeadline_before runtime valid.active event ready
    (by rw [request.2.2.2.1]; rfl) request.2.2.1.1 timely
  have pending := survivors message authentic event named requestBefore timelyBefore
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact pending
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact pending
  | application native =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact pending
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rcases control.execution.network.pending_retained_or_selected identifier message pending with
        retained | selected
      · change message ∈ (control.execution.includePending app identifier).network.pending
        rw [(app).includePending_network]
        exact retained
      · obtain ⟨native, target, completed, normalized, accepted⟩ :=
          counted_call_resolves_of_history runtime leaks bounds plan inputs horizon scheduler trace
            message authentic event named requestBefore timelyBefore
        have resolved := PhaseRuntimeState.settle_resolves control.execution.application.phases
          control.execution.application.generation control.execution.application.entry
          (control.execution.application.current.inclusionResult message.payload.packet.call native)
          control.execution.application.retired namespaces.ordered event completed
        let updated := control.execution.application.current.inclusionResult
          message.payload.packet.call native
        let intermediate : PhaseRuntimeState graph :=
          {control.execution.application with current := updated}
        let installed := intermediate.normalize
        change control.execution.application.attempt ≠ installed.attempt ∨
          event ∈ installed.current.native.config.cut.completed at resolved
        have installedEq : target = installed := normalized
        rw [← installedEq] at resolved
        have actual : (control.execution.includePending app identifier).application = target := by
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            selected, accepted, Option.getD_some]
        rw [actual] at same request
        rcases resolved with retired | done
        · exact (retired same).elim
        · exact (request.2.2.1.1 done).elim

private theorem counted_survivors_history (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) :
    ∀ {state} (_trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (CountedSurvivors runtime leaks) state := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend before after prior joint legal reached ih =>
      change after ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler before joint).support at reached
      cases before with
      | none =>
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro message member
          exact (List.not_mem_nil member).elim
      | some control =>
          have raw := (onePacketMenu runtime leaks bounds).toRawTrace
            (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler prior
          obtain ⟨input, valid, _, _⟩ :=
            currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact countedSurvivors_respond runtime leaks execution valid ih who _
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact ih
              | succ remaining =>
                  obtain ⟨command, _, supported⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
                  exact countedSurvivors_environment runtime leaks bounds plan ordered maximal
                    inputs horizon scheduler _ prior ih next command moved

/-- In genuine count-clean phased histories, an authentic packet for a ready
current-attempt event cannot have been consumed while still timely. Retirement
may void the semantic output, but then the original physical request is gone. -/
theorem survivor_pending (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (authentic : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (named : message.payload.packet.call.event? graph = some event)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event) :
    message ∈ control.execution.network.pending :=
  counted_survivors_history runtime leaks bounds plan ordered maximal inputs horizon scheduler trace
    message authentic event named request timely

end Vegas.EventGraphRuntime.PhaseCount
