/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingAcceptance
import Vegas.Examples.CommitSeedBroadcastProperPolicy
import Vegas.Pending.PhaseCountedSurvivor
import Vegas.Pending.PhaseSeedEmissionUnique

/-! # Actual counted admission at each selected original late include -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def lateClock (good : Bool) : Nat := if good then 2 else 3

def lateIncludePosition (seeds : Seeds) (owner : Player) : Nat :=
  (if seeds.2 owner then 14 else 21) + (seeds.1.symm owner).val

private theorem lateIncludePosition_lt (seeds : Seeds) (owner : Player) :
    lateIncludePosition seeds owner < 28 := by
  have bounded := (seeds.1.symm owner).isLt
  unfold lateIncludePosition
  split <;> omega

private theorem lateIncludePosition_clock_lt (seeds : Seeds) (owner : Player) :
    originalClock (lateIncludePosition seeds owner) < 6 := by
  unfold lateIncludePosition
  generalize bitEq : seeds.2 owner = bit
  generalize rankEq : seeds.1.symm owner = rank
  cases bit <;> fin_cases rank <;> decide

theorem original_late_command (seeds : Seeds) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    originalCommand seeds (lateIncludePosition seeds owner) past view =
      lateCommand owner (seeds.2 owner) (lateClock (seeds.2 owner)) past view := by
  unfold lateIncludePosition
  generalize rankEq : seeds.1.symm owner = rank
  have named : seeds.1 rank = owner := by
    rw [← rankEq]
    exact seeds.1.apply_symm_apply owner
  cases bitEq : seeds.2 owner <;> fin_cases rank
  all_goals first
    | exact (congrArg (fun who => lateCommand who (seeds.2 who) 3 past view) named).trans
        (congrArg (fun good => lateCommand owner good 3 past view) bitEq)
    | exact (congrArg (fun who => lateCommand who (seeds.2 who) 2 past view) named).trans
        (congrArg (fun good => lateCommand owner good 2 past view) bitEq)

/-- A ready eligible original envelope is the actual pending packet selected
by the late command. Its physical identity and timing do not depend on its
private preparation or evidence request. -/
theorem original_late_ready_packet (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (position : execution.environmentRecall.length =
      lateIncludePosition seeds owner)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock (seeds.2 owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    message ∈ execution.network.inputs ∧ message.sender = owner ∧
      message.payload.attempt = originalAttempt ∧
      message.payload.packet.call.event? graph = some (bindingEvent owner) ∧
      execution.network.lookup message.id = some message ∧
      execution.application.current.native.WithinDeadline runtime (bindingEvent owner) ∧
      choose seeds execution.environmentRecall (execution.observeEnvironment app) =
        .«include» message.id := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have valid := raw_native_valid (family seeds) _ raw
  have readyOwner : ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    apply decide_eq_true
    have visible := (execution.application.requests_publicView valid owner
      (originalCoordinate owner)).mpr request
    change PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩
    rw [original]
    exact visible
  have stamp := original_timer (family seeds) _ raw original owner request.2.2.1.1
  change execution.application.current.native.activatedAt (bindingEvent owner) = some 0 at stamp
  have timely : execution.application.current.native.WithinDeadline runtime
      (bindingEvent owner) := by
    rw [State.WithinDeadline, stamp]
    change execution.application.current.native.clock - 0 < 6
    rw [Nat.sub_zero, original_clock_index seeds _ raw original, position]
    exact lateIncludePosition_clock_lt seeds owner
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seeds) remaining execution trace
  have recalled := app.history_inputRecall initial horizon (family seeds) raw
  obtain ⟨input, authored, tagged, named⟩ := PhaseSeedScheduler.localInput_emission_authentic
    runtime leaks execution (originalCoordinate owner) owner words recalled _ message emitted
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, bindingEvent owner⟩ := by
    rw [authored, tagged]
    change execution.application.SeedRequest owner (originalCoordinate owner)
    exact request
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  have pending := PhaseCount.survivor_pending runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (compiledRuntimePhasePlan_maximal program .concurrentReveals)
    (setup.initialLaw.map encodeInputs)
      horizon (family seeds) _ compiledTrace message input (bindingEvent owner) named
        packetRequest timely
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds (family seeds)).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have unique := app.input_identifier_injective_history initial horizon (family seeds)
    ⟨remaining, none, execution⟩ raw
  have singleton := PhaseSeedScheduler.localInput_emissions_eq_singleton runtime leaks execution
    (originalCoordinate owner) owner words clean
      (fun first firstInput second secondInput same =>
        unique first second firstInput secondInput same) _ message emitted
  have pendingAny : (execution.observeEnvironment app).network.pending.any
      (fun packet => packet.id = message.id) = true := by
    exact List.any_eq_true.mpr ⟨message, pending, by simp only [decide_true]⟩
  have chosen : choose seeds execution.environmentRecall (execution.observeEnvironment app) =
      .include message.id := by
    rw [choose_original seeds _ _ original, position, original_late_command]
    simp [lateCommand, readyOwner, singleton, pendingCommand, pendingAny, lateClock]
  obtain ⟨actual, lookup⟩ := Option.isSome_iff_exists.mp (show
      (execution.network.lookup message.id).isSome = true from
    List.find?_isSome.mpr ⟨message, pending, by simp only [decide_true]⟩)
  have namedIdentifier := List.find?_some lookup
  have actualId : actual.id = message.id := by
    change decide (actual.id = message.id) = true at namedIdentifier
    exact of_decide_eq_true namedIdentifier
  have actualInput := (app.retained_envelopes_mem_inputs execution
    (app.history_provenance initial horizon (family seeds) raw) recalled).lookup message.id actual
      lookup
  have identical := unique actual message actualInput input actualId
  subst actual
  exact ⟨input, authored, tagged, named, lookup, timely, chosen⟩

/-- Actual counted late binding admission retains the raw native handler
result and its normalized application state for arbitrary private preparation. -/
theorem original_late_binding_admission (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (position : execution.environmentRecall.length =
      lateIncludePosition seeds owner)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock (seeds.2 owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment (bindingEvent owner) candidate) :
    ∃ native next,
      message ∈ execution.network.inputs ∧ message.sender = owner ∧
      message.payload.attempt = originalAttempt ∧
      execution.network.lookup message.id = some message ∧
      execution.application.current.native.WithinDeadline runtime (bindingEvent owner) ∧
      choose seeds execution.environmentRecall (execution.observeEnvironment app) =
        .«include» message.id ∧
      handle runtime execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      bindingEvent owner ∈ native.config.cut.completed ∧
      native.accepted (.inr (bindingEvent owner)) = some candidate ∧
      next = ({ execution.application with current :=
        execution.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize ∧
      app.handle execution.application message = some next := by
  obtain ⟨input, authored, tagged, _named, lookup, timely, chosen⟩ :=
    original_late_ready_packet seeds remaining execution trace owner position request message
      emitted
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, bindingEvent owner⟩ := by
    rw [authored, tagged]
    exact request
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  obtain ⟨native, next, handled, completed, accepted, normalized, phaseHandled⟩ :=
    PhaseCount.binding_accepted_of_history runtime leaks bounds plan (setup.initialLaw.map
      encodeInputs) horizon (family seeds) compiledTrace message input (bindingEvent owner)
        candidate call
        packetRequest timely
  exact ⟨native, next, input, authored, tagged, lookup, timely, chosen, handled, completed,
    accepted, normalized, phaseHandled⟩

/-- At its selected original late include, any genuine counted envelope emitted
at the eligible clock actually has a true receipt after the command. The source
request is derived from the actual history, including arbitrary preparations. -/
theorem original_late_emission_accepted (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (position : execution.environmentRecall.length =
      lateIncludePosition seeds owner)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (lateClock (seeds.2 owner), message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions)
    (moved : next ∈ (execution.environmentStep app
      (choose seeds execution.environmentRecall (execution.observeEnvironment app))).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner next := by
  classical
  by_cases earlier : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      execution
  · obtain ⟨packet, input, authored, stamp, named, receipt⟩ := earlier
    refine ⟨packet, ?_, authored, stamp, named, ?_⟩
    · rwa [app.environmentStep_inputs execution next _ moved]
    · exact (app.environmentStep_receipts_prefix execution next _ moved).subset receipt
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have early : execution.environmentRecall.length < 28 := by
    rw [position]
    exact lateIncludePosition_lt seeds owner
  have request := original_request_of_unaccepted_before_expiry seeds _ raw owner earlier early
  obtain ⟨input, authored, tagged, named, lookup, timely, chosen⟩ :=
    original_late_ready_packet seeds remaining execution trace owner position request message
      emitted
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, bindingEvent owner⟩ := by
    rw [authored, tagged]
    exact request
  rw [chosen] at moved
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  obtain ⟨_native, target, _completed, _normalized, handled⟩ :=
    PhaseCount.counted_call_resolves_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon (family seeds) compiledTrace message input
        (bindingEvent owner) named packetRequest timely
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
  cases (PMF.mem_support_pure_iff _ _).mp moved
  refine ⟨message, ?_, authored, tagged, named, ?_⟩
  · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      lookup] using input
  · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      lookup, handled, Option.isSome_some]
    exact List.mem_append_right _ (List.mem_singleton_self _)

end Vegas.Examples.CommitSeedBroadcast
