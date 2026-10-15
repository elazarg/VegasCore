/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedInclusion
import Vegas.Pending.PhaseResolutionPersistence

/-! # A surviving coordinate's nonactivation reply was an actual wait -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
private theorem decision_expiry_due (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph)
    (chosen : decision runtime delay bound coordinate seed input = .expiry) :
    runtime.deadline coordinate.1.event ≤ input.elapsed := by
  unfold decision at chosen
  split at chosen
  · assumption
  · split at chosen
    · cases chosen
    · dsimp only at chosen
      split at chosen <;> cases chosen

/-- A counted local include physically resolves its original event: an
immediate retry can retire the namespace instead of retaining the completed cell. -/
theorem inclusion_resolves_of_trace (delay bound : graph.EventId → Nat)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (seed : Seed runtime delay) (identifier : MessageId Player)
    (included : reply runtime leaks delay bound coordinate seed
      (queryAt runtime leaks execution coordinate owner) = .include identifier)
    (reached : next ∈ (execution.environmentStep app (.include identifier)).support) :
    coordinate.1.attempt ≠ next.application.attempt ∨
      coordinate.1.event ∈ next.application.current.native.config.cut.completed := by
  obtain ⟨message, authentic, sender, attempt, addressed, _, found, timely⟩ :=
    reply_inclusion_packet_of_trace runtime leaks delay bound bounds plan ordered maximal inputs
      horizon scheduler remaining execution trace coordinate owner request seed identifier included
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, coordinate.1.event⟩ := by
    simpa only [sender, attempt] using request
  have handled : ∃ native target,
      coordinate.1.event ∈ native.config.cut.completed ∧
      target = ({execution.application with current :=
        execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      (app).handle execution.application message = some target := by
    cases call : message.payload.packet.call with
    | malformed raw => rw [call] at addressed; cases addressed
    | commitment event candidate =>
        rw [call] at addressed
        cases Option.some.inj addressed
        obtain ⟨native, target, _, completed, _, normalized, accepted⟩ :=
          PhaseCount.binding_accepted_of_history runtime leaks bounds plan inputs horizon scheduler
            trace message authentic coordinate.1.event candidate call packetRequest timely
        refine ⟨native, target, completed, ?_, accepted⟩
        simpa only [call] using normalized
    | opening event candidate raw =>
        rw [call] at addressed
        cases Option.some.inj addressed
        obtain ⟨native, target, _, completed, normalized, accepted⟩ :=
          PhaseCount.opening_accepted_of_history runtime leaks bounds plan inputs horizon scheduler
            trace message authentic coordinate.1.event candidate raw call packetRequest timely
        refine ⟨native, target, completed, ?_, accepted⟩
        simpa only [call] using normalized
  obtain ⟨native, target, completed, normalized, accepted⟩ := handled
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    trace
  obtain ⟨_, _, namespaces, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  have resolved := PhaseRuntimeState.settle_resolves execution.application.phases
    execution.application.generation execution.application.entry
    (execution.application.current.inclusionResult message.payload.packet.call native)
    execution.application.retired namespaces.ordered coordinate.1.event completed
  let intermediate : PhaseRuntimeState graph :=
    {execution.application with current :=
      execution.application.current.inclusionResult message.payload.packet.call native}
  change execution.application.attempt ≠ intermediate.normalize.attempt ∨
    coordinate.1.event ∈ intermediate.normalize.current.native.config.cut.completed at resolved
  have targetEq : target = intermediate.normalize := normalized
  rw [← targetEq] at resolved
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  have actual : (execution.includePending app identifier).application = target := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  rw [actual, request.1]
  exact resolved

/-- Genuine tick draining cannot silently consume a rejected selected packet
in the clean game: if the selected physical request survives a nonactivation
reply, that reply was wait. Foreign and malformed raw traffic remains outside
this precise service-domain statement. -/
theorem nonactivation_wait_or_resolved (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (remaining : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
        ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority seeds.1 execution = some coordinate)
    (command : (app).Command)
    (chosen : command ∈ ((controller runtime leaks delay bound priority).family seeds
      execution.environmentRecall (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support)
    (idle : (command.actor? app).isNone = true) :
    command = .wait ∨ coordinate.1.Resolved next.application := by
  let scheduler := (controller runtime leaks delay bound priority).family seeds
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨input, valid, namespaces, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨owner, request⟩ := selected_request runtime leaks priority seeds.1 execution valid
    coordinate selected
  have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep execution
    next command reached namespaces.ordered
  have chosenEq := (PMF.mem_support_pure_iff _ _).mp chosen
  have actualReply : reply runtime leaks delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks execution coordinate owner) = command :=
    (choose_eq_reply runtime leaks delay bound priority seeds execution coordinate selected owner
      request.2.2.2.1).symm.trans chosenEq.symm
  cases decided : decision runtime delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks execution coordinate owner) with
  | activation =>
      have commandEq : command = .activate owner := by
        simpa only [reply, decided, request.2.2.2.1, Option.map_some, Option.getD_some] using
          actualReply.symm
      rw [commandEq] at idle
      cases idle
  | wait => exact Or.inl (by simpa only [reply, decided] using actualReply.symm)
  | inclusion index =>
      cases indexed : (queryAt runtime leaks execution coordinate owner).emissions[index]? with
      | none =>
          exact Or.inl (by
            simpa only [reply, decided, indexed, Option.map_none, Option.getD_none] using
              actualReply.symm)
      | some emission =>
          have commandEq : command = .include emission.identifier := by
            simpa only [reply, decided, indexed, Option.map_some, Option.getD_some] using
              actualReply.symm
          have moved := reached
          rw [commandEq] at moved
          have included := actualReply.trans commandEq
          have resolves := inclusion_resolves_of_trace runtime leaks delay bound bounds plan ordered
            maximal inputs horizon scheduler remaining execution next trace coordinate owner request
            (seeds.2 coordinate) emission.identifier included moved
          exact Or.inr (CommitAttemptEvent.Resolved.of_step coordinate.1 execution.application
            next.application request.1 progress resolves)
  | expiry =>
      have commandEq : command = .application (.expire coordinate.1.event) := by
        simpa only [reply, decided] using actualReply.symm
      have moved := reached
      rw [commandEq] at moved
      obtain ⟨updated, changed, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      have due := decision_expiry_due runtime delay bound coordinate (seeds.2 coordinate)
        (queryAt runtime leaks execution coordinate owner) decided
      have resolves := PhaseRuntimeState.expire_resolves_of_request runtime execution.application
        state valid namespaces.ordered request due nativeMoved
      exact Or.inr (CommitAttemptEvent.Resolved.of_step coordinate.1 execution.application
        state request.1 progress resolves)

/-- Once a physical coordinate has resolved it cannot return, even through later retries.
Thus every earlier selected nonactivation at a currently surviving coordinate was wait. -/
theorem nonactivation_wait_of_future_request (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (remaining : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
        ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority seeds.1 execution = some coordinate)
    (command : (app).Command)
    (chosen : command ∈ ((controller runtime leaks delay bound priority).family seeds
      execution.environmentRecall (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support)
    (futureScheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (final : (app).Execution)
    (continued : final ∈ ((app).runRounds futureScheduler players count next).support)
    (owner : Player) (survives : final.application.SeedRequest owner coordinate.1)
    (idle : (command.actor? app).isNone = true) : command = .wait := by
  rcases nonactivation_wait_or_resolved runtime leaks delay bound priority seeds bounds plan
      ordered maximal inputs horizon remaining execution next trace coordinate selected command
      chosen
      reached idle with waiting | resolved
  · exact waiting
  · let scheduler := (controller runtime leaks delay bound priority).family seeds
    have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
    obtain ⟨input, valid, namespaces, _⟩ :=
      currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
    have validNext := (phaseApplication_invariant runtime leaks input).environmentStep execution
      next command valid reached
    have orderedNext := (phaseApplication_seedOrder runtime leaks).environmentStep execution next
      command namespaces.ordered reached
    exact (CommitAttemptEvent.Resolved.no_request_runRounds runtime leaks coordinate.1
      futureScheduler players count next final validNext orderedNext resolved continued owner
      survives).elim

end Vegas.EventGraphRuntime.PhaseSeedCalendar
