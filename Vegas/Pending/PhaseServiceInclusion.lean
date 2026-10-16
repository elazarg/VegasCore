/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceTiming
import Vegas.Pending.PhaseSeedInclusion

/-! # Authentic resolving inclusions for arbitrary timed local service rules -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every selected identifier occurs in the actual local emission word and
is selected strictly before the deadline; the rule's inclusion order is free. -/
theorem reply_inclusion_witness
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (coordinate : PhaseSeedAddress graph) (seed : LocalSeed)
    (input : PhaseSeedOperationalInput graph) (identifier : MessageId Player)
    (included : reply runtime leaks decideLocal coordinate seed input = .include identifier) :
    ∃ emission ∈ input.emissions, emission.identifier = identifier ∧
      input.elapsed < runtime.deadline coordinate.1.event := by
  have timely : input.elapsed < runtime.deadline coordinate.1.event := by
    by_contra late
    have expired := (timed coordinate seed input).mpr (Nat.le_of_not_gt late)
    simp only [reply, expired, reduceCtorEq] at included
  unfold reply at included
  cases decided : decideLocal coordinate seed input with
  | activation =>
      cases acting : graph.actor? coordinate.1.event <;> simp [decided, acting] at included
  | inclusion index =>
      cases indexed : input.emissions[index]? with
      | none => simp only [decided, indexed, Option.map_none, Option.getD_none,
          reduceCtorEq] at included
      | some emission =>
          have identifierEq : emission.identifier = identifier := by
            simpa only [decided, indexed, Option.map_some, Option.getD_some,
              ReactiveApplication.Command.include.injEq] using included
          exact ⟨emission, List.mem_of_getElem? indexed, identifierEq, timely⟩
  | expiry => simp only [decided, reduceCtorEq] at included
  | wait => simp only [decided, reduceCtorEq] at included

/-- At a genuine clean idle history, the selected erased identifier is the
actual pending own packet, even with arbitrary prior retries and handle choices. -/
theorem reply_inclusion_packet_of_trace
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (seed : LocalSeed) (identifier : MessageId Player)
    (included : reply runtime leaks decideLocal coordinate seed
      (queryAt runtime leaks execution coordinate owner) = .include identifier) :
    ∃ message ∈ execution.network.inputs,
      message.sender = owner ∧ message.payload.attempt = coordinate.1.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.1.event ∧
      message ∈ execution.network.pending ∧ execution.network.lookup identifier = some message ∧
      execution.application.current.native.WithinDeadline runtime coordinate.1.event := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have recalled := (PhaseCount.countRecall_history runtime leaks raw).1
  have word := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
    scheduler remaining execution trace
  obtain ⟨emission, member, idEq, timely⟩ := reply_inclusion_witness runtime leaks decideLocal
    timed coordinate seed (queryAt runtime leaks execution coordinate owner) identifier included
  obtain ⟨packet, packetMember, operationalEq⟩ := List.mem_map.mp member
  obtain ⟨authentic, sender, attempt, addressed⟩ := PhaseSeedScheduler.localInput_emission_authentic
    runtime leaks execution coordinate.1 owner word recalled packet.1 packet.2 packetMember
  have identifierEq : packet.2.id = identifier :=
    (congrArg PhaseSeedEmission.identifier operationalEq).trans idEq
  obtain ⟨input, invariant, _, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((invariant.active.activated_iff coordinate.1.event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  have deadline :
      execution.application.current.native.WithinDeadline runtime coordinate.1.event := by
    change execution.application.current.native.clock -
      (execution.application.current.native.activatedAt coordinate.1.event).getD
        execution.application.current.native.clock < runtime.deadline coordinate.1.event at timely
    have stamp : execution.application.current.native.activatedAt coordinate.1.event =
        some entered := activated
    rw [stamp, Option.getD_some] at timely
    simpa only [State.WithinDeadline, stamp] using timely
  have packetRequest : execution.application.SeedRequest packet.2.sender
      ⟨packet.2.payload.attempt, coordinate.1.event⟩ := by
    simpa only [sender, attempt] using request
  have pending := PhaseCount.survivor_pending runtime leaks bounds plan ordered maximal inputs
    horizon scheduler _ trace packet.2 authentic coordinate.1.event addressed packetRequest deadline
  have unique := (app).uniqueIds_history scheduler initial horizon _ raw
  have hasLookup : (execution.network.lookup identifier).isSome = true :=
    List.find?_isSome.mpr ⟨packet.2, pending, by simp only [identifierEq, decide_true]⟩
  obtain ⟨selected, found⟩ := Option.isSome_iff_exists.mp hasLookup
  have selectedTest := List.find?_some found
  have selectedId : selected.id = identifier := of_decide_eq_true selectedTest
  have same : selected = packet.2 := (unique.inputs packet.2 authentic).pending selected
    (List.mem_of_find?_eq_some found) (selectedId.trans identifierEq.symm)
  rw [same] at found
  exact ⟨packet.2, authentic, sender, attempt, addressed, pending, found, deadline⟩

/-- A counted local include physically resolves its original event: an
immediate retry can retire the namespace instead of retaining the completed cell. -/
theorem inclusion_resolves_of_trace
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
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
    (seed : LocalSeed) (identifier : MessageId Player)
    (included : reply runtime leaks decideLocal coordinate seed
      (queryAt runtime leaks execution coordinate owner) = .include identifier)
    (reached : next ∈ (execution.environmentStep app (.include identifier)).support) :
    coordinate.1.attempt ≠ next.application.attempt ∨
      coordinate.1.event ∈ next.application.current.native.config.cut.completed := by
  obtain ⟨message, authentic, sender, attempt, addressed, _, found, timely⟩ :=
    reply_inclusion_packet_of_trace runtime leaks decideLocal timed bounds plan ordered maximal
      inputs
      horizon scheduler remaining execution trace coordinate owner request seed identifier included
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, coordinate.1.event⟩ := by
    simpa only [sender, attempt] using request
  have handled := PhaseCount.counted_call_resolves_of_history runtime leaks bounds plan inputs
    horizon scheduler trace message authentic coordinate.1.event addressed packetRequest timely
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


end Vegas.EventGraphRuntime.PhaseServiceScheduler
