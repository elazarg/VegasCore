/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountedSurvivor
import Vegas.Pending.PhaseSeedHistoryInput
import Vegas.Pending.PhaseSeedQueryMarks

/-! # A selected inclusion names an authentic pending packet of its own event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

namespace PhaseSeedScheduler

omit [Fintype Player] in
/-- Every item in the complete local word is an authentic own envelope for the
same physical attempt and event, recovered from genuine retained player recall. -/
theorem localInput_emission_authentic (execution : (app).Execution)
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (valid : WordRecall runtime leaks execution) (recalled : execution.InputRecall app)
    (tick : Nat) (message : Message Player (CommitAttemptPacket graph))
    (member : (tick, message) ∈ (localInput runtime leaks coordinate owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions) :
    message ∈ execution.network.inputs ∧ message.sender = owner ∧
      message.payload.attempt = coordinate.attempt ∧
        message.payload.packet.call.event? graph = some coordinate.event := by
  rw [localInput_word, valid owner coordinate] at member
  obtain ⟨record, recordMember, packetMember⟩ := List.mem_flatMap.mp member
  obtain ⟨packet, packetMember, pairEq⟩ := List.mem_map.mp packetMember
  have samePacket : packet = message := congrArg Prod.snd pairEq
  subst packet
  obtain ⟨entry, entryMember, recordEq⟩ := List.mem_map.mp recordMember
  rw [← recordEq] at packetMember
  obtain ⟨inOutput, selected⟩ := List.mem_filter.mp packetMember
  have own : message.sender = owner ∧ message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event := of_decide_eq_true selected
  have emitted : entry.emitted = some message := Option.mem_toList.mp inOutput
  have output : message ∈ (app).outputs (execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, (List.mem_filter.mp entryMember).1, emitted⟩
  rw [← recalled owner] at output
  exact ⟨(List.mem_filter.mp output).1, own⟩

end PhaseSeedScheduler

namespace PhaseSeedCalendar

omit [DecidableEq Player] in
/-- The actual inclusion index comes from the authorized finite emission word
and is selected strictly before this event's original deadline. -/
theorem decision_inclusion_witness (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph) (index : Nat)
    (chosen : decision runtime delay bound coordinate seed input = .inclusion index) :
    ∃ emission, input.emissions[index]? = some emission ∧ emission.authorized = true ∧
      input.elapsed < runtime.deadline coordinate.1.event := by
  by_cases due : runtime.deadline coordinate.1.event ≤ input.elapsed
  · simp only [decision, ite_eq_left due, reduceCtorEq] at chosen
  · by_cases activate : seed.1.val ≤ input.elapsed ∧ input.elapsed ∉ input.activationClocks
    · simp only [decision, ite_eq_right due, ite_eq_left activate, reduceCtorEq] at chosen
    · simp only [decision, ite_eq_right due, ite_eq_right activate] at chosen
      cases found : input.emissions.zipIdx.find? (fun entry => entry.1.authorized &&
          (entry.1.clock + bound coordinate.1.event < runtime.deadline coordinate.1.event ||
            seed.2 (Fin.ofNat (clockLimit runtime delay + 1) input.elapsed))) with
      | none => simp only [found, reduceCtorEq] at chosen
      | some entry =>
          have same : entry.2 = index := PhaseSeedDecision.inclusion.inj (by
            simpa only [found] using chosen)
          have indexed := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
          have test := List.find?_some found
          have authorized := (Bool.and_eq_true_iff.mp test).1
          rw [same] at indexed
          exact ⟨entry.1, indexed, authorized, Nat.lt_of_not_ge due⟩

/-- A concrete include reply names an authorized member of the erased word. -/
theorem reply_inclusion_witness (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph) (identifier : MessageId Player)
    (included : reply runtime leaks delay bound coordinate seed input = .include identifier) :
    ∃ emission ∈ input.emissions, emission.identifier = identifier ∧
      emission.authorized = true ∧ input.elapsed < runtime.deadline coordinate.1.event := by
  unfold reply at included
  cases decided : decision runtime delay bound coordinate seed input with
  | activation =>
      cases actor : graph.actor? coordinate.1.event <;> simp [decided, actor] at included
  | inclusion index =>
      obtain ⟨emission, indexed, authorized, timely⟩ :=
        decision_inclusion_witness runtime delay bound coordinate seed input index decided
      have identifierEq : emission.identifier = identifier := by
        simpa only [decided, indexed, Option.map_some, Option.getD_some,
          ReactiveApplication.Command.include.injEq] using included
      exact ⟨emission, List.mem_of_getElem? indexed, identifierEq, authorized, timely⟩
  | expiry => simp only [decided, reduceCtorEq] at included
  | wait => simp only [decided, reduceCtorEq] at included

/-- At a genuine clean idle history, the selected erased identifier is the
actual pending own packet, even with arbitrary prior retries and handle choices. -/
theorem reply_inclusion_packet_of_trace (delay bound : graph.EventId → Nat)
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
    (seed : Seed runtime delay) (identifier : MessageId Player)
    (included : reply runtime leaks delay bound coordinate seed
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
  obtain ⟨emission, member, idEq, _, timely⟩ := reply_inclusion_witness runtime leaks delay bound
    coordinate seed (queryAt runtime leaks execution coordinate owner) identifier included
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

end PhaseSeedCalendar
end Vegas.EventGraphRuntime
