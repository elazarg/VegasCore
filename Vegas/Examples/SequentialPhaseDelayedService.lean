/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseServiceSetup
import Vegas.Pending.ReservedEpochService
import Vegas.Pending.ReservedEpochFinite
import Vegas.Pending.ReservedEpochClockAccounting
import Vegas.Pending.ReservedEpochWaitingPackets
import Vegas.Pending.ReservedEpochDelivery
import Vegas.Pending.PhaseOpeningResponse
import Interaction.ReactiveRawRoundTrace

/-! # Positive clock latency before a first strategic publication

The first event is owned and has rank zero. Its configured deadline is six
ticks. A periodic reserved service skips activation in the first cycle and
processes packets before each cycle's activations. Its physical service
contract holds on every raw history, including terminal histories.
-/

noncomputable section

namespace Vegas.Examples.SequentialPhaseDelayedService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

abbrev fixture := SequentialPhaseService.setup
abbrev compiled := SequentialPhaseService.compiled
abbrev owner := SequentialPhaseService.owner
abbrev event := SequentialPhaseService.event
abbrev plan := SequentialPhaseService.plan
abbrev leaks := SequentialPhaseService.leaks

def runtime : EventGraphRuntime compiled := serviceRuntime fixture .sequential (fun _ => 6)

abbrev app := phaseApplication runtime leaks
abbrev initial : PMF app.State := SequentialPhaseService.initial

def tape : ReservedEpoch.Tape SequentialPhaseService.Player 1 where
  order := fun _ => Equiv.refl _
  activation := fun cycle _ => cycle.val = 1
  processing := fun _ => true

abbrev packetBudget := ReservedEpoch.packetCapacity runtime
abbrev horizon := ReservedEpoch.executionHorizon runtime
abbrev scheduler : app.Scheduler := ReservedEpoch.family runtime leaks packetBudget tape

theorem tape_boundedGaps (cycles : Nat) : tape.BoundedGaps cycles 2 1 where
  activation cycle _ who := by
    by_cases odd : cycle % 2 = 1
    · refine ⟨cycle, le_rfl, by omega, ?_⟩
      simpa [ReservedEpoch.Tape.activates, ReservedEpoch.Tape.index, tape, Fin.val_ofNat]
        using odd
    · refine ⟨cycle + 1, by omega, by omega, ?_⟩
      have next : (cycle + 1) % 2 = 1 := by omega
      simpa [ReservedEpoch.Tape.activates, ReservedEpoch.Tape.index, tape, Fin.val_ofNat]
        using next
  processing cycle _ := ⟨cycle, le_rfl, by omega, rfl⟩

private theorem maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample := by
  have sole : plan.phases = [sequentialRuntimePhaseAt SequentialPhaseService.program event] := by
    simp only [plan, SequentialPhaseService.plan, sequentialRuntimePhasePlan]
    rw [List.ofFn_succ]
    rfl
  rw [sole]
  exact List.isChain_singleton _

theorem opportunity : PhaseService.Opportunity runtime leaks initial horizon scheduler
    (fun _ => 3) := by
  exact ReservedEpoch.family_opportunity runtime leaks packetBudget
    (ReservedEpoch.completionCycles runtime) tape 2 1 (tape_boundedGaps _) plan
    (serviceGraph_revealRelaxedOrdered fixture .sequential) maximal
    (fixture.initialLaw.map fixture.eventInputs)

theorem protectedInclusion : PhaseService.ProtectedInclusion runtime leaks initial horizon scheduler
    (fun _ => 2) :=
  ReservedEpoch.family_protectedInclusion runtime leaks (ReservedEpoch.completionCycles runtime)
    tape 2 1 (tape_boundedGaps _) plan (fixture.initialLaw.map fixture.eventInputs)

theorem completesPlay : PhaseService.CompletesPlay runtime leaks initial horizon scheduler :=
  ReservedEpoch.family_completesPlay runtime leaks tape plan
    (serviceGraph_revealRelaxedOrdered fixture .sequential) maximal
    (fixture.initialLaw.map fixture.eventInputs)

theorem timely : runtime.AsyncTimely (fun _ => 3) (fun _ => 2) := by
  intro requested _
  change 3 + 2 < 6
  decide

theorem physical_contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler
    (fun _ => 3) (fun _ => 2) := ⟨opportunity, protectedInclusion, completesPlay⟩

instance : app.FiniteNature initial scheduler :=
  phaseApplication_finiteNature runtime leaks initial scheduler
    (by
      change SequentialPhaseService.initial.support.Finite
      exact ReactiveApplication.FiniteNature.initial_finite (scheduler :=
        SequentialPhaseService.scheduler))
    (fun _ _ => by
      change (PMF.pure _).support.Finite
      rw [PMF.support_pure]
      exact Set.finite_singleton _)

theorem owned_first_event : compiled.actor? event = some owner ∧ event.val = 0 := by
  exact ⟨rfl, rfl⟩

abbrev width := ReservedEpoch.cycleWidth (graph := compiled) packetBudget

private theorem reached_idle (count : Nat) (bounded : count ≤ horizon) :
    ∃ execution : app.Execution,
      Nonempty ((app.protocol initial horizon scheduler).Trace
        (some ⟨horizon - count, none, execution⟩)) ∧
      execution.environmentRecall.length = count := by
  obtain ⟨execution, reached⟩ :=
    (app.roundsFrom initial scheduler (fun _ => app.silentPolicy) count).support_nonempty
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial horizon scheduler
    (fun _ => app.silentPolicy) count bounded execution reached
  refine ⟨execution, ⟨trace⟩, ?_⟩
  have accounted := app.raw_trace_horizon initial horizon scheduler trace
  simp only at accounted
  omega

/-- A genuine legal raw callback occurs after the first physical clock tick.
The activation command itself consumes no additional tick. -/
theorem positive_latency_activation : ∃ before after : app.Execution,
    Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨horizon - (width + packetBudget), none, before⟩)) ∧
    Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨horizon - (width + packetBudget) - 1, some owner, after⟩)) ∧
    before.application.current.native.clock = 1 ∧
    after.application.current.native.clock = 1 ∧
    before.environmentRecall.length = width + packetBudget := by
  have room : width + packetBudget < horizon := by decide
  obtain ⟨before, ⟨trace⟩, cursor⟩ := reached_idle (width + packetBudget) (by omega)
  have selected : ReservedEpoch.command runtime leaks packetBudget tape
      before.environmentRecall.length (before.observeEnvironment app) = .activate owner := by
    rw [cursor]
    have act := ReservedEpoch.activation_at runtime leaks packetBudget tape 1 0
      (before.observeEnvironment app) (by decide)
    simpa only [Nat.one_mul, Fin.val_zero, Nat.add_zero] using act
  have clock : before.application.current.native.clock = 1 := by
    rw [ReservedEpoch.clock_history runtime leaks packetBudget tape plan
      (fixture.initialLaw.map fixture.eventInputs) horizon _ trace, cursor]
    exact ReservedEpoch.cursor_div (graph := compiled) packetBudget 1 packetBudget (by
      unfold ReservedEpoch.cycleWidth
      omega)
  obtain ⟨after, moved⟩ := (before.environmentStep app (.activate owner)).support_nonempty
  have selectedSupport : (.activate owner : app.Command) ∈
      (scheduler before.environmentRecall (before.observeEnvironment app)).support := by
    change _ ∈ (PMF.pure _).support
    exact (PMF.mem_support_pure_iff _ _).mpr selected.symm
  obtain ⟨nextTrace⟩ := app.raw_trace_environment initial horizon scheduler
    (horizon - (width + packetBudget) - 1) before after (.activate owner)
      (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ horizon -
        (width + packetBudget))] using trace) selectedSupport moved
  refine ⟨before, after, ⟨trace⟩, ⟨nextTrace⟩, clock, ?_, cursor⟩
  unfold ReactiveApplication.Execution.environmentStep at moved
  obtain ⟨changed, observed, rfl⟩ := PMF.support_map .. ▸ moved
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ observed
  exact clock

/-- A raw opening submitted at the delayed callback is physically receipted
in the next cycle. There is a real clock tick between emission and receipt;
the receipt may reject a value inconsistent with the private initial binding. -/
theorem positive_latency_receipt : ∃ sent delivered : app.Execution,
    ∃ message : Message SequentialPhaseService.Player (CommitAttemptPacket compiled),
    Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨horizon - sent.environmentRecall.length, none, sent⟩)) ∧
    Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨horizon - delivered.environmentRecall.length, none, delivered⟩)) ∧
    sent.application.current.native.clock = 1 ∧
    delivered.application.current.native.clock = 2 ∧
    message ∈ sent.network.pending ∧
    message.payload.packet.call.event? compiled = some event ∧
    ∃ accepted, (message.id, accepted) ∈ delivered.receipts := by
  obtain ⟨before, active, _, ⟨activeTrace⟩, _, activeClock, _⟩ := positive_latency_activation
  have activeCursor : active.environmentRecall.length = width + packetBudget + 1 := by
    have accounted := app.raw_trace_horizon initial horizon scheduler activeTrace
    change active.environmentRecall.length + (horizon - (width + packetBudget) - 1) =
      horizon at accounted
    have room : width + packetBudget < horizon := by decide
    omega
  let response := PhaseCount.phaseOpeningResponse runtime leaks event
    (owner, .initial ⟨0, by decide⟩) ⟨.bool, true⟩
  let sent := active.respond app owner response
  let message : Message SequentialPhaseService.Player (CommitAttemptPacket compiled) :=
    ⟨(owner, active.network.nextSerial owner),
      app.packet (app.submit active.application owner
        (disclosureSubmission (.opening event (owner, .initial ⟨0, by decide⟩)
          ⟨.bool, true⟩))) owner (active.network.known owner)
        (disclosureSubmission (.opening event (owner, .initial ⟨0, by decide⟩)
          ⟨.bool, true⟩))⟩
  have pending : message ∈ sent.network.pending := by
    change message ∈ List.append active.network.pending [message]
    exact List.mem_append.mpr (Or.inr (List.Mem.head []))
  have sentCursor : sent.environmentRecall.length = width + packetBudget + 1 := activeCursor
  have sentClock : sent.application.current.native.clock = 1 := activeClock
  obtain ⟨sentTrace⟩ := app.raw_trace_respond initial horizon scheduler
    (horizon - (width + packetBudget) - 1) active owner response activeTrace
  let count := width - packetBudget - 1
  obtain ⟨boundary, reached⟩ :=
    (app.runRounds scheduler (fun _ => app.silentPolicy) count sent).support_nonempty
  have boundaryCursor : boundary.environmentRecall.length = 2 * width := by
    rw [app.runRounds_environmentRecall_length scheduler (fun _ => app.silentPolicy)
      count sent boundary reached, sentCursor]
    dsimp [count, width, ReservedEpoch.cycleWidth]
    omega
  obtain ⟨boundaryTrace⟩ := app.raw_trace_runRounds initial horizon scheduler
    (fun _ => app.silentPolicy) (horizon - 2 * width) count sent boundary
      (by
        have remaining : horizon - 2 * width + count =
            horizon - (width + packetBudget) - 1 := by decide
        simpa only [remaining] using sentTrace) reached
  have retained := ReservedEpoch.pending_until_processing_boundary runtime leaks packetBudget
    tape (fun _ => app.silentPolicy) 1 (packetBudget + 1) 2 count sent boundary
      (by change sent.environmentRecall.length = width + (packetBudget + 1); omega) (by omega)
      (by intro later lower upper; omega)
      (by dsimp [count, width, ReservedEpoch.cycleWidth] at *; omega)
      message pending reached
  have capacity := ReservedEpoch.pending_le_cycles runtime leaks packetBudget tape initial
    (ReservedEpoch.completionCycles runtime) _ boundaryTrace
  change boundary.network.pending.length ≤ packetBudget at capacity
  obtain ⟨delivered, processed⟩ := (app.runRounds scheduler (fun _ => app.silentPolicy)
    boundary.network.pending.length boundary).support_nonempty
  have receipt := ReservedEpoch.processing_segment runtime leaks packetBudget tape
    (fun _ => app.silentPolicy) 2 0 boundary.network.pending boundary delivered
      (by simpa only [Nat.add_zero] using boundaryCursor) (by omega) rfl rfl processed
  have deliveredCursor : delivered.environmentRecall.length =
      2 * width + boundary.network.pending.length := by
    rw [receipt.2.2.2.2.2, boundaryCursor]
  obtain ⟨deliveredTrace⟩ := app.raw_trace_runRounds initial horizon scheduler
    (fun _ => app.silentPolicy) (horizon - (2 * width + boundary.network.pending.length))
      boundary.network.pending.length boundary delivered
      (by
        have room : 2 * width + packetBudget ≤ horizon := by decide
        have remaining : horizon - (2 * width + boundary.network.pending.length) +
            boundary.network.pending.length = horizon - 2 * width := by omega
        simpa only [remaining] using boundaryTrace) processed
  refine ⟨sent, delivered, message, ?_, ?_, sentClock, ?_, pending, ?_, receipt.2.2.2.1 _ retained⟩
  · have remaining : horizon - (width + packetBudget + 1) =
        horizon - (width + packetBudget) - 1 := by omega
    simpa only [sentCursor, remaining] using Nonempty.intro sentTrace
  · simpa only [deliveredCursor] using Nonempty.intro deliveredTrace
  · rw [ReservedEpoch.clock_history runtime leaks packetBudget tape plan
      (fixture.initialLaw.map fixture.eventInputs) horizon _ deliveredTrace, deliveredCursor]
    exact ReservedEpoch.cursor_div (graph := compiled) packetBudget 2
      boundary.network.pending.length (lt_of_le_of_lt capacity (by
        unfold ReservedEpoch.cycleWidth
        omega))
  · change Payload.event? compiled
      ((active.application.submit owner _).emit owner
        (active.network.known owner) _).packet.call = _
    rw [phase_emit_call]
    rfl

end Vegas.Examples.SequentialPhaseDelayedService
