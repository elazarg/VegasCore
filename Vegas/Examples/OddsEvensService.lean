/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensSetup
import Vegas.Pending.ReservedEpochService
import Vegas.Pending.ReservedEpochFinite
import Vegas.Pending.ReservedEpochClockAccounting
import Interaction.ReactiveRawRoundTrace

/-! # A positive-latency physical service for two-player Odds–Evens -/

noncomputable section

namespace Vegas.Examples.OddsEvensService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

abbrev fixture := OddsEvens.setup
abbrev compiled := OddsEvens.compiled
abbrev plan := OddsEvens.plan

def leaks : MessageNetwork.ObservationRule OddsEvens.Player (CommitAttemptPacket compiled) :=
  fun _ _ => PMF.pure ∅

instance : leaks.FiniteSupport where
  support_finite _ _ := by
    simp only [leaks, PMF.support_pure]
    exact Set.finite_singleton _

def runtime : EventGraphRuntime compiled := serviceRuntime fixture .sequential (fun _ => 6)

abbrev app := phaseApplication runtime leaks

def initial : PMF app.State :=
  (fixture.initialLaw.map fixture.eventInputs).map (PhaseRuntimeState.initial plan)

def tape : ReservedEpoch.Tape OddsEvens.Player 1 where
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

theorem partitionRegular : RuntimePhase.PartitionRegular plan.phases := by
  right
  intro before after earlier
  exact (EventOrder.sequential.mem_predecessors before after).mpr earlier

theorem opportunity : PhaseService.Opportunity runtime leaks initial horizon scheduler
    (fun _ => 3) :=
  ReservedEpoch.family_opportunity runtime leaks packetBudget
    (ReservedEpoch.completionCycles runtime) tape 2 1 (tape_boundedGaps _) plan
    (serviceGraph_revealRelaxedOrdered fixture .sequential) partitionRegular
    (fixture.initialLaw.map fixture.eventInputs)

theorem protectedInclusion : PhaseService.ProtectedInclusion runtime leaks initial horizon scheduler
    (fun _ => 2) :=
  ReservedEpoch.family_protectedInclusion runtime leaks (ReservedEpoch.completionCycles runtime)
    tape 2 1 (tape_boundedGaps _) plan (fixture.initialLaw.map fixture.eventInputs)

theorem completesPlay : PhaseService.CompletesPlay runtime leaks initial horizon scheduler :=
  ReservedEpoch.family_completesPlay runtime leaks tape plan
    (serviceGraph_revealRelaxedOrdered fixture .sequential) partitionRegular
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
      rw [initial, PMF.support_map, PMF.support_map]
      exact ((Setup.FiniteInitialLaw.support_finite (setup := fixture)).image _).image _)
    (fun _ _ => by
      change (PMF.pure _).support.Finite
      rw [PMF.support_pure]
      exact Set.finite_singleton _)

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
      (some ⟨horizon - (width + packetBudget) - 1, some (tape.owner 1 0), after⟩)) ∧
    before.application.current.native.clock = 1 ∧
    after.application.current.native.clock = 1 ∧
    before.environmentRecall.length = width + packetBudget := by
  have room : width + packetBudget < horizon := by decide
  obtain ⟨before, ⟨trace⟩, cursor⟩ := reached_idle (width + packetBudget) (by omega)
  have selected : ReservedEpoch.command runtime leaks packetBudget tape
      before.environmentRecall.length (before.observeEnvironment app) =
        .activate (tape.owner 1 0) := by
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
  obtain ⟨after, moved⟩ :=
    (before.environmentStep app (.activate (tape.owner 1 0))).support_nonempty
  have selectedSupport : (.activate (tape.owner 1 0) : app.Command) ∈
      (scheduler before.environmentRecall (before.observeEnvironment app)).support := by
    change _ ∈ (PMF.pure _).support
    exact (PMF.mem_support_pure_iff _ _).mpr selected.symm
  obtain ⟨nextTrace⟩ := app.raw_trace_environment initial horizon scheduler
    (horizon - (width + packetBudget) - 1) before after (.activate (tape.owner 1 0))
      (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ horizon -
        (width + packetBudget))] using trace) selectedSupport moved
  refine ⟨before, after, ⟨trace⟩, ⟨nextTrace⟩, clock, ?_, cursor⟩
  unfold ReactiveApplication.Execution.environmentStep at moved
  obtain ⟨changed, observed, rfl⟩ := PMF.support_map .. ▸ moved
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ observed
  exact clock

end Vegas.Examples.OddsEvensService
