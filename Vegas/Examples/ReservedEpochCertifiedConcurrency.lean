/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ReservedEpochBudgetConcurrency
import Vegas.Examples.ReservedEpochBoundedGaps
import Vegas.Pending.ReservedEpochService

/-! # Usable concurrent packets in a budgeted asynchronous service -/

noncomputable section

namespace Vegas.Examples.ReservedEpochCertifiedConcurrency

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open CommitTimingInformation

abbrev Player := CommitTimingInformation.Player
abbrev graph := CommitTimingInformation.graph
abbrev runtime := CommitTimingInformation.runtime
abbrev leaks := CommitTimingInformation.leaks
abbrev app := CommitTimingInformation.app
abbrev plan := CommitTimingInformation.plan

def bounds : MessageBounds graph :=
  { CommitTimingInformation.bounds with candidateCount := ReservedEpoch.executionHorizon runtime }

theorem prefix_within_horizon :
    ReservedEpoch.packetCapacity runtime + 2 ≤ ReservedEpoch.executionHorizon runtime := by
  have positive := ReservedEpoch.completionCycles_pos runtime
  have width : ReservedEpoch.packetCapacity runtime + 2 ≤
      ReservedEpoch.cycleWidth (graph := graph) (ReservedEpoch.packetCapacity runtime) := by
    unfold ReservedEpoch.cycleWidth
    omega
  have multiple := Nat.mul_le_mul_right
    (ReservedEpoch.cycleWidth (graph := graph) (ReservedEpoch.packetCapacity runtime)) positive
  exact width.trans (by
    simpa only [ReservedEpoch.executionHorizon, ReservedEpoch.horizon,
      ReservedEpoch.packetCapacity, Nat.one_mul] using multiple)

theorem service_contract (inputs : PMF graph.Inputs) :
    PhaseService.AsyncContract runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpochBudgetConcurrency.selectedScheduler (ReservedEpoch.packetCapacity runtime))
      (fun _ => 2) (fun _ => 3) := by
  exact ReservedEpoch.implementation_asyncContract runtime leaks ReservedEpochConcurrency.prior
    1 2 (fun tape supported =>
      ReservedEpochConcurrency.supported_tape_boundedGaps tape supported _)
    plan ((toEventGraph CommitTimingInformation.program).withMode_revealRelaxedOrdered
      (toEventGraph_barrierOrdered CommitTimingInformation.program) .concurrentReveals)
    (compiledRuntimePhasePlan_maximal CommitTimingInformation.program .concurrentReveals) inputs

theorem timely_service : runtime.AsyncTimely (fun _ => 2) (fun _ => 3) :=
  ReservedEpoch.asyncTimely runtime 1 2 (fun _ _ => by change 5 < 7; decide)

theorem candidate_reserve : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount :=
  le_rfl

theorem supported_concurrent_trace (reverse bit : Bool) :
    Nonempty ((app.protocol (PMF.pure (initialState bit))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpochBudgetConcurrency.selectedScheduler
        (ReservedEpoch.packetCapacity runtime))).Trace
        (some ⟨ReservedEpoch.executionHorizon runtime - (ReservedEpoch.packetCapacity runtime + 2),
          none, ReservedEpochBudgetConcurrency.afterBoth
            (ReservedEpoch.packetCapacity runtime) reverse bit⟩)) := by
  apply app.raw_trace_roundsFrom (PMF.pure (initialState bit))
    (ReservedEpoch.executionHorizon runtime) _ ReservedEpochConcurrency.players
    (ReservedEpoch.packetCapacity runtime + 2) prefix_within_horizon
  simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind,
    CommitTimingInformation.initialExecution] using
    ReservedEpochBudgetConcurrency.concurrent_prefix_supported
      (ReservedEpoch.packetCapacity runtime) reverse bit

theorem valid_concurrent_service (reverse bit : Bool) :
    PhaseService.AsyncContract runtime leaks
      ((PMF.pure (encodeInputs (sourceInitial bit))).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpochBudgetConcurrency.selectedScheduler (ReservedEpoch.packetCapacity runtime))
      (fun _ => 2) (fun _ => 3) ∧
    runtime.AsyncTimely (fun _ => 2) (fun _ => 3) ∧
    ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount ∧
    Nonempty ((app.protocol (PMF.pure (initialState bit))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpochBudgetConcurrency.selectedScheduler
        (ReservedEpoch.packetCapacity runtime))).Trace
        (some ⟨ReservedEpoch.executionHorizon runtime - (ReservedEpoch.packetCapacity runtime + 2),
          none, ReservedEpochBudgetConcurrency.afterBoth
            (ReservedEpoch.packetCapacity runtime) reverse bit⟩)) ∧
    ∀ owner : Player,
      ReservedEpochConcurrency.commitmentMessage owner ∈
        (ReservedEpochBudgetConcurrency.afterBoth
          (ReservedEpoch.packetCapacity runtime) reverse bit).network.pending ∧
      (∃ next, app.handle (ReservedEpochBudgetConcurrency.afterBoth
        (ReservedEpoch.packetCapacity runtime) reverse bit).application
          (ReservedEpochConcurrency.commitmentMessage owner) = some next) ∧
      (ReservedEpochBudgetConcurrency.afterBoth
        (ReservedEpoch.packetCapacity runtime) reverse bit).application.current.native.bindingResult
          (owner, .prepared 0) .bool = .success true := by
  refine ⟨service_contract _, timely_service, candidate_reserve,
    supported_concurrent_trace reverse bit, ?_⟩
  intro owner
  have packet := (ReservedEpochBudgetConcurrency.two_valid_packets_pending
    (ReservedEpoch.packetCapacity runtime) reverse bit).2.2 owner
  exact ⟨packet.1, packet.2.2.2.1, packet.2.2.2.2⟩

end Vegas.Examples.ReservedEpochCertifiedConcurrency
