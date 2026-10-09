/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionReliability
import Vegas.Pending.ReactiveLatestErasure

/-! # Certain late inclusion with the actual service and erasure contracts

The deterministic endpoint of the native committed-resolution scheduler
satisfies both the all-history asynchronous service contract and the
all-input late-packet erasure condition. Its genuine initialized late opening
is accepted with certainty. Consequently those two conditions jointly do
not impose a positive failure floor on late openings. No equilibrium
preservation or nondegenerate stochastic scheduler is asserted here.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionErasure

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open CommittedResolutionService

private theorem fixed_command_erasure
    (command : app.Command) (removed : MessageId Player)
    (restored : ReactiveApplication.Command.restore app removed command = command) :
    ∃ (probability : ℝ) (nonnegative : 0 ≤ probability) (atMost : probability ≤ 1),
      PMF.pure command = mix probability nonnegative atMost (PMF.pure (.include removed))
        ((PMF.pure command).map (ReactiveApplication.Command.restore app removed)) := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rw [mix_zero, PMF.pure_map, restored]

/-- The deterministic endpoint is erasure-independent at every input,
including inputs with multiple pending eligible envelopes. -/
theorem certain_scheduler_blind :
    (runtime setup).BlindToLatePackets leaks bound
      (CommittedResolutionReliability.scheduler 1 zero_le_one le_rfl) := by
  intro past view message _pending _late
  have lengthErase : (app.eraseEnvironmentRecall message.id past).length = past.length := by
    exact List.length_map ..
  by_cases lateCursor : past.length = 5
  · simpa only [CommittedResolutionReliability.scheduler, lateCursor, lengthErase, ↓reduceIte,
      mix_one] using (runtime setup).reactiveLatest_include_or_erased leaks aliceEvent alice
        view message.id
  · simp only [CommittedResolutionReliability.scheduler, lateCursor, lengthErase, ↓reduceIte,
      CommittedResolutionService.scheduler]
    generalize located : past.length = position
    have notFive : position ≠ 5 := by simpa only [located] using lateCursor
    by_cases inside : position < 16
    · interval_cases position
      all_goals first
      | exact False.elim (notFive rfl)
      | simpa only [stageChoice] using
          (runtime setup).reactiveLatest_include_or_erased leaks aliceEvent alice view message.id
      | simpa only [stageChoice] using
          (runtime setup).reactiveLatest_include_or_erased leaks bobEvent bob view message.id
      | simpa only [stageChoice] using fixed_command_erasure _ message.id rfl
    · have idle : stageChoice position view = PMF.pure .wait := by
        unfold stageChoice
        split <;> first | omega | rfl
      have erasedIdle : stageChoice position (view.erase app message.id) = PMF.pure .wait := by
        unfold stageChoice
        split <;> first | omega | rfl
      rw [idle, erasedIdle]
      exact fixed_command_erasure .wait message.id rfl

/-- A concrete native scheduler jointly satisfies the service and erasure
contracts while a supported initialized late opening has zero failure. -/
theorem certain_late_inclusion_with_joint_contract :
    AsyncContract (runtime setup) leaks (initialLaw setup) CommittedResolutionService.horizon
      (CommittedResolutionReliability.scheduler 1 zero_le_one le_rfl) delay bound ∧
    (runtime setup).BlindToLatePackets leaks bound
      (CommittedResolutionReliability.scheduler 1 zero_le_one le_rfl) ∧
    CommittedResolutionReliability.initializedExecution.application ∈ (initialLaw setup).support ∧
    ¬ CommittedResolutionRecovery.lateExecution.application.publicView.InclusionFitsDeadline
      (runtime setup) bound aliceEvent ∧
    (runtime setup).canonicalServiceDecision leaks alice
      (CommittedResolutionRecovery.lateExecution.recall alice)
      (CommittedResolutionRecovery.lateExecution.observe app alice) aliceEvent true =
        ⟨some CommittedResolutionRecovery.opening⟩ ∧
    app.runRounds (CommittedResolutionReliability.scheduler 1 zero_le_one le_rfl)
      CommittedResolutionRecovery.latePlayers 5
        CommittedResolutionReliability.initializedExecution =
      PMF.pure (CommittedResolutionRecovery.lateExecution.respond app alice
        ⟨some CommittedResolutionRecovery.opening⟩) ∧
    (((app.runRounds (CommittedResolutionReliability.scheduler 1 zero_le_one le_rfl)
      CommittedResolutionRecovery.latePlayers 6
        CommittedResolutionReliability.initializedExecution).map
          CommittedResolutionReliability.accepted) true).toReal = 1 ∧
    (((app.runRounds (CommittedResolutionReliability.scheduler 1 zero_le_one le_rfl)
      CommittedResolutionRecovery.latePlayers CommittedResolutionService.horizon
        CommittedResolutionReliability.initializedExecution).map
          CommittedResolutionReliability.accepted) true).toReal = 1 := by
  exact ⟨CommittedResolutionReliability.contract 1 zero_le_one le_rfl,
    certain_scheduler_blind, CommittedResolutionReliability.initialized_supported,
    CommittedResolutionRecovery.late_window.2, CommittedResolutionRecovery.canonical_late_response,
    CommittedResolutionReliability.late_response_reached 1 zero_le_one le_rfl,
    CommittedResolutionReliability.initialized_receipt_probability 1 zero_le_one le_rfl,
    le_antisymm (pmf_toReal_apply_le_one _ _)
      (CommittedResolutionReliability.terminal_receipt_probability 1 zero_le_one le_rfl)⟩

end Vegas.Examples.CommittedResolutionErasure
