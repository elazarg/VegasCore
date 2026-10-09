/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLateAcceptance
import Interaction.ReactiveMonitoring

/-! # Arbitrarily reliable late inclusion in the actual partially public service

Both canonical late timing policies are legal initialized executions. Their
accepting-receipt law has probability `weight / (1 + weight)` after nine public
commands, and acceptance persists under every later raw policy. The same
finite-weight family satisfies the complete asynchronous service contract and
all-view erasure independence. This is an operational boundary, not an SE
counterexample.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeReliability

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance

def accepted (execution : app.Execution) : Bool :=
  decide (((alice, 0), true) ∈ execution.receipts)

theorem first_late_window_closed (bit : Bool) (label : Fin 3) :
    ¬ (firstLateDecision bit label).application.publicView.InclusionFitsDeadline
      LateOpeningRuntimeService.runtime bound aliceEvent := by
  change ¬ (1 - 0 + 2 < 3)
  decide

theorem second_late_window_closed (bit : Bool) (label : Fin 3) (seen : Bool) :
    ¬ (secondLateDecision bit label 1 seen).application.publicView.InclusionFitsDeadline
      LateOpeningRuntimeService.runtime bound aliceEvent := by
  change ¬ (2 - 0 + 2 < 3)
  decide

theorem acceptedLottery_accepted (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    accepted (acceptedLottery bit label slot seen) = true :=
  decide_eq_true (acceptedLottery_receipt bit label slot seen)

theorem omittedLottery_not_accepted (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    accepted (omittedLottery bit label slot seen) = false := by
  fin_cases slot <;> cases seen <;> rfl

theorem after_observation_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      4 (bobObserved bit label slot seen)).map accepted =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure true) (PMF.pure false) := by
  rw [show 4 = 3 + 1 by decide, ReactiveApplication.runRounds_add,
    beforeLottery_run, PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  rw [lottery_round, mix_map, PMF.pure_map, PMF.pure_map,
    acceptedLottery_accepted, omittedLottery_not_accepted]

/-- Both initialized late sending times have exactly the same receipt law,
while retaining their different native pending-observation records. -/
theorem initialized_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      9 (initialExecution bit label)).map accepted =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure true) (PMF.pure false) := by
  rw [show 9 = 5 + 4 by decide, ReactiveApplication.runRounds_add]
  fin_cases slot
  · change ((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 0) 5 (initialExecution bit label)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit 0) 4)).map accepted = _
    rw [firstBob_run, mix_bind, PMF.pure_bind, PMF.pure_bind, mix_map,
      after_observation_receipt_law, after_observation_receipt_law, mix_self]
  · change ((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 1) 5 (initialExecution bit label)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit 1) 4)).map accepted = _
    rw [secondBob_run, PMF.pure_bind, after_observation_receipt_law]

theorem initialized_receipt_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      9 (initialExecution bit label)).map accepted) true).toReal = inclusionProbability weight := by
  rw [initialized_receipt_law, mix_apply_toReal]
  simp [PMF.pure_apply]

/-- No later player, scheduler or malformed response can erase an accepting
receipt already produced by the actual late inclusion. -/
theorem continued_receipt_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (laterScheduler : app.Scheduler) (players : Player → app.Policy) (count : Nat) :
    inclusionProbability weight ≤
      ((((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit slot) 4 (bobObserved bit label slot seen)).bind
          (app.runRounds laterScheduler players count)).map accepted) true).toReal := by
  have acceptedLaw : (app.runRounds laterScheduler players count
      (acceptedLottery bit label slot seen)).map accepted = PMF.pure true := by
    calc
      _ = (app.runRounds laterScheduler players count
          (acceptedLottery bit label slot seen)).map (fun _ => true) := by
        apply map_congr_on_support
        intro execution supported
        apply decide_eq_true
        exact (app.receipt_policyInvariant players ((alice, 0), true)).runRounds
          laterScheduler count (acceptedLottery bit label slot seen) execution
            (acceptedLottery_receipt bit label slot seen) supported
      _ = _ := pmf_map_fun_const _ _
  rw [show 4 = 3 + 1 by decide, ReactiveApplication.runRounds_add,
    beforeLottery_run, PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  rw [lottery_round, mix_bind, PMF.pure_bind, PMF.pure_bind, mix_map, acceptedLaw,
    mix_apply_toReal]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, mul_one]
  exact le_add_of_nonneg_right (mul_nonneg
    (sub_nonneg.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le)
    ENNReal.toReal_nonneg)

theorem continued_initialized_receipt_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (laterScheduler : app.Scheduler) (players : Player → app.Policy) (count : Nat) :
    inclusionProbability weight ≤
      ((((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit slot) 9 (initialExecution bit label)).bind
          (app.runRounds laterScheduler players count)).map accepted) true).toReal := by
  rw [show 9 = 5 + 4 by decide, ReactiveApplication.runRounds_add, PMF.bind_bind]
  fin_cases slot
  · change inclusionProbability weight ≤
      ((((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit 0) 5 (initialExecution bit label)).bind fun observed =>
          (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
            (latePlayers bit 0) 4 observed).bind
              (app.runRounds laterScheduler players count)).map accepted) true).toReal
    rw [firstBob_run, mix_bind, PMF.pure_bind, PMF.pure_bind, mix_map, mix_apply_toReal]
    have seen := continued_receipt_probability weight nonnegative bit label 0 true
      laterScheduler players count
    have missed := continued_receipt_probability weight nonnegative bit label 0 false
      laterScheduler players count
    linarith
  · change inclusionProbability weight ≤
      ((((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit 1) 5 (initialExecution bit label)).bind fun observed =>
          (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
            (latePlayers bit 1) 4 observed).bind
              (app.runRounds laterScheduler players count)).map accepted) true).toReal
    rw [secondBob_run, PMF.pure_bind]
    exact continued_receipt_probability weight nonnegative bit label 1 false
      laterScheduler players count

theorem terminal_receipt_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    inclusionProbability weight ≤
      (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit slot) LateOpeningRuntimeService.horizon (initialExecution bit label)).map
          accepted) true).toReal := by
  change inclusionProbability weight ≤
      (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit slot) (9 + 17) (initialExecution bit label)).map accepted) true).toReal
  rw [ReactiveApplication.runRounds_add]
  exact continued_initialized_receipt_probability weight nonnegative bit label slot
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot) 17

/-- Even within the same partially public service-and-erasure class, no
positive failure floor holds for a canonical late opening's final receipt.
The nine-command lottery itself has strictly positive failure probability. -/
theorem exists_joint_service_below_failure_floor (floor : ℝ) (positive : 0 < floor)
    (atMost : floor ≤ 1) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      inclusionProbability weight < 1 ∧ 1 - inclusionProbability weight < floor ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      ∀ (bit : Bool) (label : Fin 3) (slot : Fin 2),
        (initialPhysical bit label) ∈ initial.support ∧
        (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit slot) 9 (initialExecution bit label)).map accepted) true).toReal =
            inclusionProbability weight ∧
        1 - (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit slot) LateOpeningRuntimeService.horizon (initialExecution bit label)).map
            accepted) true).toReal < floor := by
  let probability : ℝ := 1 - floor / 2
  have probabilityNonnegative : 0 ≤ probability := by dsimp only [probability]; linarith
  have belowOne : probability < 1 := by dsimp only [probability]; linarith
  let weight : ℝ := probability / (1 - probability)
  have nonnegative : 0 ≤ weight := by dsimp only [weight]; positivity
  have realized : inclusionProbability weight = probability := by
    rw [inclusionProbability_eq]
    exact
      (MessageNetwork.chooseWithOutside_singleton_toReal weight nonnegative (alice, 0)).symm.trans
      (MessageNetwork.chooseWithOutside_realizes_probability probability
        probabilityNonnegative belowOne (alice, 0)).1
  have close : 1 - inclusionProbability weight < floor := by
    rw [realized]
    dsimp only [probability]
    linarith
  refine ⟨weight, nonnegative, realized ▸ belowOne, close,
    LateOpeningRuntimeService.contract weight nonnegative,
    LateOpeningRuntimeServiceErasure.scheduler_blind weight nonnegative, ?_⟩
  intro bit label slot
  have terminal := terminal_receipt_probability weight nonnegative bit label slot
  exact ⟨initialPhysical_supported bit label,
    initialized_receipt_probability weight nonnegative bit label slot, by linarith⟩

end Vegas.Examples.LateOpeningRuntimeReliability
