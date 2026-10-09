/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionRecovery
import Interaction.ReactiveSchedulerPrefix
import Interaction.ReactiveMonitoring

/-! # Arbitrary late inclusion reliability under the native service contract

Changing the public lottery at one late inclusion round preserves every
all-history service promise. A genuine initialized, canonical late opening
then has exactly the chosen receipt probability. This is an operational
boundary result; it does not assert an equilibrium impossibility.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionReliability

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open CommittedResolutionService

def scheduler (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) : app.Scheduler := fun past view =>
  if past.length = 5 then
    mix probability nonnegative atMost
      (PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view))
      (PMF.pure .wait)
  else CommittedResolutionService.scheduler past view

theorem scheduler_support_subset (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    (scheduler probability nonnegative atMost past view).support ⊆
      (CommittedResolutionService.scheduler past view).support := by
  intro command supported
  unfold scheduler at supported
  split at supported
  · rename_i cursor
    change command ∈ (stageChoice past.length view).support
    rw [cursor]
    change command ∈ (mix (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view))
      (PMF.pure .wait)).support
    rcases support_mix_subset probability nonnegative atMost _ _ supported with
      included | idle
    · apply mem_support_mix_left (3 / 4) (by norm_num) (by norm_num) (by norm_num)
      exact included
    · apply mem_support_mix_right (3 / 4) (by norm_num) (by norm_num) (by norm_num)
      exact idle
  · exact supported

theorem contract (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) :
    AsyncContract (runtime setup) leaks (initialLaw setup) CommittedResolutionService.horizon
      (scheduler probability nonnegative atMost) delay bound :=
  AsyncContract.of_scheduler_support_subset (runtime setup) leaks (initialLaw setup)
    CommittedResolutionService.horizon (scheduler probability nonnegative atMost)
    CommittedResolutionService.scheduler
    (scheduler_support_subset probability nonnegative atMost) delay bound
    CommittedResolutionService.contract

instance finiteNature (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) :
    app.FiniteNature (initialLaw setup) (scheduler probability nonnegative atMost) :=
  app.finiteNature_of_scheduler_support_subset (initialLaw setup)
    (scheduler probability nonnegative atMost) CommittedResolutionService.scheduler
    (scheduler_support_subset probability nonnegative atMost)

def initializedExecution : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (setup.eventInputs (sourceInitial true)))

/-- The late response is reached from a supported initialized state for every lottery. -/
theorem late_response_reached (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) :
    app.runRounds (scheduler probability nonnegative atMost)
      CommittedResolutionRecovery.latePlayers 5 initializedExecution =
      PMF.pure (CommittedResolutionRecovery.lateExecution.respond app alice
        ⟨some CommittedResolutionRecovery.opening⟩) := by
  rw [app.runRounds_eq_of_scheduler_agreement
    (scheduler probability nonnegative atMost) CommittedResolutionRecovery.scheduler
    CommittedResolutionRecovery.latePlayers 5 initializedExecution (by
      intro past view _ upper
      have notLate : past.length ≠ 5 := by
        change past.length < 0 + 5 at upper
        omega
      simp only [scheduler, CommittedResolutionRecovery.scheduler, notLate, ↓reduceIte])]
  exact CommittedResolutionRecovery.late_response_reached

theorem initialized_supported : initializedExecution.application ∈ (initialLaw setup).support := by
  rw [initialLaw, serviceInitialLaw, PMF.support_map]
  refine ⟨sourceInitial true, ?_, rfl⟩
  apply mem_support_mix_left (1 / 4) (by norm_num) (by norm_num) (by norm_num)
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

def waitingExecution : app.Execution :=
  let submitted := CommittedResolutionRecovery.lateExecution.respond app alice
    ⟨some CommittedResolutionRecovery.opening⟩
  { submitted with environmentRecall := submitted.environmentRecall ++
      [⟨submitted.observeEnvironment app, .wait⟩] }

/-- The actual next-round execution law has the chosen success probability. -/
theorem late_round (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) (players : Player → app.Policy) :
    app.round (scheduler probability nonnegative atMost) players
      (CommittedResolutionRecovery.lateExecution.respond app alice
        ⟨some CommittedResolutionRecovery.opening⟩) =
      mix probability nonnegative atMost (PMF.pure CommittedResolutionRecovery.acceptedExecution)
        (PMF.pure waitingExecution) := by
  let submitted := CommittedResolutionRecovery.lateExecution.respond app alice
    ⟨some CommittedResolutionRecovery.opening⟩
  have selected : (runtime setup).reactiveLatest leaks aliceEvent alice
      (submitted.observeEnvironment app) = .include (alice, 0) := by
    rfl
  have included : app.dispatch players (.include (alice, 0)) submitted =
      PMF.pure CommittedResolutionRecovery.acceptedExecution := by
    have actual := (CommittedResolutionRecovery.late_inclusion players).1
    change app.round CommittedResolutionRecovery.scheduler players submitted = _ at actual
    rw [ReactiveApplication.round] at actual
    change (PMF.pure (.include (alice, 0) : app.Command)).bind _ = _ at actual
    simpa only [PMF.pure_bind] using actual
  have idle : app.dispatch players .wait submitted = PMF.pure waitingExecution := by
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  change (scheduler probability nonnegative atMost submitted.environmentRecall
    (submitted.observeEnvironment app)).bind _ = _
  have cursor : submitted.environmentRecall.length = 5 := rfl
  simp only [scheduler, cursor, ↓reduceIte, selected, mix_bind, PMF.pure_bind]
  rw [included, idle]

def accepted (execution : app.Execution) : Bool :=
  decide ((CommittedResolutionRecovery.openingMessage.id, true) ∈ execution.receipts)

/-- No protected-window premise supplies a positive failure floor for late sends. -/
theorem late_receipt_probability (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) (players : Player → app.Policy) :
    (((app.round (scheduler probability nonnegative atMost) players
      (CommittedResolutionRecovery.lateExecution.respond app alice
        ⟨some CommittedResolutionRecovery.opening⟩)).map accepted)
      true).toReal = probability := by
  rw [late_round, mix_map, PMF.pure_map, PMF.pure_map, mix_apply_toReal]
  have success : accepted CommittedResolutionRecovery.acceptedExecution = true := by
    exact decide_eq_true (CommittedResolutionRecovery.late_inclusion players).2.2.1
  have failure : accepted waitingExecution = false := by rfl
  simp [success, failure, PMF.pure_apply]

/-- The six-round native law, retaining the genuine initialized prefix. -/
theorem initialized_receipt_probability (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) :
    (((app.runRounds (scheduler probability nonnegative atMost)
      CommittedResolutionRecovery.latePlayers 6 initializedExecution).map accepted)
      true).toReal = probability := by
  rw [show 6 = 5 + 1 by decide, ReactiveApplication.runRounds_add, late_response_reached,
    PMF.pure_bind]
  simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using
    late_receipt_probability probability nonnegative atMost CommittedResolutionRecovery.latePlayers

/-- Once accepted, the late opening's receipt survives every raw continuation. -/
theorem continued_receipt_probability (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) (laterScheduler : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) :
    probability ≤
      ((((app.runRounds (scheduler probability nonnegative atMost)
        CommittedResolutionRecovery.latePlayers 6 initializedExecution).bind
          (app.runRounds laterScheduler players count)).map accepted) true).toReal := by
  have acceptedLaw :
      (app.runRounds laterScheduler players count
        CommittedResolutionRecovery.acceptedExecution).map accepted = PMF.pure true := by
    calc
      _ = (app.runRounds laterScheduler players count
          CommittedResolutionRecovery.acceptedExecution).map (fun _ => true) := by
        apply map_congr_on_support _
        intro execution supported
        apply decide_eq_true
        exact (app.receipt_policyInvariant players
          (CommittedResolutionRecovery.openingMessage.id, true)).runRounds laterScheduler count
          CommittedResolutionRecovery.acceptedExecution execution
          (CommittedResolutionRecovery.late_inclusion players).2.2.1 supported
      _ = _ := pmf_map_fun_const _ _
  rw [show 6 = 5 + 1 by decide, ReactiveApplication.runRounds_add, late_response_reached,
    PMF.pure_bind]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  rw [late_round, mix_bind, PMF.pure_bind, PMF.pure_bind, mix_map, acceptedLaw,
    mix_apply_toReal]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, mul_one]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr atMost) ENNReal.toReal_nonneg)

/-- The same lower bound holds at the fixture's actual terminal horizon. -/
theorem terminal_receipt_probability (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMost : probability ≤ 1) :
    probability ≤
      (((app.runRounds (scheduler probability nonnegative atMost)
        CommittedResolutionRecovery.latePlayers CommittedResolutionService.horizon
          initializedExecution).map accepted) true).toReal := by
  change probability ≤ (((app.runRounds (scheduler probability nonnegative atMost)
    CommittedResolutionRecovery.latePlayers (6 + 10) initializedExecution).map accepted)
      true).toReal
  rw [ReactiveApplication.runRounds_add]
  exact continued_receipt_probability probability nonnegative atMost
    (scheduler probability nonnegative atMost) CommittedResolutionRecovery.latePlayers 10

/-- Every requested strict failure floor is violated by some public native lottery. -/
theorem exists_contract_below_failure_floor (floor : ℝ) (positive : 0 < floor)
    (atMost : floor ≤ 1) :
    ∃ (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1),
      probability < 1 ∧ 1 - probability < floor ∧
      AsyncContract (runtime setup) leaks (initialLaw setup) CommittedResolutionService.horizon
        (scheduler probability nonnegative bounded) delay bound ∧
      initializedExecution.application ∈ (initialLaw setup).support ∧
      (((app.runRounds (scheduler probability nonnegative bounded)
        CommittedResolutionRecovery.latePlayers 6 initializedExecution).map accepted)
        true).toReal = probability ∧
      probability ≤
        (((app.runRounds (scheduler probability nonnegative bounded)
          CommittedResolutionRecovery.latePlayers CommittedResolutionService.horizon
            initializedExecution).map accepted) true).toReal ∧
      ∀ players : Player → app.Policy,
        (((app.round (scheduler probability nonnegative bounded) players
          (CommittedResolutionRecovery.lateExecution.respond app alice
            ⟨some CommittedResolutionRecovery.opening⟩)).map accepted)
          true).toReal = probability := by
  refine ⟨1 - floor / 2, by linarith, by linarith, by linarith, by linarith,
    contract _ _ _, initialized_supported, initialized_receipt_probability _ _ _,
      terminal_receipt_probability _ _ _, ?_⟩
  intro players
  exact late_receipt_probability _ _ _ players

end Vegas.Examples.CommittedResolutionReliability
