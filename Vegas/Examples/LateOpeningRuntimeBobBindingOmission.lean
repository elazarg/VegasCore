/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobRawBinding
import Vegas.Examples.LateOpeningRuntimeLatePrefix
import Interaction.ReactiveStopping

/-! # An omitted first binding cannot be repaired

After the first binding receipt, an unfinished Bob binding disables both
optional service commands. The next three commands only advance the clock,
and expiry stores failure before Bob can act again. This argument allows
every later raw policy and every earlier pending envelope.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingOmission

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeLatePrefix

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem unfinished_of_absent (physical : app.State)
    (absent : physical.config.store (.inr bobBindEvent) = none) :
    bobBindEvent ∉ physical.config.cut.completed := by
  intro completed
  have present := (physical.config.output_available bobBindEvent).mpr completed
  change (physical.config.store (.inr bobBindEvent)).isSome = true at present
  rw [absent] at present
  cases present

private theorem prefix_round (players : Player → app.Policy) (execution next : app.Execution)
    (early : 13 ≤ execution.environmentRecall.length)
    (late : execution.environmentRecall.length < 18)
    (absent : execution.application.config.store (.inr bobBindEvent) = none)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players execution).support) :
    next.application.config = execution.application.config := by
  have unfinished := unfinished_of_absent execution.application absent
  have notDone : bobBindEvent ∉ execution.application.publicView.observation.completionOrder :=
    fun done => unfinished ((execution.application.config.history_exact bobBindEvent).mp done)
  change bobBindEvent ∉
    (execution.observeEnvironment app).application.observation.completionOrder at notDone
  generalize atCursor : execution.environmentRecall.length = position at early late
  interval_cases position
  all_goals
    obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
      (execution.observeEnvironment app)).support at selected
    rw [atCursor] at selected
  · simp only [stageChoice, ite_eq_right notDone, PMF.mem_support_pure_iff] at selected
    subst command
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume, PMF.mem_support_pure_iff] at moved
    subst next
    rfl
  · simp only [stageChoice, ite_eq_right notDone, PMF.mem_support_pure_iff] at selected
    subst command
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume, PMF.mem_support_pure_iff] at moved
    subst next
    rfl
  all_goals
    simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    subst command
    rw [ReactiveApplication.dispatch, recorded_clock, PMF.pure_bind] at moved
    simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      PMF.mem_support_pure_iff] at moved
    subst next
    rfl

/-- No policy can emit a repairing response while the conditional callback
gate is disabled; the entire typed configuration remains unchanged. -/
theorem prefix_config (players : Player → app.Policy) (count : Nat)
    (execution next : app.Execution) (early : 13 ≤ execution.environmentRecall.length)
    (late : execution.environmentRecall.length + count ≤ 18)
    (absent : execution.application.config.store (.inr bobBindEvent) = none)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) :
    next.application.config = execution.application.config := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, stepped, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have same := prefix_round weight nonnegative players execution middle early (by omega)
        absent stepped
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players execution middle stepped
      have result := ih middle (by omega) (by omega) (same ▸ absent) continued
      exact result.trans same

/-- Every raw continuation after an absent first binding expires that binding
before the next unconditional Bob callback. -/
theorem omitted_binding_expires (players : Player → app.Policy) (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨13, none, execution⟩))
    (absent : execution.application.config.store (.inr bobBindEvent) = none)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 13 execution).support) :
    final.application.config.store (.inr bobBindEvent) =
      some (.failure : PublicationResult Answer) := by
  have budget := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change execution.environmentRecall.length + 13 = 26 at budget
  have cursor : execution.environmentRecall.length = 13 := by omega
  rw [show 13 = 5 + 8 by rfl, app.runRounds_add, PMF.support_bind] at reached
  obtain ⟨due, reachedDue, remaining⟩ := Set.mem_iUnion₂.mp reached
  have same := prefix_config weight nonnegative players 5 execution due (by omega)
    (by omega) absent reachedDue
  have dueCursor : due.environmentRecall.length = 18 := by
    rw [app.runRounds_environmentRecall_length
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 5 execution due reachedDue,
        cursor]
  obtain ⟨dueTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 8 5 execution due trace
      reachedDue
  have phase := completion_phase_history weight nonnegative ⟨8, none, due⟩ dueTrace
  obtain ⟨inputs, valid⟩ := phase.invariant
  have pastAlice : 11 ≤ due.environmentRecall.length := by omega
  have aliceDone := (phase.afterAlice pastAlice).1
  have ready : due.application.config.cut.Ready bobBindEvent := by
    refine ⟨unfinished_of_absent _ (same ▸ absent), ?_⟩
    intro event earlier
    fin_cases event
    · exact aliceDone
    · exact ((by decide : (1 : Fin 3) ∉ nativeGraph.order.predecessors bobBindEvent) earlier).elim
    · exact ((by decide : (2 : Fin 3) ∉ nativeGraph.order.predecessors bobBindEvent) earlier).elim
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor bobBindEvent ready rfl
  have enteredBound := (phase.afterAlice pastAlice).2 entered activated
  have dueClock : due.application.clock = 6 := by
    rw [clock_history weight nonnegative _ dueTrace, dueCursor]
    decide
  let expired : app.Execution := recorded due (.application (.expire bobBindEvent))
    (due.application.complete bobBindEvent ready (.failure : PublicationResult Answer) .failure)
  have law := environmentStep_expire_bind_eq LateOpeningRuntimeService.runtime due.application
    bobBindEvent ready entered activated (by change 3 ≤ due.application.clock - entered; omega)
      bob (.range 0 5) rfl rfl rfl
  have environment : due.environmentStep app (.application (.expire bobBindEvent)) =
      PMF.pure expired := by
    rw [ReactiveApplication.Execution.environmentStep]
    change ((environmentStep LateOpeningRuntimeService.runtime due.application
      (.expire bobBindEvent)).map _).map _ = _
    rw [law, PMF.pure_map, PMF.pure_map]
    rfl
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players due =
      PMF.pure expired := by
    rw [fixed_round weight nonnegative players due expired 18 _ dueCursor rfl environment]
    rfl
  change final ∈ ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
    players due).bind (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 7)).support at remaining
  rw [first, PMF.pure_bind] at remaining
  have stored : expired.application.config.store (.inr bobBindEvent) =
      some (.failure : PublicationResult Answer) := by
    change (due.application.config.complete bobBindEvent ready _ _).store _ = _
    rw [EventGraph.Config.store_output, EventGraph.Config.complete_output_same]
  exact (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
      (.inr bobBindEvent) (.failure : PublicationResult Answer)) players).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 7 expired final stored remaining

end Vegas.Examples.LateOpeningRuntimeBobBindingOmission
