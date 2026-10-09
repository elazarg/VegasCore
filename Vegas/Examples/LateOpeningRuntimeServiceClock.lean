/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeService
import Interaction.ReactiveServiceInvariant

/-! # The public calendar clock under arbitrary raw responses -/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

def stageTicks : Nat → Nat
  | 2 | 6 | 9 | 15 | 16 | 17 | 21 | 22 | 23 | 24 => 1
  | _ => 0

def clockAt (position : Nat) : Nat := ((List.range position).map stageTicks).sum

theorem latestAuthor_passive (who : Player) (view : app.EnvironmentView) :
    (latestAuthor who view).actor? app = none ∧
      runtime.reactiveTicks leaks (latestAuthor who view) = 0 := by
  unfold latestAuthor
  split <;> exact ⟨rfl, rfl⟩

theorem lottery_passive (weight : ℝ) (nonnegative : 0 ≤ weight) (view : app.EnvironmentView)
    (command : app.Command)
    (selected : command ∈ (app.pendingLotteryScheduler weight nonnegative [] view).support) :
    command.actor? app = none ∧ runtime.reactiveTicks leaks command = 0 := by
  rw [ReactiveApplication.pendingLotteryScheduler, PMF.support_map] at selected
  obtain ⟨chosen, _, rfl⟩ := selected
  cases chosen <;> exact ⟨rfl, rfl⟩

theorem scheduler_ticks (weight : ℝ) (nonnegative : 0 ≤ weight)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command)
    (selected : command ∈ (scheduler weight nonnegative past view).support) :
    runtime.reactiveTicks leaks command = stageTicks past.length := by
  change command ∈ (stageChoice weight nonnegative past.length view).support at selected
  generalize positionEq : past.length = position at selected ⊢
  by_cases inside : position < 26
  · interval_cases position <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals try subst command
    all_goals first
      | exact (latestAuthor_passive _ _).2
      | exact (lottery_passive _ _ _ _ selected).2
      | rfl
      | split <;> first | exact (latestAuthor_passive _ _).2 | rfl
  · have outside : 26 ≤ position := by omega
    have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    have noTick : stageTicks position = 0 := by
      unfold stageTicks
      split <;> omega
    rw [idle, PMF.mem_support_pure_iff] at selected
    subst command
    exact noTick.symm

theorem clockAt_succ (position : Nat) :
    clockAt (position + 1) = clockAt position + stageTicks position := by
  simp [clockAt, List.range_succ]

def Clocked (execution : app.Execution) : Prop :=
  execution.application.clock = clockAt execution.environmentRecall.length

private theorem environmentRecall_append (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] := by
  obtain ⟨earlier, _, rfl⟩ := PMF.support_map .. ▸ reached
  rfl

theorem clock_invariant (weight : ℝ) (nonnegative : 0 ≤ weight) :
    app.ServiceInvariant (scheduler weight nonnegative) Clocked where
  respond execution who action clocked := by
    unfold Clocked at clocked ⊢
    rw [runtime.reactive_respond_clock, app.respond_environmentRecall]
    exact clocked
  environment execution next command clocked selected reached := by
    unfold Clocked at clocked ⊢
    rw [runtime.reactive_environmentStep_clock leaks execution next command reached,
      clocked, scheduler_ticks weight nonnegative _ _ command selected,
      environmentRecall_append execution next command reached,
      List.length_append, List.length_singleton, clockAt_succ]

private theorem clock_initial (state : app.State) (supported : state ∈ initial.support) :
    Clocked (ReactiveApplication.Execution.initial app state) := by
  obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

/-- The declared public clocks hold on every raw history, including histories
with malformed packets, duplicate sends, arbitrary forwarding and silence. -/
theorem clock_history (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control)) :
    control.execution.application.clock = clockAt control.execution.environmentRecall.length :=
  (clock_invariant weight nonnegative).history initial horizon clock_initial trace

theorem displayed_clocks : clockAt 0 = 0 ∧ clockAt 3 = 1 ∧ clockAt 7 = 2 ∧ clockAt 10 = 3 ∧
    clockAt 18 = 6 ∧ clockAt 25 = 10 ∧ clockAt horizon = 10 := by
  decide

end Vegas.Examples.LateOpeningRuntimeService
