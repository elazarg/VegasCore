/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Vegas.Examples.LateOpeningRuntimeBobFreshBinding

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobRecallStability

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

private theorem command_not_bob (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution) (position : 5 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length < 11) (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall
      (execution.observeEnvironment app)).support) : command.actor? app ≠ some bob := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    at selected
  generalize cursorEq : execution.environmentRecall.length = cursor at selected position early
  interval_cases cursor <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals first
    | solve
      | subst command
        simp only [ReactiveApplication.Command.actor?]
        decide
    | solve
      | subst command
        rw [(latestAuthor_passive bob _).1]
        decide
    | change command ∈ (app.pendingLotteryScheduler weight nonnegative []
        (execution.observeEnvironment app)).support at selected
      rw [(lottery_passive weight nonnegative _ command selected).1]
      decide

private theorem round_recall_of_excluded (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution next : app.Execution)
    (excluded : ∀ command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall (execution.observeEnvironment app)).support,
        command.actor? app ≠ some bob)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players execution).support) :
    next.recall bob = execution.recall bob := by
  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, supported, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have notBob := excluded command selected
  have prior := app.environmentStep_recall execution middle command supported
  cases actor : command.actor? app with
  | none =>
      rw [actor] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact congrFun prior bob
  | some who =>
      have different : bob ≠ who := by intro same; subst who; exact notBob actor
      rw [actor] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      rw [app.respond_recall_other middle who bob different response, prior]

/-- No receiver response occurs between the rejected early service and the
first binding callback, regardless of the other player's policy. -/
theorem before_binding_recall (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution next : app.Execution)
    (position : 5 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length + count ≤ 11)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : next.recall bob = execution.recall bob := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have record := round_recall_of_excluded weight nonnegative players execution middle
        (fun command selected => command_not_bob weight nonnegative execution position
          (by omega) command selected) moved
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative)
        players execution middle moved
      have kept := ih middle (by omega) (by omega) continued
      exact kept.trans record

private theorem first_command_not_bob (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution) (early : execution.environmentRecall.length < 4)
    (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall (execution.observeEnvironment app)).support) :
    command.actor? app ≠ some bob := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    at selected
  generalize cursorEq : execution.environmentRecall.length = cursor at selected early
  interval_cases cursor <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals first
    | solve
      | subst command
        simp only [ReactiveApplication.Command.actor?]
        decide
    | subst command
      rw [(latestAuthor_passive alice _).1]
      decide

/-- Prior to the first actual Bob callback, no Bob response can enter recall. -/
theorem before_first_callback_recall (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution next : app.Execution)
    (early : execution.environmentRecall.length + count ≤ 4)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : next.recall bob = execution.recall bob := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have record := round_recall_of_excluded weight nonnegative players execution middle
        (fun command selected => first_command_not_bob weight nonnegative execution
          (by omega) command selected) moved
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players execution middle moved
      have kept := ih middle (by omega) continued
      exact kept.trans record

end Vegas.Examples.LateOpeningRuntimeBobRecallStability
