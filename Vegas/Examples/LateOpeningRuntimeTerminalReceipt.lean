/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeReliability
import Interaction.ReactiveStopping

/-! # Exact terminal receipts for the actual late-opening service

After its pending-packet lottery, the service never includes another Alice
identifier. Alice's accepting receipt therefore has the same law at settlement
as immediately after the lottery, even with arbitrary later raw responses.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeTerminalReceipt

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
open LateOpeningRuntimeReliability

private theorem latestAuthor_not_alice (view : app.EnvironmentView) :
    latestAuthor bob view ≠ .include (alice, 0) := by
  unfold latestAuthor
  split
  · simp
  · rename_i message found
    have selected := (List.find?_eq_some_iff_append.mp found).1
    have author : message.id.1 = bob := (of_decide_eq_true selected).1
    intro same
    have identified := ReactiveApplication.Command.include.inj same
    have equal : alice = bob := by
      simpa only [identified] using author
    exact (by decide : alice ≠ bob) equal

private theorem after_lottery_not_include (weight : ℝ) (nonnegative : 0 ≤ weight)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (late : 9 ≤ past.length) (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      past view).support) : command ≠ .include (alice, 0) := by
  change command ∈ (stageChoice weight nonnegative past.length view).support at selected
  generalize positionEq : past.length = position at selected late
  by_cases inside : position < 26
  · interval_cases position <;> try omega
    all_goals simp only [stageChoice, PMF.mem_support_pure_iff] at selected
    all_goals subst command
    all_goals first
      | exact latestAuthor_not_alice view
      | solve | simp
      | split <;> first | exact latestAuthor_not_alice view | simp
  · have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, PMF.mem_support_pure_iff] at selected
    subst command
    simp

private theorem accepted_environment (execution next : app.Execution) (command : app.Command)
    (excluded : command ≠ .include (alice, 0))
    (reached : next ∈ (execution.environmentStep app command).support) :
    accepted next = accepted execution := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sampled, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨physical, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      have different : id ≠ (alice, 0) := by
        intro same
        exact excluded (same ▸ rfl)
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold accepted ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message => simp [List.mem_append, Ne.symm different]

private theorem round_receipt (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution next : app.Execution)
    (late : 9 ≤ execution.environmentRecall.length)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players execution).support) :
    9 ≤ next.environmentRecall.length ∧ accepted next = accepted execution := by
  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, supported, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have receipt := accepted_environment execution middle command
    (after_lottery_not_include weight nonnegative _ _ late command selected) supported
  have length : middle.environmentRecall.length = execution.environmentRecall.length + 1 := by
    obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ supported
    simp only [List.length_append, List.length_singleton]
  cases actorEq : command.actor? app with
  | none =>
      simp only [ReactiveApplication.resume, actorEq] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact ⟨by omega, receipt⟩
  | some who =>
      simp only [ReactiveApplication.resume, actorEq, ReactiveApplication.invoke] at resumed
      obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ resumed
      refine ⟨?_, ?_⟩
      · rw [app.respond_environmentRecall]
        omega
      · unfold accepted
        rw [app.respond_receipts]
        exact receipt

/-- Every supported continuation under this scheduler preserves Alice's
receipt once the lottery has run. The later raw policies are unrestricted. -/
theorem continuation_preserves_receipt (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution next : app.Execution)
    (late : 9 ≤ execution.environmentRecall.length)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) :
    9 ≤ next.environmentRecall.length ∧ accepted next = accepted execution := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨late, rfl⟩
  | succ count ih =>
      obtain ⟨middle, stepped, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨lateMiddle, retained⟩ := round_receipt weight nonnegative players
        execution middle late stepped
      obtain ⟨lateNext, finalReceipt⟩ := ih middle lateMiddle continued
      exact ⟨lateNext, finalReceipt.trans retained⟩

theorem continuation_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution : app.Execution)
    (late : 9 ≤ execution.environmentRecall.length) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).map accepted = PMF.pure (accepted execution) := by
  calc
    _ = (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        players count execution).map (fun _ => accepted execution) := by
      apply map_congr_on_support
      intro next supported
      exact (continuation_preserves_receipt weight nonnegative players count
        execution next late supported).2
    _ = _ := pmf_map_fun_const _ _

/-- Both legal initialized late timing policies retain their exact receipt
law under every later raw policy, as long as this service is unchanged. -/
theorem initialized_continuation_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (players : Player → app.Policy) (count : Nat) :
    (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) 9 (initialExecution bit label)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          players count)).map accepted) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure true) (PMF.pure false) := by
  rw [PMF.map_bind]
  calc
    _ = (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit slot) 9 (initialExecution bit label)).bind
          (fun execution => PMF.pure (accepted execution)) := by
      apply bind_congr_on_support
      intro execution supported
      have cursor := app.runRounds_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
        9 (initialExecution bit label) execution supported
      exact continuation_receipt_law weight nonnegative players count execution (by
        simpa only [initialExecution, ReactiveApplication.Execution.initial,
          List.length_nil, zero_add] using cursor.ge)
    _ = (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        (latePlayers bit slot) 9 (initialExecution bit label)).map accepted := by
      exact PMF.bind_pure_comp _ _
    _ = _ := initialized_receipt_law weight nonnegative bit label slot

theorem terminal_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) LateOpeningRuntimeService.horizon
        (initialExecution bit label)).map accepted =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure true) (PMF.pure false) := by
  change (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (latePlayers bit slot) (9 + 17) (initialExecution bit label)).map accepted = _
  rw [ReactiveApplication.runRounds_add]
  exact initialized_continuation_receipt_law weight nonnegative bit label slot
    (latePlayers bit slot) 17

theorem terminal_receipt_probability (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) LateOpeningRuntimeService.horizon
        (initialExecution bit label)).map accepted) true).toReal =
      inclusionProbability weight := by
  rw [terminal_receipt_law, mix_apply_toReal]
  simp [PMF.pure_apply]

theorem terminal_failure_probability_positive (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    0 < 1 - (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) LateOpeningRuntimeService.horizon
        (initialExecution bit label)).map accepted) true).toReal := by
  rw [terminal_receipt_probability]
  exact sub_pos.mpr (MessageNetwork.inclusionMass_below_one weight nonnegative 1)

/-- Arbitrarily small, strictly positive terminal failure is realized by one
finite-weight builder satisfying the complete all-raw contract and erasure
independence. Both legal initialized late timing policies have exactly this
same terminal receipt law. -/
theorem exists_joint_service_with_exact_failure (floor : ℝ) (positive : 0 < floor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      ∀ (bit : Bool) (label : Fin 3) (slot : Fin 2),
        (initialPhysical bit label) ∈ initial.support ∧
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit slot) LateOpeningRuntimeService.horizon
            (initialExecution bit label)).map accepted =
          mix (inclusionProbability weight)
            (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
            (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
            (PMF.pure true) (PMF.pure false) ∧
        0 < 1 - (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit slot) LateOpeningRuntimeService.horizon
            (initialExecution bit label)).map accepted) true).toReal ∧
        1 - (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (latePlayers bit slot) LateOpeningRuntimeService.horizon
            (initialExecution bit label)).map accepted) true).toReal < floor := by
  have clippedPositive : 0 < min floor 1 := lt_min positive (by norm_num)
  obtain ⟨weight, nonnegative, _, close, contract, blind, _⟩ :=
    exists_joint_service_below_failure_floor (min floor 1) clippedPositive (min_le_right _ _)
  have weightPositive : 0 < weight := by
    by_contra notPositive
    have zero : weight = 0 := le_antisymm (le_of_not_gt notPositive) nonnegative
    rw [zero, inclusionProbability_eq] at close
    norm_num at close
  refine ⟨weight, nonnegative, weightPositive, contract, blind, ?_⟩
  intro bit label slot
  refine ⟨initialPhysical_supported bit label,
    terminal_receipt_law weight nonnegative bit label slot,
    terminal_failure_probability_positive weight nonnegative bit label slot, ?_⟩
  rw [terminal_receipt_probability]
  exact close.trans_le (min_le_left _ _)

end Vegas.Examples.LateOpeningRuntimeTerminalReceipt
