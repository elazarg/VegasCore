/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeMonitoring

/-! # Persistent report liabilities bound every later raw continuation

After one ambient submission, monitoring produces a rejected Alice receipt
with probability one half. Every subsequent native plan preserves that receipt.
The following bound quantifies arbitrary continuation policies and instructions;
neither a later opening failure nor a second violation cancels the first debit.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem native_dispatch_receipts_prefix (players : Player → nativeApp.Policy)
    (command : nativeApp.Command) (before after : nativeApp.Execution)
    (supported : after ∈ (nativeApp.dispatch players command before).support) :
    before.receipts <+: after.receipts := by
  obtain ⟨middle, reached, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have retained := nativeApp.environmentStep_receipts_prefix before middle command reached
  cases actor : command.actor? nativeApp with
  | none =>
      simp only [ReactiveApplication.resume, actor] at moved
      cases FinDist.mem_support_pure.mp moved
      exact retained
  | some who =>
      simp only [ReactiveApplication.resume, actor] at moved
      obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ moved
      rw [nativeApp.respond_receipts]
      exact retained

theorem native_plan_receipts_prefix (players : Player → nativeApp.Policy)
    (plan : List (ServiceInstruction nativeGraph)) (before after : nativeApp.Execution)
    (supported : after ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan before).support) :
    before.receipts <+: after.receipts := by
  induction plan generalizing before with
  | nil =>
      cases FinDist.mem_support_pure.mp supported
      rfl
  | cons instruction rest ih =>
      obtain ⟨middle, reached, moved⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨command, _, executed⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      exact (native_dispatch_receipts_prefix players command before middle executed).trans
        (ih middle moved)

theorem rejected_alice_persists {before after : List (MessageId Player × Bool)}
    (retained : before <+: after) (rejected : rejectedAlice before = true) :
    rejectedAlice after = true := by
  obtain ⟨tail, rfl⟩ := retained
  change (before ++ tail).any _ = true
  rw [List.any_append]
  change (rejectedAlice before || rejectedAlice tail) = true
  rw [rejected]
  rfl

theorem source_alice_utility_le_one (result : Results) : utility result alice ≤ 1 := by
  rw [utility_alice]
  cases result with
  | mk opening guess =>
      cases opening <;> simp only [correctness, openingPenalty]
      · norm_num
      · split_ifs <;> norm_num

theorem native_alice_utility_le (deposit : ℝ) (execution : nativeApp.Execution) :
    nativeExecutionUtility deposit alice execution ≤
      1 - if rejectedAlice execution.receipts then deposit else 0 := by
  unfold nativeExecutionUtility
  simpa only [true_and] using
    sub_le_sub_right (source_alice_utility_le_one (nativeResults execution.application.config))
      (if rejectedAlice execution.receipts then deposit else 0)

theorem native_alice_continuation_le (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph))
    (execution : nativeApp.Execution) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan execution).expect
      (nativeExecutionUtility deposit alice) ≤
        1 - if rejectedAlice execution.receipts then deposit else 0 := by
  apply FinDist.expect_le_of_forall
  intro after supported
  apply (native_alice_utility_le deposit after).trans
  have retained := native_plan_receipts_prefix players plan execution after supported
  cases alarm : rejectedAlice execution.receipts with
  | false =>
      cases rejectedAlice after.receipts <;> simp [nonnegative]
  | true => rw [rejected_alice_persists retained alarm]

/-- The charge bounds arbitrary complete response policies after the report,
including deliberate final withholding or further malformed calls. -/
theorem submitted_continuation_utility_le (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan)).expect
        (nativeExecutionUtility deposit alice) ≤ 1 - deposit / 2 := by
  rw [FinDist.expect_bind]
  apply le_trans (FinDist.expect_mono (fun execution _ =>
    native_alice_continuation_le deposit nonnegative players plan execution))
  rw [← FinDist.expect_map (fun execution : nativeApp.Execution =>
    rejectedAlice execution.receipts) (monitoredPrefixLaw bit (submissionAction submission))
      (fun alarm : Bool => 1 - if alarm then deposit else 0)]
  rw [submission_monitoring_law, FinDist.expect_mix]
  simp only [FinDist.expect_pure, ↓reduceIte, Bool.false_eq_true]
  ring_nf
  exact le_rfl

end VegasTests.MonitoredGuessing
