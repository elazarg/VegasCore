/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeMonitoring

/-! # Persistent report liabilities bound every later raw continuation

After one ambient submission, monitoring produces a rejected Alice receipt
with probability one half. Every subsequent native plan preserves that receipt.
The following bound quantifies arbitrary continuation policies and instructions;
neither a later opening failure nor a second violation cancels the first debit.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem native_dispatch_receipts_prefix (players : Player → nativeApp.Policy)
    (command : nativeApp.Command) (before after : nativeApp.Execution)
    (supported : after ∈ (nativeApp.dispatch players command before).support) :
    before.receipts <+: after.receipts := by
  obtain ⟨middle, reached, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have retained := nativeApp.environmentStep_receipts_prefix before middle command reached
  cases actor : command.actor? nativeApp with
  | none =>
      simp only [ReactiveApplication.resume, actor] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact retained
  | some who =>
      simp only [ReactiveApplication.resume, actor] at moved
      obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ moved
      rw [nativeApp.respond_receipts]
      exact retained

theorem native_plan_receipts_prefix (players : Player → nativeApp.Policy)
    (plan : List (ServiceInstruction nativeGraph)) (before after : nativeApp.Execution)
    (supported : after ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan before).support) :
    before.receipts <+: after.receipts := by
  induction plan generalizing before with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | cons instruction rest ih =>
      obtain ⟨middle, reached, moved⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨command, _, executed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (native_dispatch_receipts_prefix players command before middle executed).trans
        (ih middle moved)

theorem source_alice_utility_le_one (result : Results) : utility result alice ≤ 1 := by
  rw [utility_alice]
  cases result with
  | mk opening guess =>
      cases opening <;> simp only [correctness, openingPenalty]
      · norm_num
      · split_ifs <;> norm_num

theorem native_alice_utility_le (charge : ℝ) (execution : nativeApp.Execution) :
    nativeComparisonExecutionUtility charge alice execution ≤
      1 - if aliceLiability execution then charge else 0 := by
  unfold nativeComparisonExecutionUtility
  simpa only [true_and] using
    sub_le_sub_right (source_alice_utility_le_one (nativeResults execution.application.config))
      (if aliceLiability execution then charge else 0)

theorem native_alice_continuation_le (charge : ℝ) (nonnegative : 0 ≤ charge)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph))
    (execution : nativeApp.Execution) :
    expect (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan execution)
      (nativeComparisonExecutionUtility charge alice) ≤
        1 - if aliceLiability execution then charge else 0 := by
  refine expect_le_const _ _ (payoffIntegrable_of_bounded _ _
    (nativeComparisonExecutionUtility_abs_le charge alice)) _ fun after supported => ?_
  apply (native_alice_utility_le charge after).trans
  have retained := native_plan_liability players plan execution after supported
  cases alarm : aliceLiability execution with
  | false =>
      cases aliceLiability after <;> simp [nonnegative]
  | true => rw [retained alarm]

/-- The charge bounds arbitrary complete response policies after the report,
including deliberate final withholding or further malformed calls. -/
theorem submitted_continuation_utility_le (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) (charge : ℝ) (nonnegative : 0 ≤ charge)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    expect ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan))
        (nativeComparisonExecutionUtility charge alice) ≤ 1 - charge / 2 := by
  have prefixFinite : (monitoredPrefixLaw bit (submissionAction submission)).support.Finite := by
    rw [monitoredPrefixLaw, PMF.support_map]
    exact (MessageNetwork.ObservationRule.FiniteSupport.support_finite (leaks := nativeLeaks)
      _ _).image _
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _
    (nativeComparisonExecutionUtility_abs_le charge alice))]
  apply le_trans (expect_mono (fun execution _ =>
    native_alice_continuation_le charge nonnegative players plan execution)
    (payoffIntegrable_of_finite_support _ _ prefixFinite)
    (payoffIntegrable_of_finite_support _ _ prefixFinite))
  have alarms := expect_map (fun execution : nativeApp.Execution =>
    aliceLiability execution) (monitoredPrefixLaw bit (submissionAction submission))
      (fun alarm : Bool => 1 - if alarm then charge else 0)
  simp only [Function.comp_def] at alarms
  rw [← alarms, submission_monitoring_law, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _)
    (payoffIntegrable_pure _ _)]
  simp only [expect_pure, ↓reduceIte, Bool.false_eq_true]
  ring_nf
  exact le_rfl

end Vegas.Examples.MonitoredGuessing
