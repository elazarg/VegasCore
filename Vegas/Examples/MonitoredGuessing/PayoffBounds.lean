/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeSanctions

/-! # Native monitoring bounds for arbitrary settlement functions

The monitoring argument uses a bound on terminal settlements, not the
correctness-payoff formula. Every raw submission is covered, together with
every later raw policy and service instruction. Receipt liability persists
even when later calls fail or opening is withheld.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def monitoredSettlement (settlement : Results → ℝ) (charge : ℝ)
    (execution : nativeApp.Execution) : ℝ :=
  settlement (nativeResults execution.application.config) -
    if rejectedAlice execution.receipts then charge else 0

/-- A settlement reads only the finitely many results and the alarm, so its
expectation under every execution law is defined. -/
theorem monitoredSettlement_integrable (settlement : Results → ℝ) (charge : ℝ)
    (law : PMF nativeApp.Execution) :
    PayoffIntegrable law (monitoredSettlement settlement charge) :=
  (payoffIntegrable_map_iff
    (fun execution : nativeApp.Execution =>
      (nativeResults execution.application.config, rejectedAlice execution.receipts)) law
    (fun outcome => settlement outcome.1 - if outcome.2 then charge else 0)).mp
      (payoffIntegrable_of_finite _ _)

theorem settlement_continuation_bound (settlement : Results → ℝ) (upper charge : ℝ)
    (bounded : ∀ result, settlement result ≤ upper) (nonnegative : 0 ≤ charge)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph))
    (execution : nativeApp.Execution) :
    expect (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan execution)
      (monitoredSettlement settlement charge) ≤
        upper - if rejectedAlice execution.receipts then charge else 0 := by
  refine expect_le_const _ _ (monitoredSettlement_integrable settlement charge _) _
    fun after supported => ?_
  apply (sub_le_sub_right (bounded (nativeResults after.application.config)) _).trans
  have retained := native_plan_receipts_prefix players plan execution after supported
  cases alarm : rejectedAlice execution.receipts with
  | false =>
      cases rejectedAlice after.receipts <;> simp [nonnegative]
  | true => rw [rejected_alice_persists retained alarm]

/-- Ordinary passive monitoring imposes the same expected charge on every
initial raw submission, independently of its message contents and all later
strategic responses. Collection remains the specified utility interpretation. -/
theorem submission_settlement_bound (settlement : Results → ℝ) (upper charge : ℝ)
    (bounded : ∀ result, settlement result ≤ upper) (nonnegative : 0 ≤ charge)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    expect ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan))
        (monitoredSettlement settlement charge) ≤ upper - charge / 2 := by
  have prefixFinite : (monitoredPrefixLaw bit (submissionAction submission)).support.Finite := by
    rw [monitoredPrefixLaw, PMF.support_map]
    exact (MessageNetwork.ObservationRule.FiniteSupport.support_finite (leaks := nativeLeaks)
      _ _).image _
  rw [expect_bind_tower _ _ _ (monitoredSettlement_integrable settlement charge _)]
  apply le_trans (expect_mono (fun execution _ =>
    settlement_continuation_bound settlement upper charge bounded nonnegative players plan
      execution)
    (payoffIntegrable_of_finite_support _ _ prefixFinite)
    (payoffIntegrable_of_finite_support _ _ prefixFinite))
  have alarms := expect_map (fun execution : nativeApp.Execution =>
    rejectedAlice execution.receipts) (monitoredPrefixLaw bit (submissionAction submission))
      (fun alarm : Bool => upper - if alarm then charge else 0)
  simp only [Function.comp_def] at alarms
  rw [← alarms, submission_monitoring_law, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _)
    (payoffIntegrable_pure _ _)]
  simp only [expect_pure, ↓reduceIte, Bool.false_eq_true]
  ring_nf
  exact le_rfl

/-- A finite charge suffices against every raw submission when prescribed
silent continuation yields at least `lower`. Neither the source nor the
runtime is restricted to correctness rewards. -/
theorem submission_deterred_by_range (settlement : Results → ℝ) (lower upper charge : ℝ)
    (bounded : ∀ result, settlement result ≤ upper) (nonnegative : 0 ≤ charge)
    (sufficient : 2 * (upper - lower) ≤ charge)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph)) :
    expect ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan))
        (monitoredSettlement settlement charge) ≤ lower := by
  apply (submission_settlement_bound settlement upper charge bounded nonnegative bit
    submission players plan).trans
  linarith

end Vegas.Examples.MonitoredGuessing
