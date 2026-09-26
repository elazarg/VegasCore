/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeSanctions

/-! # Native monitoring bounds for arbitrary settlement functions

The monitoring argument uses a bound on terminal settlements, not the
correctness-payoff formula. Every raw submission is covered, together with
every later raw policy and service instruction. Receipt liability persists
even when later calls fail or opening is withheld.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def monitoredSettlement (settlement : Results → ℝ) (charge : ℝ)
    (execution : nativeApp.Execution) : ℝ :=
  settlement (nativeResults execution.application.config) -
    if rejectedAlice execution.receipts then charge else 0

theorem settlement_continuation_bound (settlement : Results → ℝ) (upper charge : ℝ)
    (bounded : ∀ result, settlement result ≤ upper) (nonnegative : 0 ≤ charge)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph))
    (execution : nativeApp.Execution) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan execution).expect
      (monitoredSettlement settlement charge) ≤
        upper - if rejectedAlice execution.receipts then charge else 0 := by
  apply FinDist.expect_le_of_forall
  intro after supported
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
    ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan)).expect
        (monitoredSettlement settlement charge) ≤ upper - charge / 2 := by
  rw [FinDist.expect_bind]
  apply le_trans (FinDist.expect_mono (fun execution _ =>
    settlement_continuation_bound settlement upper charge bounded nonnegative players plan
      execution))
  rw [← FinDist.expect_map (fun execution : nativeApp.Execution =>
    rejectedAlice execution.receipts) (monitoredPrefixLaw bit (submissionAction submission))
      (fun alarm : Bool => upper - if alarm then charge else 0)]
  rw [submission_monitoring_law, FinDist.expect_mix]
  simp only [FinDist.expect_pure, ↓reduceIte, Bool.false_eq_true]
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
    ((monitoredPrefixLaw bit (submissionAction submission)).bind
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan)).expect
        (monitoredSettlement settlement charge) ≤ lower := by
  apply (submission_settlement_bound settlement upper charge bounded nonnegative bit
    submission players plan).trans
  linarith

end VegasTests.MonitoredGuessing
