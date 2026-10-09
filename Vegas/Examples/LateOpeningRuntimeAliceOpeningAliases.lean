/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveInactiveRecall
import Vegas.Examples.LateOpeningRuntimeAliceOpeningContinuation

/-! # All genuine raw aliases of Alice's final opening

Two raw submissions that emit the genuine initialized opening have the same
physical effect. Their private remembered syntax may differ. Alice has no
further callback, and the other player retains its complete observation and
recall, so the exact projected suffix laws and terminal utility laws agree.

The audit reads authenticated traffic and the settled public record. Erasing
Alice's inactive private recall does not erase traffic, receipts, pending
packets, recipient knowledge, or any field used by the terminal payoff.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeAliceEmptyDecision
  LateOpeningRuntimeAliceOpeningContinuation LateOpeningRuntimeAliceContinuation

theorem payoff_eraseRecall (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (execution : app.Execution) (owner who : Player) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished (execution.eraseRecall app owner)) who =
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished execution) who := by
  rfl

theorem aliceUtility_eraseRecall (reward forfeit : ℝ) (deposit : Player → ℝ)
    (execution : app.Execution) :
    aliceUtility reward forfeit deposit (execution.eraseRecall app alice) =
      aliceUtility reward forfeit deposit execution := by
  rfl

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Genuine raw aliases differ only in the inactive owner's private recall. -/
theorem submitted_erasedRecall_eq (decision : DecisionHistory weight nonnegative)
    (first second : app.Submission)
    (firstGenuine : EmitsOpening weight nonnegative decision first)
    (secondGenuine : EmitsOpening weight nonnegative decision second) :
    (submitted weight nonnegative decision first).eraseRecall app alice =
      (submitted weight nonnegative decision second).eraseRecall app alice := by
  have firstUnchanged := opening_submission_unchanged weight nonnegative decision first firstGenuine
  have secondUnchanged :=
    opening_submission_unchanged weight nonnegative decision second secondGenuine
  change app.packet (app.submit decision.execution.application alice first) alice
    (decision.execution.network.known alice) first = _ at firstGenuine
  change app.packet (app.submit decision.execution.application alice second) alice
    (decision.execution.network.known alice) second = _ at secondGenuine
  rw [firstUnchanged] at firstGenuine
  rw [secondUnchanged] at secondGenuine
  simp only [submitted, ReactiveApplication.Execution.respond, firstUnchanged, secondUnchanged,
    firstGenuine, secondGenuine, ReactiveApplication.Execution.eraseRecall]
  congr 1
  funext observer
  by_cases owner : observer = alice
  · subst observer
    simp only [↓reduceIte]
  · simp only [owner, ↓reduceIte]

/-- The full remaining law agrees after removing Alice's inactive recall;
all later Bob reactions use the same original policy and complete views. -/
theorem opening_continuation_projected_eq (decision : DecisionHistory weight nonnegative)
    (first second : app.Submission)
    (firstGenuine : EmitsOpening weight nonnegative decision first)
    (secondGenuine : EmitsOpening weight nonnegative decision second)
    (players : Player → app.Policy) (count : Nat) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players count
        (submitted weight nonnegative decision first)).map
          (fun execution => execution.eraseRecall app alice) =
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players count
        (submitted weight nonnegative decision second)).map
          (fun execution => execution.eraseRecall app alice) := by
  exact app.continuation_eq_of_erasedRecall_eq
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
    (LateOpeningRuntimeAliceIncentive.alice_absent weight nonnegative) players count _ _
    (by change 8 ≤ decision.execution.environmentRecall.length
        rw [decision_cursor weight nonnegative])
    (submitted_erasedRecall_eq weight nonnegative decision first second firstGenuine secondGenuine)

/-- Exact settlement-utility law, not only an expected-value comparison. -/
theorem opening_payoff_law_eq (decision : DecisionHistory weight nonnegative)
    (first second : app.Submission)
    (firstGenuine : EmitsOpening weight nonnegative decision first)
    (secondGenuine : EmitsOpening weight nonnegative decision second)
    (players : Player → app.Policy) (count : Nat) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (who : Player) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players count
        (submitted weight nonnegative decision first)).map
          (fun execution => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
            (app.finished execution) who) =
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players count
        (submitted weight nonnegative decision second)).map
          (fun execution => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
            (app.finished execution) who) := by
  have laws := opening_continuation_projected_eq weight nonnegative decision first second
    firstGenuine secondGenuine players count
  have mapped := congrArg (fun law : PMF app.Execution => law.map
    (fun execution => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
      (app.finished execution) who)) laws
  simpa only [PMF.map_comp, Function.comp_def, payoff_eraseRecall] using mapped

theorem opening_expected_payoff_eq (decision : DecisionHistory weight nonnegative)
    (first second : app.Submission)
    (firstGenuine : EmitsOpening weight nonnegative decision first)
    (secondGenuine : EmitsOpening weight nonnegative decision second)
    (players : Player → app.Policy) (reward forfeit : ℝ) (deposit : Player → ℝ) :
    expect (openingLaw weight nonnegative decision first players)
        (aliceUtility reward forfeit deposit) =
      expect (openingLaw weight nonnegative decision second players)
        (aliceUtility reward forfeit deposit) := by
  have laws := opening_continuation_projected_eq weight nonnegative decision first second
    firstGenuine secondGenuine (quietAgainst players) 18
  have mapped := congrArg (fun law : PMF app.Execution =>
    expect law (aliceUtility reward forfeit deposit)) laws
  simpa only [openingLaw, expect_map, Function.comp_def, aliceUtility_eraseRecall] using mapped

end Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases
