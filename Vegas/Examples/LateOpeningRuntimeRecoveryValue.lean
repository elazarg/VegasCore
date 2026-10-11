/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation
import Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation
import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation

/-! # Actual late-opening values against the original Safe receiver

The full native lottery retains rejection and audit deductions. No equilibrium
or source-law preservation premise is used to evaluate this continuation.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeRecoveryValue
open Interaction GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeSettlementContinuation
  LateOpeningRuntimeBobSafeContinuation LateOpeningRuntimeUtility
  LateOpeningRuntimeBobBindingService

theorem receiverCompletion_safe (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bobPolicy : players bob = safePolicy)
    (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (clock : execution.application.clock = 3)
    (supported : final ∈ (receiverCompletion weight nonnegative players execution).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success safe) := by
  have chosen := answerPolicy_binding weight nonnegative safe 14 execution trace quiet ready clock
  unfold receiverCompletion ReactiveApplication.invoke at supported
  rw [bobPolicy, safePolicy, chosen, PMF.pure_map, PMF.pure_bind] at supported
  exact (answer_continuation_clean weight nonnegative safe players bobPolicy execution final
    trace quiet ready timely (fun actual => PMF.pure actual)
    (fun actual observed positive => by
      cases (PMF.mem_support_pure_iff _ _).mp positive
      exact List.Subset.refl _) supported).1

/-- The proper opening is exactly the compiler's action at this actual view. -/
theorem reactiveDecision_late_opening (bit : Bool) (label : Fin 3) :
    LateOpeningRuntimeService.runtime.reactiveDecision leaks alice aliceEvent true
      ((secondLateDecision bit label 1 false).observe app alice).application =
        ⟨some (Vegas.EventGraphRuntime.disclosureSubmission
          (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩))⟩ := by
  change (⟨some ((Vegas.EventGraphRuntime.disclosureSubmission
    (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)).normalizeReactive alice
      ((secondLateDecision bit label 1 false).observe app alice).application [])⟩ : app.Action) = _
  congr 1
  congr 1
  apply Vegas.EventGraphRuntime.disclosureSubmission_normalize_opening
    alice _ aliceEvent aliceCandidate ⟨.bool, bit⟩ rfl
  exact (LateOpeningRuntimeAliceEmptyWitness.decisionHistory (0 : ℝ) (by norm_num)
    bit label).fixed

theorem successful_safe_payoff (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = safePolicy) (bit : Bool) (label : Fin 3)
    (slot : Fin 2) (seen : Bool) (possible : slot = 0 ∨ seen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (final : app.Execution)
    (supported : final ∈ (receiverCompletion weight nonnegative players
      (answerDecision bit label slot seen)).support) :
    LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (app.finished final) alice = reward / 2 := by
  let decision := LateOpeningRuntimeAliceSuccessfulContinuation.decisionHistory weight
    nonnegative positive bit label slot seen possible
  have clock : (answerDecision bit label slot seen).application.clock = 3 := by
    rw [answerDecision_physical]
  have published := receiverCompletion_safe weight nonnegative players bobPolicy _ final
    decision.trace decision.quiet decision.ready decision.timely clock supported
  unfold receiverCompletion ReactiveApplication.invoke at supported
  obtain ⟨middle, chosen, later⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ chosen
  have value := LateOpeningRuntimeAliceSuccessfulContinuation.continuation_payoff_of_publication
    weight nonnegative positive bit label slot seen possible response players final later safe
      published reward forfeit deposit (fun actual => PMF.pure actual)
        (fun actual observed issued => by
          cases (PMF.mem_support_pure_iff _ _).mp issued
          exact List.Subset.refl _)
  norm_num [LateOpeningRuntimeAliceSuccessfulContinuation.successfulValue, safe, answerValue]
    at value
  exact value

theorem failed_safe_payoff (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bobPolicy : players bob = safePolicy)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (possible : slot = 0 ∨ earlySeen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (final : app.Execution)
    (supported : final ∈ (receiverCompletion weight nonnegative players
      (LateOpeningRuntimeBindingObservation.failedAnswerDecision bit label slot
        earlySeen finalSeen)).support) :
    LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (app.finished final) alice = -forfeit - deposit alice := by
  let decision := LateOpeningRuntimeAliceFailureContinuation.decisionHistory weight nonnegative
    bit label slot earlySeen finalSeen possible
  have clock : decision.execution.application.clock = 3 := by
    change (LateOpeningRuntimeBindingObservation.failedAnswerDecision bit label slot
      earlySeen finalSeen).application.clock = 3
    rw [LateOpeningRuntimeBindingObservation.failedAnswerDecision_physical]
    rfl
  have published := receiverCompletion_safe weight nonnegative players bobPolicy _ final
    decision.trace decision.quiet decision.ready decision.timely clock supported
  have value := LateOpeningRuntimeAliceFailurePayoff.failed_completion_payoff weight nonnegative
    players bit label slot earlySeen finalSeen possible final supported safe published reward
      forfeit deposit
  norm_num [safe, answerValue] at value
  exact value

/-- The unchanged late lottery has an exact two-point net-payoff law against
Safe, retaining every other future policy. Omission loses both forfeit and audit collateral. -/
theorem settlement_safe_payoff_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = safePolicy) (bit : Bool) (label : Fin 3)
    (slot : Fin 2) (seen : Bool) (possible : slot = 0 ∨ seen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ) :
    (settlementCompletion weight nonnegative players (beforeLottery bit label slot seen)).map
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (reward / 2)) (PMF.pure (-forfeit - deposit alice)) := by
  let utility := fun final : app.Execution => LateOpeningRuntimeGame.payoff reward forfeit
    (fun actual => PMF.pure actual) deposit (app.finished final) alice
  have successful : (receiverCompletion weight nonnegative players
      (answerDecision bit label slot seen)).map utility = PMF.pure (reward / 2) := by
    rw [← PMF.map_const (receiverCompletion weight nonnegative players
      (answerDecision bit label slot seen)) (reward / 2)]
    apply map_congr_on_support
    intro final supported
    exact successful_safe_payoff weight nonnegative positive players bobPolicy bit label slot
      seen possible reward forfeit deposit final supported
  have failed : ∀ finalSeen, (receiverCompletion weight nonnegative players
      (LateOpeningRuntimeBindingObservation.failedAnswerDecision bit label slot seen
        finalSeen)).map utility = PMF.pure (-forfeit - deposit alice) := by
    intro finalSeen
    rw [← PMF.map_const (receiverCompletion weight nonnegative players
      (LateOpeningRuntimeBindingObservation.failedAnswerDecision bit label slot seen finalSeen))
        (-forfeit - deposit alice)]
    apply map_congr_on_support
    intro final supported
    exact failed_safe_payoff weight nonnegative players bobPolicy bit label slot seen finalSeen
      possible reward forfeit deposit final supported
  change (settlementCompletion weight nonnegative players _).map utility = _
  rw [canonical_completion_law, mix_map, mix_map, successful, failed true, failed false, mix_self]

/-- A genuine opening at the actual last Alice callback retains the full native
continuation and has the fallible builder's exact two-point net-payoff law. -/
theorem late_callback_safe_payoff_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = safePolicy) (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission) (reward forfeit : ℝ) (deposit : Player → ℝ) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice ⟨some submission⟩)).map
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (reward / 2)) (PMF.pure (-forfeit - deposit alice)) := by
  have native := genuine_final_payoff_law weight nonnegative players bit label submission genuine
    reward forfeit deposit (fun actual => PMF.pure actual) alice
  have same : LateOpeningRuntimeLateResponseKernel.finalDecision bit label ⟨none⟩ ∅ =
      secondLateDecision bit label 1 false := rfl
  rw [same] at native
  exact native.trans (settlement_safe_payoff_law weight nonnegative positive players bobPolicy
    bit label 1 false (Or.inr rfl) reward forfeit deposit)

/-- Exact value of the genuine native opening: inclusion earns the Safe source
reward, while omission forfeits the source payment and the authentic audit deposit. -/
theorem late_callback_safe_value (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = safePolicy) (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission) (reward forfeit : ℝ) (deposit : Player → ℝ) :
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice ⟨some submission⟩))
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      inclusionProbability weight * (reward / 2) -
        (1 - inclusionProbability weight) * (forfeit + deposit alice) := by
  have law := late_callback_safe_payoff_law weight nonnegative positive players bobPolicy bit label
    submission genuine reward forfeit deposit
  have value := congrArg (fun distribution : PMF ℝ => expect distribution id) law
  rw [expect_map, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _)
    (payoffIntegrable_pure _ _), expect_pure, expect_pure] at value
  simp only [Function.comp_def, id_eq] at value
  exact value.trans (by ring)

/-- Fallible late inclusion refutes exact source-value correspondence at a
genuine ready timely callback, without any equilibrium or preservation premise. -/
theorem late_callback_safe_value_lt_source (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = safePolicy) (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (lossNonnegative : 0 ≤ forfeit + deposit alice) :
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice ⟨some submission⟩))
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) <
      sourceUtility reward forfeit (finalState bit label true safe true) alice := by
  rw [late_callback_safe_value weight nonnegative positive players bobPolicy bit label submission
    genuine reward forfeit deposit, (sourceUtility_intended reward forfeit bit label).1]
  have below : inclusionProbability weight < 1 :=
    MessageNetwork.inclusionMass_below_one weight nonnegative 1
  have rewardLoss : 0 < (1 - inclusionProbability weight) * (reward / 2) :=
    mul_pos (sub_pos.mpr below) (by linarith)
  have auditLoss : 0 ≤ (1 - inclusionProbability weight) * (forfeit + deposit alice) :=
    mul_nonneg (sub_nonneg.mpr below.le) lossNonnegative
  nlinarith

/-- The canonical proper opening at the genuine legal last callback has strictly
less expected net payoff than the original successful-opening source run.
The existing service contract and timeliness hold for this unchanged scheduler;
they protect the first opportunity, not an arbitrary later response. -/
theorem late_compiler_action_value_lt_source (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) (players : Player → app.Policy)
    (bobPolicy : players bob = safePolicy) (bit : Bool) (label : Fin 3)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardPositive : 0 < reward) (lossNonnegative : 0 ≤ forfeit + deposit alice) :
    expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
      ((secondLateDecision bit label 1 false).respond app alice
        (LateOpeningRuntimeService.runtime.reactiveDecision leaks alice aliceEvent true
          ((secondLateDecision bit label 1 false).observe app alice).application)))
      (fun final => LateOpeningRuntimeGame.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit (app.finished final) alice) <
      expect (SourceProgram.run program intendedProfile (sourceInitial bit label))
        (fun final => sourceUtility reward forfeit final alice) := by
  rw [reactiveDecision_late_opening, intendedProfile, run_constant, expect_pure]
  apply late_callback_safe_value_lt_source weight nonnegative positive players bobPolicy
    bit label _ _ reward forfeit deposit rewardPositive lossNonnegative
  exact LateOpeningRuntimeAliceOpeningContinuation.canonical_emits_opening weight nonnegative
    (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)

end Vegas.Examples.LateOpeningRuntimeRecoveryValue
