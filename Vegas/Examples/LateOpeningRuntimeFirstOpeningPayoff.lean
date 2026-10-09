/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization
import Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw

/-! # Complete native payoff law of a genuine first late opening

A globally rational profile is silent at both early receiver samples and
does not retry a genuine pending first opening. Every available genuine
first-submission representation therefore gives exactly the fair mixture
of the two canonical original receiver continuations. The current first
response may have zero probability under the assessed policy.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstOpeningPayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLateResponseKernel
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeSettlementContinuation
  LateOpeningRuntimeBindingObservation LateOpeningRuntimeSeenLikelihood

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem quiet_retry_payoff_law (policy : Player → app.Policy) (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool)
    (reward forfeit : ℝ) (deposit : Player → ℝ) :
    ((quietRetry weight nonnegative bit label submission seen).bind
      (receiverCompletion weight nonnegative policy)).map
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) alice) =
      (settlementCompletion weight nonnegative policy (beforeLottery bit label 0 seen)).map
        (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) alice) := by
  have law := genuine_first_payoff_law weight nonnegative policy bit label submission
    genuine seen reward forfeit deposit (fun actual => PMF.pure actual) alice
  rw [whole_suffix_law weight nonnegative policy _ (by
    change (finalDecision bit label ⟨some submission⟩
      (if seen then {(alice, 0)} else ∅)).environmentRecall.length = 8
    exact final_cursor bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅))] at law
  simpa only [settlementCompletion, quietRetry] using law

variable (reward forfeit : ℝ) (deposit : Player → ℝ)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
  (rational : assessment.IsSequentiallyRational
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit history.state who))

include rational in
theorem early_comparison_law (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    earlyComparison weight nonnegative assessment.strategy bit label submission seen =
      quietRetry weight nonnegative bit label submission seen := by
  have canonicalQuiet := LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral assessment rational
      bit label 0 seen (Or.inl rfl)
  have actualQuiet : players weight nonnegative assessment.strategy bob
      ((earlyObserved bit label submission seen).recall bob)
      ((earlyObserved bit label submission seen).observe app bob) = PMF.pure ⟨none⟩ := by
    change players weight nonnegative assessment.strategy bob
      (bobInformation (earlyObserved bit label submission seen)).1
      (bobInformation (earlyObserved bit label submission seen)).2 = _
    rw [genuine_early_information weight nonnegative bit label submission genuine seen]
    exact canonicalQuiet
  unfold earlyComparison
  dsimp only
  rw [actualQuiet, PMF.pure_bind, ite_eq_left rfl]

include rational in
theorem first_genuine_payoff_law (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (aliceDepositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit)
    (collateral : 1 < deposit bob) (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice))
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) :
    (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨some submission⟩ (players weight nonnegative assessment.strategy)).map
          (fun final => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit (app.finished final) alice) =
      mix (1 / 2) (by norm_num) (by norm_num)
        ((settlementCompletion weight nonnegative (players weight nonnegative assessment.strategy)
          (beforeLottery bit label 0 true)).map (fun final => LateOpeningRuntimeNash.payoff
            reward forfeit (fun actual => PMF.pure actual) deposit (app.finished final) alice))
        ((settlementCompletion weight nonnegative (players weight nonnegative assessment.strategy)
          (beforeLottery bit label 0 false)).map (fun final => LateOpeningRuntimeNash.payoff
            reward forfeit (fun actual => PMF.pure actual) deposit
              (app.finished final) alice)) := by
  rw [LateOpeningRuntimeFirstResponseRetryNormalization.rational_response_completion_law
    weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitNonnegative
      aliceDepositNonnegative marginPositive assessment rational bit label ⟨some submission⟩
        available]
  simp only [firstComparison, ite_eq_left genuine]
  rw [early_comparison_law weight nonnegative reward forfeit deposit assessment rational
      forfeitNonnegative collateral bit label submission genuine true,
    early_comparison_law weight nonnegative reward forfeit deposit assessment rational
      forfeitNonnegative collateral bit label submission genuine false,
    mix_bind, mix_map,
    quiet_retry_payoff_law weight nonnegative _ bit label submission genuine true,
    quiet_retry_payoff_law weight nonnegative _ bit label submission genuine false]

end Vegas.Examples.LateOpeningRuntimeFirstOpeningPayoff
