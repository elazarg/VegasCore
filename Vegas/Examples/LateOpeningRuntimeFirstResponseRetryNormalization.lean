/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation

/-! # Exact native retry normalization after counterfactual first responses

Positive retry margin makes the quiet-retry comparison exact after every
available first raw response, including genuine private aliases that the
original first law assigns probability zero. The comparison retains the
original early receiver response and every other original continuation.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeFirstSettlementContinuation
  LateOpeningRuntimeSettlementContinuation LateOpeningRuntimeLatePrefixKernel

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
  (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
  (marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin weight reward forfeit deposit)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
  (rational : assessment.IsSequentiallyRational
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit history.state who))

include rational positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive in
theorem rational_response_prefix_law (bit : Bool) (label : Fin 3) (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    firstBindingLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response (players weight nonnegative assessment.strategy) =
      firstComparison weight nonnegative assessment.strategy bit label response := by
  have bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative assessment.strategy actual.1 ≤ 0 := by
    intro actual
    obtain ⟨decision, history, current⟩ := actual.2
    have zero := LateOpeningRuntimeAliceRationality.sequentially_rational_second_packet_zero
      weight nonnegative actual.1 history decision current reward forfeit deposit positive
        rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational
    exact zero.le
  have close := response_comparison_close weight nonnegative assessment.strategy bit label
    0 (le_refl _) bound response available
  exact (show PMF.WithinTV 0 _ _ by simpa only [ite_self] using close).eq_of_zero

include rational positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive in
theorem rational_response_completion_law (bit : Bool) (label : Fin 3) (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response (players weight nonnegative assessment.strategy) =
      (firstComparison weight nonnegative assessment.strategy bit label response).bind
        (receiverCompletion weight nonnegative
          (players weight nonnegative assessment.strategy)) := by
  rw [response_completion_law, rational_response_prefix_law weight nonnegative reward forfeit
    deposit positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive
      assessment rational bit label response available]

end Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization
