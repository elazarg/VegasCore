/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization
import Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation

/-! # Exact native retry normalization after counterfactual first responses

Normalized pending responses make the quiet-retry comparison exact after every
available first raw response, including genuine private aliases that the
original first law assigns probability zero. The comparison retains the
original early receiver response and every other original continuation.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization
open LateOpeningRuntimeAliceResponseNormalization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeFirstSettlementContinuation
  LateOpeningRuntimeSettlementContinuation LateOpeningRuntimeLatePrefixKernel

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
  (normalized : PendingResponsesNormalized weight nonnegative assessment.strategy)


include normalized in
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
    have zero := normalized
      actual.1 history decision current
    exact zero.le
  have close := response_comparison_close weight nonnegative assessment.strategy bit label
    0 (le_refl _) bound response available
  exact (show PMF.WithinTV 0 _ _ by simpa only [ite_self] using close).eq_of_zero

include normalized in
theorem rational_response_completion_law (bit : Bool) (label : Fin 3) (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response (players weight nonnegative assessment.strategy) =
      (firstComparison weight nonnegative assessment.strategy bit label response).bind
        (receiverCompletion weight nonnegative
          (players weight nonnegative assessment.strategy)) := by
  rw [response_completion_law, rational_response_prefix_law
    weight nonnegative assessment normalized bit label response available]

end Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization
