/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobSafeDecision
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Native sequential rationality before Alice's publication settles

A premature Bob packet is actually rejected and fully audited. Silence with
the incumbent future policy and the available quiet/Safe/open policy give two
genuine whole-policy comparisons. With collateral above Bob's maximum gross
payoff, sequential rationality forces silence at every first unresolved Bob
information site, under its own arbitrary belief. No clean-support premise,
posterior premise or target-to-source preservation claim is imposed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyBobRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeEarlyBobInformation
  LateOpeningRuntimeEarlyBobDecision LateOpeningRuntimeEarlyBobSafeMenu
  LateOpeningRuntimeEarlyBobSafeDecision

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem responseValue_integrable
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PayoffIntegrable
      (responseLaw weight nonnegative site (assessment.strategy bob site.1))
      (responseValue weight nonnegative site representative decision current
        reward forfeit deposit assessment) := by
  exact payoffIntegrable_expect_of_bounded _ _ _
    (by positivity : 0 ≤ 1 + |forfeit| + |deposit bob|)
    (utility_bounded reward forfeit deposit)

theorem quiet_responseValue_bound
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) (quiet : ¬ response.transmission.isSome) :
    responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment response ≤
    responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment ⟨none⟩ := by
  have same : response = ⟨none⟩ := by
    cases response with
    | mk transmission =>
      cases transmission with
      | none => rfl
      | some submission => cases quiet rfl
  rw [same]

include representative decision current in
/-- The exact native whole-policy comparisons eliminate every premature
raw packet, even at information sites reached only by previous deviations. -/
theorem rational_early_packet_zero
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ((responseLaw weight nonnegative site (assessment.strategy bob site.1)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  apply eventProbability_zero_of_two_value_comparisons
    (responseLaw weight nonnegative site (assessment.strategy bob site.1))
    (responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment) {response | response.transmission.isSome}
    (responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment ⟨none⟩) (deposit bob - 1)
    (responseValue_integrable weight nonnegative site representative decision current
      reward forfeit deposit assessment)
  · intro response _ costly
    have bound := rejected_responseValue_bound weight nonnegative site representative decision
      current reward forfeit deposit forfeitNonnegative (by linarith) assessment response costly
    linarith
  · intro response _ quiet
    exact quiet_responseValue_bound weight nonnegative site representative decision current
      reward forfeit deposit assessment response quiet
  · rw [← incumbent_context_value_response weight nonnegative site representative decision current,
      ← quiet_context_value weight nonnegative site representative decision current]
    exact comparison
      (quietPolicy weight nonnegative site representative decision current assessment)
      (Set.mem_univ _)
  · rw [← incumbent_context_value_response weight nonnegative site representative decision current]
    exact (safe_context_nonnegative weight nonnegative site representative decision current
      reward forfeit deposit assessment).trans
      (comparison (safeFinitePolicy weight nonnegative) (Set.mem_univ _))
  · linarith

include representative decision current in
theorem sequentially_rational_early_packet_zero
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy bob site.1)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 := by
  apply rational_early_packet_zero weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative collateral assessment
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

include representative decision current in
/-- Every sequential equilibrium of the actual bounded raw runtime stays
quiet before the earlier publication settles when the full audit exceeds one. -/
theorem equilibrium_early_packet_zero
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy bob site.1)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 :=
  sequentially_rational_early_packet_zero weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative collateral assessment equilibrium.1

private theorem pure_quiet_of_packet_zero (law : PMF app.Action)
    (zero : (law.toOuterMeasure {response | response.transmission.isSome}).toReal = 0) :
    law = PMF.pure ⟨none⟩ := by
  have null : law.toOuterMeasure {response | response.transmission.isSome} = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp zero).resolve_right (outerMeasure_ne_top _ _)
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  have quiet : ¬ response.transmission.isSome := by
    intro costly
    exact (ne_of_gt (outerMeasure_pos_of_mem_support response costly supported)) null
  have same : response = ⟨none⟩ := by
    cases response with
    | mk transmission =>
      cases transmission with
      | none => rfl
      | some submission => cases quiet rfl
  exact Set.mem_singleton_iff.mpr same

include representative decision current in
/-- The complete native response law is the pure silent action, which can
be reused directly in later physical-prefix and belief calculations. -/
theorem sequentially_rational_early_response_law
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    responseLaw weight nonnegative site (assessment.strategy bob site.1) = PMF.pure ⟨none⟩ :=
  pure_quiet_of_packet_zero _
    (sequentially_rational_early_packet_zero weight nonnegative site representative decision current
      reward forfeit deposit forfeitNonnegative collateral assessment rational)

include representative decision current in
/-- Every actual native sequential equilibrium has the same pure silent
response law at an early unresolved-publication class. -/
theorem equilibrium_early_response_law
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    responseLaw weight nonnegative site (assessment.strategy bob site.1) = PMF.pure ⟨none⟩ :=
  sequentially_rational_early_response_law weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative collateral assessment equilibrium.1

/-- Equal error bounds for the two actual deviations give the sharp
epsilon divided by collateral-minus-one premature-packet probability bound. -/
theorem early_packet_le_of_deviation_regrets
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (epsilon : ℝ)
    (quietRegret : (context weight nonnegative site reward forfeit deposit assessment).value
        (quietPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy bob) ≤ epsilon)
    (safeRegret : (context weight nonnegative site reward forfeit deposit assessment).value
        (safeFinitePolicy weight nonnegative) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy bob) ≤ epsilon) :
    ((responseLaw weight nonnegative site (assessment.strategy bob site.1)).toOuterMeasure
      {response | response.transmission.isSome}).toReal ≤ epsilon / (deposit bob - 1) := by
  have bound := eventProbability_le_of_two_value_comparisons
    (responseLaw weight nonnegative site (assessment.strategy bob site.1))
    (responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment) {response | response.transmission.isSome}
    (responseValue weight nonnegative site representative decision current
      reward forfeit deposit assessment ⟨none⟩) (deposit bob - 1) epsilon epsilon
    (responseValue_integrable weight nonnegative site representative decision current
      reward forfeit deposit assessment)
    (fun response _ costly => by
      have bound := rejected_responseValue_bound weight nonnegative site representative decision
        current reward forfeit deposit forfeitNonnegative (by linarith) assessment response costly
      linarith)
    (fun response _ quiet => quiet_responseValue_bound weight nonnegative site representative
      decision current reward forfeit deposit assessment response quiet)
    (by
      rw [← incumbent_context_value_response weight nonnegative site representative decision
          current,
        ← quiet_context_value weight nonnegative site representative decision current]
      exact quietRegret)
    (by
      rw [← incumbent_context_value_response weight nonnegative site representative decision
          current]
      linarith [safe_context_nonnegative weight nonnegative site representative decision current
        reward forfeit deposit assessment])
    (by linarith)
  simpa only [add_sub_cancel_right] using bound

end Vegas.Examples.LateOpeningRuntimeEarlyBobRationality
