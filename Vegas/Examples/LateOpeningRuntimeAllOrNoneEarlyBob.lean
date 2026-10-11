/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
import Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeEarlyBobInformation
  LateOpeningRuntimeEarlyBobDecision LateOpeningRuntimeEarlyBobSafeMenu
  LateOpeningRuntimeEarlyBobSafeDecision
open LateOpeningRuntimeAllOrNoneTrafficAudit (sample)
open LateOpeningRuntimeEarlyBobAudit LateOpeningRuntimeBobSafeContinuation
  LateOpeningRuntimeFirstRetryComparison

variable (α : ℝ) (hα : 0 ≤ α)
  (hα1 : α ≤ 1)
  (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeGame.payoff reward forfeit (sample α hα hα1)
      deposit history.state bob) (2 * LateOpeningRuntimeService.horizon + 1)

def utility (final : app.Execution) : ℝ :=
  LateOpeningRuntimeGame.payoff reward forfeit (sample α hα hα1) deposit
    (app.finished final) bob

theorem utility_bounded (final : app.Execution) :
    |utility α hα hα1 reward forfeit deposit final| ≤ 1 + |forfeit| + |deposit bob| :=
  LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (sample α hα hα1)
    deposit (app.finished final)

theorem context_integrable
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy bob) :
    Context.IntegrableAt
      (context α hα hα1 weight nonnegative site reward forfeit deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (sample α hα hα1)
      deposit history.state

theorem local_context_outcome_law
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeGame.model weight nonnegative).Choice bob site.1)) :
    ((context α hα hα1 weight nonnegative site reward forfeit deposit assessment).outcome
      (localPolicy weight nonnegative site assessment law)).map History.state =
    (finalLaw weight nonnegative site representative decision current assessment law).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  rw [current_local_continuation_law weight nonnegative site representative
      decision current,
    PMF.map_bind]

theorem local_context_value
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeGame.model weight nonnegative).Choice bob site.1)) :
    (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (localPolicy weight nonnegative site assessment law) =
    expect (finalLaw weight nonnegative site representative decision current assessment law)
      (utility α hα hα1 reward forfeit deposit) := by
  have mapped := expect_map History.state
    ((context α hα hα1 weight nonnegative site reward forfeit deposit assessment).outcome
      (localPolicy weight nonnegative site assessment law))
    (fun state => LateOpeningRuntimeGame.payoff reward forfeit (sample α hα hα1)
      deposit state bob)
  rw [local_context_outcome_law α hα hα1 weight nonnegative site representative
      decision current,
    expect_map] at mapped
  exact mapped.symm

theorem incumbent_context_value
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob site.1)) (utility α hα hα1 reward forfeit deposit) := by
  have result := local_context_value α hα hα1 weight nonnegative site representative
    decision current reward forfeit deposit assessment (assessment.strategy bob site.1)
  simpa only [localPolicy, InformationModel.BehavioralPolicy.withLaw_eq_self] using result

def responseValue
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) : ℝ :=
  expect ((assessment.belief bob site).bind fun history =>
    continuation weight nonnegative site representative decision current assessment history
      response)
    (utility α hα hα1 reward forfeit deposit)

theorem local_context_value_response
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeGame.model weight nonnegative).Choice bob site.1)) :
    (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (localPolicy weight nonnegative site assessment law) =
    expect (responseLaw weight nonnegative site law)
      (responseValue α hα hα1 weight nonnegative site representative decision current
        reward forfeit deposit assessment) := by
  rw [local_context_value α hα hα1 weight nonnegative site representative
      decision current,
    finalLaw_response_first weight nonnegative site representative
      decision current]
  exact expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _
    (utility_bounded α hα hα1 reward forfeit deposit))

theorem incumbent_context_value_response
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (responseLaw weight nonnegative site (assessment.strategy bob site.1))
      (responseValue α hα hα1 weight nonnegative site representative decision current
        reward forfeit deposit assessment) := by
  have result := local_context_value_response α hα hα1 weight nonnegative site representative
    decision current reward forfeit deposit assessment (assessment.strategy bob site.1)
  simpa only [localPolicy, InformationModel.BehavioralPolicy.withLaw_eq_self] using result

theorem quiet_context_value
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (quietPolicy weight nonnegative site representative decision current assessment) =
    responseValue α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment ⟨none⟩ := by
  rw [quietPolicy, local_context_value_response α hα hα1 weight nonnegative site representative
    decision current]
  simp only [responseLaw, PMF.pure_map, quietChoice, Option.getD_some, expect_pure]

theorem rejected_responseValue_bound
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) (submitted : response.transmission.isSome) :
    responseValue α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment response ≤ 1 - α * deposit bob := by
  apply expect_le_const _ _ (payoffIntegrable_of_bounded _ _
    (utility_bounded α hα hα1 reward forfeit deposit))
  intro final reached
  obtain ⟨history, _, sampled⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  obtain ⟨submission, sent⟩ := Option.isSome_iff_exists.mp submitted
  have responseEq : response = ⟨some submission⟩ := by cases response; cases sent; rfl
  have upper := early_submission_continuation_utility_bound (reward := reward)
    forfeitNonnegative
    (fun owner => α * deposit owner)
    (mul_nonneg hα depositNonnegative)
    weight nonnegative recovered.execution recovered.trace submission recovered.unresolved
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) final
      (by simpa only [continuation, responseEq] using sampled)
  apply le_trans ?_ upper
  change LateOpeningRuntimeGame.payoff _ _ _ _ (some ⟨0, none, final⟩) bob ≤ _
  rw [LateOpeningRuntimeAllOrNoneTrafficAudit.payoff]
  apply sub_le_self
  split
  · exact mul_nonneg (sub_nonneg.mpr hα1) depositNonnegative
  · exact le_rfl

theorem safe_context_outcome_law
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    ((context α hα hα1 weight nonnegative site reward forfeit deposit assessment).outcome
      (safeFinitePolicy weight nonnegative)).map History.state =
    (safeFinalLaw weight nonnegative site representative decision current assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, safeFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  exact safe_current_continuation_law weight nonnegative site representative decision current
    assessment history

theorem safe_context_value
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (safeFinitePolicy weight nonnegative) =
    expect (safeFinalLaw weight nonnegative site representative decision current assessment)
      (utility α hα hα1 reward forfeit deposit) := by
  have mapped := expect_map History.state
    ((context α hα hα1 weight nonnegative site reward forfeit deposit assessment).outcome
      (safeFinitePolicy weight nonnegative))
    (fun state => LateOpeningRuntimeGame.payoff reward forfeit (sample α hα hα1)
      deposit state bob)
  rw [safe_context_outcome_law α hα hα1 weight nonnegative site representative
      decision current,
    expect_map] at mapped
  exact mapped.symm

include representative decision current in
theorem safe_context_nonnegative
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    0 ≤ (context α hα hα1 weight nonnegative site reward forfeit deposit assessment).value
      (safeFinitePolicy weight nonnegative) := by
  rw [safe_context_value α hα hα1 weight nonnegative site representative
      decision current]
  apply expect_nonneg
  intro final reached
  obtain ⟨history, _, sampled⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  exact safe_continuation_nonnegative weight nonnegative
    (safePlayers weight nonnegative assessment) (by simp only [safePlayers, Function.update_self])
    recovered.execution final recovered.trace recovered.emptyRecall recovered.unresolved
    reward forfeit deposit (sample α hα hα1)
    (by
      intro actual observed supported
      exact LateOpeningRuntimeAllOrNoneTrafficAudit.sample_authentic α
        hα hα1 actual observed supported) sampled

theorem responseValue_integrable
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment) :
    PayoffIntegrable
      (responseLaw weight nonnegative site (assessment.strategy bob site.1))
      (responseValue α hα hα1 weight nonnegative site representative decision current
        reward forfeit deposit assessment) := by
  exact payoffIntegrable_expect_of_bounded _ _ _
    (by positivity : 0 ≤ 1 + |forfeit| + |deposit bob|)
    (utility_bounded α hα hα1 reward forfeit deposit)

theorem quiet_responseValue_bound
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) (quiet : ¬ response.transmission.isSome) :
    responseValue α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment response ≤
    responseValue α hα hα1 weight nonnegative site representative decision current
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
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < α * deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context α hα hα1 weight nonnegative site reward forfeit deposit assessment)) :
    ((responseLaw weight nonnegative site (assessment.strategy bob site.1)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable α hα hα1 weight nonnegative site reward forfeit deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable α hα hα1 weight nonnegative site reward forfeit deposit
      assessment alternative)).mp rational
  apply eventProbability_zero_of_two_value_comparisons
    (responseLaw weight nonnegative site (assessment.strategy bob site.1))
    (responseValue α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment) {response | response.transmission.isSome}
    (responseValue α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment ⟨none⟩) (α * deposit bob - 1)
    (responseValue_integrable α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment)
  · intro response _ costly
    have bound := rejected_responseValue_bound α hα hα1 weight nonnegative site representative
      decision current reward forfeit deposit forfeitNonnegative (by
        have : 0 < deposit bob := by
          by_contra notPositive
          have nonpositive := mul_nonpos_of_nonneg_of_nonpos hα
            (le_of_not_gt notPositive)
          linarith
        exact this.le) assessment response costly
    linarith
  · intro response _ quiet
    exact quiet_responseValue_bound α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment response quiet
  · rw [← incumbent_context_value_response α hα hα1 weight nonnegative site representative
      decision current,
      ← quiet_context_value α hα hα1 weight nonnegative site representative
      decision current]
    exact comparison
      (quietPolicy weight nonnegative site representative decision current assessment)
      (Set.mem_univ _)
  · rw [← incumbent_context_value_response α hα hα1 weight nonnegative site representative
      decision current]
    exact (safe_context_nonnegative α hα hα1 weight nonnegative site representative decision current
      reward forfeit deposit assessment).trans
      (comparison (safeFinitePolicy weight nonnegative) (Set.mem_univ _))
  · linarith

include representative decision current in
theorem sequentially_rational_early_packet_zero
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < α * deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample α hα hα1) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy bob site.1)).toOuterMeasure
      {response | response.transmission.isSome}).toReal = 0 := by
  apply rational_early_packet_zero α hα hα1 weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative collateral assessment
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

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
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < α * deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample α hα hα1) deposit history.state who)) :
    responseLaw weight nonnegative site (assessment.strategy bob site.1) = PMF.pure ⟨none⟩ :=
  pure_quiet_of_packet_zero _
    (sequentially_rational_early_packet_zero α hα hα1 weight nonnegative site representative
      decision current reward forfeit deposit forfeitNonnegative collateral assessment rational)

open LateOpeningRuntimeEarlyResponseLaw

theorem sequentially_rational_response_law (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < α * deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample α hα hα1) deposit history.state who))
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (possible : slot = 0 ∨ seen = false) :
    players weight nonnegative assessment.strategy bob
      ((observed bit label slot seen).recall bob)
      ((observed bit label slot seen).observe app bob) = PMF.pure ⟨none⟩ := by
  obtain ⟨site, history, current⟩ := information_representative weight nonnegative bit label
    slot seen possible
  let actual := LateOpeningRuntimeEarlyResponseLaw.decision
    weight nonnegative bit label slot seen possible
  have silent := sequentially_rational_early_response_law
    α hα hα1 weight nonnegative site history actual current reward forfeit deposit
    forfeitNonnegative
      collateral assessment rational
  have info := LateOpeningRuntimeEarlyBobDecision.site_information
    weight nonnegative site history actual current
  unfold LateOpeningRuntimeEarlyBobDecision.responseLaw at silent
  rw [info] at silent
  simpa only [players, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def,
    actual, LateOpeningRuntimeEarlyResponseLaw.decision] using silent

theorem sequentially_rational_responses_silent (reward forfeit : ℝ)
    (deposit : Player → ℝ) (forfeitNonnegative : 0 ≤ forfeit)
    (collateral : 1 < α * deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeGame.payoff reward forfeit
        (sample α hα hα1) deposit history.state who)) :
    LateOpeningRuntimeEarlyResponseLaw.ResponsesSilent
      weight nonnegative assessment.strategy := by
  intro bit label slot seen possible
  exact sequentially_rational_response_law α hα hα1 weight nonnegative reward forfeit
    deposit forfeitNonnegative collateral assessment rational bit label slot seen possible

end Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob
