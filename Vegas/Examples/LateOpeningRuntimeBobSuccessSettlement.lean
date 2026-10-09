/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization

/-! # Clean settlement at optimal successful-publication bindings

Equality in the actual logical-score ceiling holds at every belief-supported
hidden history and supported physical continuation of a maximizing response.
A positive publication forfeit therefore excludes failed final publication;
positive collateral forces zero terminal audit charge. Hidden histories with
zero assessed belief are not included in these support conclusions.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSuccessDecision LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeBobSuccessOptimization LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobRawBinding (serviced continuation_split)
open LateOpeningRuntimeBobBindingDecision (context context_integrable)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

def conditionalValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ℝ :=
  expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 14
    ((decisionOfInformation weight nonnegative site representative decision current
      history).execution.respond app bob response)) fun final =>
        LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) bob

def conditionalScore (response : app.Action)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ℝ :=
  bindingScore (originalLabel (decisionOfInformation weight nonnegative site representative decision
    current history).execution)
      ((serviced decision.execution response).application.config.store (.inr bobBindEvent))


theorem conditionalValue_le_score (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    conditionalValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response history ≤ conditionalScore weight nonnegative site representative decision
        current response history := by
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
  intro final reached
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have same := response_result_same_information weight nonnegative decision _ compatible.2.1
    compatible.2.2 response
  have upper := continuation_payoff_le_score weight nonnegative _ response _ final reached
    reward forfeit forfeitNonnegative deposit depositNonnegative (fun actual => PMF.pure actual)
  rwa [← same] at upper

/-- The nonnegative loss below the selected logical score has zero mean at
every supported maximizing response, and hence vanishes on actual belief support. -/
theorem rational_conditional_value_eq_score (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    ∀ history ∈ (assessment.belief bob site).support,
      conditionalValue weight nonnegative site representative decision current reward forfeit
        deposit assessment response history =
      conditionalScore weight nonnegative site representative decision current response
        history := by
  let value := conditionalValue weight nonnegative site representative decision current reward
    forfeit deposit assessment response
  let score := conditionalScore weight nonnegative site representative decision current response
  have valueIntegrable : PayoffIntegrable (assessment.belief bob site) value :=
    payoffIntegrable_of_bounded _ _ fun history =>
      expect_abs_le_of_bounded (show 0 ≤ 1 + |forfeit| + |deposit bob| by positivity)
        (fun final => LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit
          (fun actual => PMF.pure actual) deposit (app.finished final))
  have scoreIntegrable : PayoffIntegrable (assessment.belief bob site) score :=
    payoffIntegrable_of_bounded _ _ fun history => bindingScore_abs_le_one _ _
  have selectedValue := rational_supported_response_value weight nonnegative site representative
    decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment
      rational
      response supported
  have selectedScore : expect (assessment.belief bob site) score =
      bestAnswerValue weight nonnegative site reward forfeit deposit assessment := by
    apply le_antisymm (response_score_value_le_bestAnswerValue weight nonnegative site
      representative decision current reward forfeit deposit assessment response)
    rw [← selectedValue]
    exact responseValue_le_scoreValue weight nonnegative site representative decision current reward
      forfeit deposit forfeitNonnegative depositNonnegative assessment response
  have gapMean :
      expect (assessment.belief bob site) (fun history => value history - score history) = 0 := by
    rw [expect_sub valueIntegrable scoreIntegrable, selectedScore]
    change responseValue weight nonnegative site representative decision current reward forfeit
      deposit assessment response - _ = 0
    rw [selectedValue, sub_self]
  have equal := expect_eq_const_of_le_on_support (assessment.belief bob site)
    (fun history => value history - score history) 0
      (payoffIntegrable_sub valueIntegrable scoreIntegrable)
      (fun history _ => sub_nonpos.mpr (conditionalValue_le_score weight nonnegative site
        representative decision current reward forfeit deposit forfeitNonnegative depositNonnegative
          assessment response history)) gapMean
  intro history reached
  exact sub_eq_zero.mp (equal history reached)

/-- Saturation reaches every physical branch of every hidden history to
which the actual assessment assigns positive belief. -/
theorem rational_supported_payoff_eq_score (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (believed : history ∈ (assessment.belief bob site).support) :
    ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 14
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob response)).support,
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
        (app.finished final) bob =
          conditionalScore weight nonnegative site representative decision current response
            history := by
  apply expect_eq_const_of_le_on_support _ _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
  · intro final reached
    have compatible := decisionOfInformation_spec weight nonnegative site representative decision
      current history
    have same := response_result_same_information weight nonnegative decision _ compatible.2.1
      compatible.2.2 response
    have upper := continuation_payoff_le_score weight nonnegative _ response _ final reached
      reward forfeit forfeitNonnegative deposit depositNonnegative (fun actual => PMF.pure actual)
    rwa [← same] at upper
  · exact rational_conditional_value_eq_score weight nonnegative site representative decision
      current
      reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational response
        supported history believed

omit site representative decision current in
/-- Equality with a successfully selected logical score forces publication
and zero charge when the forfeit and collateral are positive. -/
theorem score_saturation_settles_clean (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) (answer : Answer)
    (selected : (serviced decision.execution response).application.config.store
      (.inr bobBindEvent) = some (.success answer))
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (decision.execution.respond app bob response)).support)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (saturated : LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final) bob =
      bindingScore (originalLabel decision.execution)
        ((serviced decision.execution response).application.config.store (.inr bobBindEvent))) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          (app.finished final) bob = 0 := by
  obtain ⟨bit, label, binding, publication, bitEq, labelEq, reachable, bound, published, readout⟩ :=
    LateOpeningRuntimeBobSuccessPayoff.continuation_readout weight nonnegative decision response
      players final reached
  have charged := TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (app.finished final) bob
  have deduction := mul_nonneg charged.1 depositPositive.le
  have nonnegativeScore := bindingScore_nonnegative (originalLabel decision.execution)
    ((serviced decision.execution response).application.config.store (.inr bobBindEvent))
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility at saturated
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout bob] at saturated
  cases publication with
  | failure =>
      rw [sourceUtility_bob_failure] at saturated
      linarith
  | success opened =>
      have splitReach := reached
      rw [continuation_split weight nonnegative _ decision.trace decision.quiet] at splitReach
      have retained := (ReactiveApplication.Invariant.policyInvariant app
        (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
          (.inr bobBindEvent) (.success answer : PublicationResult Answer)) players).runRounds
            (LateOpeningRuntimeService.scheduler weight nonnegative) 13 _ final selected splitReach
      have actualBound := bob_success_from_binding final.application _ reachable opened published
      have same : opened = answer := by
        have equality := Option.some.inj (actualBound.symm.trans retained)
        exact PublicationResult.success.inj equality
      subst opened
      refine ⟨published, ?_⟩
      rw [sourceUtility_bob_after_alice_success, labelEq, selected] at saturated
      change answerScore label answer - TerminalAudit.charge _ _ _ bob * deposit bob =
        answerScore label answer at saturated
      have zero : TerminalAudit.charge
          (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
            (app.finished final) bob * deposit bob = 0 := by linarith
      exact (mul_eq_zero.mp zero).resolve_right (ne_of_gt depositPositive)

/-- Optimal bindings after successful Alice publication settle the same
maximizing Safe or label answer with zero Bob charge on actual joint support. -/
theorem rational_supported_clean_settlement (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    ∃ answer : Answer,
      (serviced decision.execution response).application.config.store (.inr bobBindEvent) =
        some (.success answer) ∧
      (answer = safe ∨ ∃ label : Fin 3, answer = labelGuess label) ∧
      (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative answer) =
          bestAnswerValue weight nonnegative site reward forfeit deposit assessment ∧
      ∀ history ∈ (assessment.belief bob site).support,
        ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 14
          ((decisionOfInformation weight nonnegative site representative decision current
            history).execution.respond app bob response)).support,
          final.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
            TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
              (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
                (app.finished final) bob = 0 := by
  obtain ⟨answer, selected, shape, maximizing⟩ := rational_supported_binding weight nonnegative site
    representative decision current reward forfeit deposit forfeitPositive.le depositPositive.le
      assessment rational response supported
  refine ⟨answer, selected, shape, maximizing, ?_⟩
  intro history believed final reached
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have same := response_result_same_information weight nonnegative decision _ compatible.2.1
    compatible.2.2 response
  have selectedHere := same.symm.trans selected
  have saturated := rational_supported_payoff_eq_score weight nonnegative site representative
    decision current reward forfeit deposit forfeitPositive.le depositPositive.le assessment
      rational response supported history believed final reached
  unfold conditionalScore at saturated
  rw [same] at saturated
  exact score_saturation_settles_clean weight nonnegative reward forfeit deposit _ response _
    answer selectedHere final reached forfeitPositive depositPositive saturated

end Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement
