/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeOptionalDecision

/-! # Payoff saturation at the optional native publication callback

Sequential rationality compares the incumbent's complete remaining policy
against the actual chosen-answer policy. Exact saturation of that deviation's
hidden-history payoff ceiling forces zero terminal audit charge and successful
publication on the assessment's joint response, belief and physical support.
No posterior formula or positive belief at every compatible history is assumed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOptionalRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeOptionalOpening
  LateOpeningRuntimeOptionalInformation LateOpeningRuntimeOptionalIncentive
  LateOpeningRuntimeOptionalDecision LateOpeningRuntimeBobSafeContinuation
  LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobBindingDecision
  (answerPlayers answerPlayers_admissible context context_integrable)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨12, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem conditionalValue_bounded
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    |conditionalValue weight nonnegative site representative decision current reward forfeit
      deposit assessment response history| ≤ 1 + |forfeit| + |deposit bob| :=
  expect_abs_le_of_bounded (by positivity) fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final)

theorem canonicalValue_bounded
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    |canonicalValue weight nonnegative site representative decision current reward forfeit
      deposit assessment history| ≤ 1 + |forfeit| + |deposit bob| :=
  expect_abs_le_of_bounded (by positivity) fun final =>
    LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final)

theorem responseValue_bounded
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    |responseValue weight nonnegative site representative decision current reward forfeit
      deposit assessment response| ≤ 1 + |forfeit| + |deposit bob| :=
  expect_abs_le_of_bounded (by positivity) fun history =>
    conditionalValue_bounded weight nonnegative site representative decision current reward forfeit
      deposit assessment response history

open Classical in
theorem payoff_audit_regret_le_canonicalValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final) bob +
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          (app.finished final) bob * deposit bob +
      (if final.application.config.store (.inr bobRevealEvent) = some .failure
        then forfeit else 0) ≤
    canonicalValue weight nonnegative site representative decision current reward forfeit deposit
      assessment history := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have future : answerPlayers weight nonnegative assessment decision.answer bob =
      answerPolicy recovered.answer := by
    simp only [answerPlayers, Function.update_self]
    exact congrArg answerPolicy compatible.2.2.2
  have averaged := expect_mono (fun canonicalFinal canonicalReached =>
    canonical_audit_regret weight nonnegative recovered reward forfeit
      (fun actual => PMF.pure actual) (by
        intro actual observed sampled
        cases (PMF.mem_support_pure_iff _ _).mp sampled
        exact List.Subset.refl _)
      deposit response players (answerPlayers weight nonnegative assessment decision.answer)
      future final canonicalFinal reached canonicalReached)
    (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _ fun terminal =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished terminal))
  simpa only [expect_constant, canonicalValue, recovered] using averaged

theorem payoff_le_canonicalValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (app.finished final) bob ≤
    canonicalValue weight nonnegative site representative decision current reward forfeit deposit
      assessment history := by
  classical
  have comparison := payoff_audit_regret_le_canonicalValue weight nonnegative site representative
    decision current reward forfeit deposit assessment history response players final reached
  have auditNonnegative := mul_nonneg (TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
    (app.finished final) bob).1 depositNonnegative
  have failureNonnegative : 0 ≤ if final.application.config.store (.inr bobRevealEvent) =
      some .failure then forfeit else 0 := by split_ifs <;> positivity
  linarith

theorem conditionalValue_le_canonicalValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    conditionalValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response history ≤
    canonicalValue weight nonnegative site representative decision current reward forfeit deposit
      assessment history := by
  apply expect_le_const _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
  intro final reached
  exact payoff_le_canonicalValue weight nonnegative site representative decision current reward
    forfeit deposit forfeitNonnegative depositNonnegative assessment history response _ final
      reached

theorem responseValue_le_canonical_mean (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) :
    responseValue weight nonnegative site representative decision current reward forfeit deposit
      assessment response ≤
    expect (assessment.belief bob site) (canonicalValue weight nonnegative site representative
      decision current reward forfeit deposit assessment) := by
  apply expect_mono (fun history _ => conditionalValue_le_canonicalValue weight nonnegative site
    representative decision current reward forfeit deposit forfeitNonnegative depositNonnegative
      assessment response history)
    (payoffIntegrable_of_bounded _ _ fun history =>
      conditionalValue_bounded weight nonnegative site representative decision current reward
        forfeit deposit assessment response history)
    (payoffIntegrable_of_bounded _ _ fun history =>
      canonicalValue_bounded weight nonnegative site representative decision current reward forfeit
        deposit assessment history)

include representative decision current in
theorem rational_value_eq_canonical_mean (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
    expect (assessment.belief bob site) (canonicalValue weight nonnegative site representative
      decision current reward forfeit deposit assessment) := by
  apply le_antisymm
  · rw [incumbent_value_eq_response_average weight nonnegative site representative decision current]
    apply expect_le_const _ _
      (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
        representative decision current reward forfeit deposit assessment response)
    intro response _
    exact responseValue_le_canonical_mean weight nonnegative site representative decision current
      reward forfeit deposit forfeitNonnegative depositNonnegative assessment response
  · have comparison := (Context.isLocallyOptimal_iff_of_integrable
      (context_integrable weight nonnegative site reward forfeit deposit assessment
        (assessment.strategy bob))
      (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
        assessment alternative)).mp rational
          (answerFinitePolicy weight nonnegative decision.answer) (Set.mem_univ _)
    rwa [canonical_context_value weight nonnegative site representative decision current]
      at comparison

theorem rational_supported_response_value (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ∀ response ∈ (currentResponses weight nonnegative decision assessment).support,
      responseValue weight nonnegative site representative decision current reward forfeit deposit
        assessment response =
      expect (assessment.belief bob site) (canonicalValue weight nonnegative site representative
        decision current reward forfeit deposit assessment) := by
  apply expect_eq_const_of_le_on_support _ _ _
    (payoffIntegrable_of_bounded _ _ fun response => responseValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment response)
    (fun response _ => responseValue_le_canonical_mean weight nonnegative site representative
      decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment
        response)
  rw [← incumbent_value_eq_response_average weight nonnegative site representative decision current]
  exact rational_value_eq_canonical_mean weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational

theorem rational_conditional_value_eq_canonicalValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    ∀ history ∈ (assessment.belief bob site).support,
      conditionalValue weight nonnegative site representative decision current reward forfeit
        deposit assessment response history =
      canonicalValue weight nonnegative site representative decision current reward forfeit
        deposit assessment history := by
  let value := conditionalValue weight nonnegative site representative decision current reward
    forfeit deposit assessment response
  let ceiling := canonicalValue weight nonnegative site representative decision current reward
    forfeit deposit assessment
  have valueIntegrable : PayoffIntegrable (assessment.belief bob site) value :=
    payoffIntegrable_of_bounded _ _ fun history => conditionalValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment response history
  have ceilingIntegrable : PayoffIntegrable (assessment.belief bob site) ceiling :=
    payoffIntegrable_of_bounded _ _ fun history => canonicalValue_bounded weight nonnegative site
      representative decision current reward forfeit deposit assessment history
  have gapMean : expect (assessment.belief bob site)
      (fun history => value history - ceiling history) = 0 := by
    rw [expect_sub valueIntegrable ceilingIntegrable]
    exact sub_eq_zero.mpr (rational_supported_response_value weight nonnegative site representative
      decision current reward forfeit deposit forfeitNonnegative depositNonnegative assessment
        rational response supported)
  have equal := expect_eq_const_of_le_on_support (assessment.belief bob site)
    (fun history => value history - ceiling history) 0
    (payoffIntegrable_sub valueIntegrable ceilingIntegrable)
    (fun history _ => sub_nonpos.mpr (conditionalValue_le_canonicalValue weight nonnegative site
      representative decision current reward forfeit deposit forfeitNonnegative depositNonnegative
        assessment response history)) gapMean
  intro history reached
  exact sub_eq_zero.mp (equal history reached)

theorem rational_supported_payoff_eq_canonicalValue (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (believed : history ∈ (assessment.belief bob site).support) :
    ∀ final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)).support,
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) bob =
      canonicalValue weight nonnegative site representative decision current reward forfeit
        deposit assessment history := by
  apply expect_eq_const_of_le_on_support _ _ _
    (payoffIntegrable_of_bounded _ _ fun final =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final))
    (fun final reached => payoff_le_canonicalValue weight nonnegative site representative decision
      current reward forfeit deposit forfeitNonnegative depositNonnegative assessment history
        response _ final reached)
  exact rational_conditional_value_eq_canonicalValue weight nonnegative site representative decision
    current reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational
      response supported history believed

theorem rational_supported_clean_settlement (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (believed : history ∈ (assessment.belief bob site).support)
    (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) ∧
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          (app.finished final) bob = 0 := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  have saturated := rational_supported_payoff_eq_canonicalValue weight nonnegative site
    representative decision current reward forfeit deposit forfeitPositive.le depositPositive.le
      assessment rational response supported history believed final reached
  have comparison := payoff_audit_regret_le_canonicalValue weight nonnegative site representative
    decision current reward forfeit deposit assessment history response players final reached
  have charged := TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (app.finished final) bob
  have auditNonnegative := mul_nonneg charged.1 depositPositive.le
  have notFailed : final.application.config.store (.inr bobRevealEvent) ≠ some .failure := by
    intro failed
    rw [failed, ite_eq_left rfl] at comparison
    linarith
  have clear : TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) bob = 0 := by
    rw [ite_eq_right notFailed] at comparison
    have zero : TerminalAudit.charge
        (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          (app.finished final) bob * deposit bob = 0 := by linarith
    exact (mul_eq_zero.mp zero).resolve_right (ne_of_gt depositPositive)
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨12, some bob, recovered.execution⟩ recovered.trace
  obtain ⟨aliceResult, aliceStored⟩ := Option.isSome_iff_exists.mp
    (LateOpeningRuntimeReadout.bob_prefix_other_field_available recovered.execution.application
      recovered.ready (.inr aliceEvent) (by decide))
  obtain ⟨result, stored, _readout⟩ :=
    LateOpeningRuntimeBobIncentive.continuation_readout weight nonnegative 12
    recovered.execution recovered.trace recovered.answer recovered.bound recovered.ready bit label
    valid aliceResult aliceStored response players final reached
  cases result with
  | failure => exact (notFailed stored).elim
  | success answer =>
      have immutable := LateOpeningRuntimeReadout.bob_continuation_success_immutable
        LateOpeningRuntimeService.runtime leaks players
        (LateOpeningRuntimeService.scheduler weight nonnegative) 12 recovered.execution final _
          valid recovered.answer recovered.bound response reached answer stored
      have compatible := decisionOfInformation_spec weight nonnegative site representative decision
        current history
      exact ⟨stored.trans (congrArg (fun value => some (PublicationResult.success value))
        (immutable.trans compatible.2.2.2.symm)), clear⟩

end Vegas.Examples.LateOpeningRuntimeOptionalRationality
