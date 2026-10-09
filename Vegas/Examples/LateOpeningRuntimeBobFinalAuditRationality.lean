/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobFinalAuditObservation

/-! # Zero final receiver collection on the entire information class

Canonical opening reaches the same immutable gross payoff without a charge.
Positive receiver collateral therefore eliminates every full-audit violation
under assessed support. The checked settled-record and own-input law then
extends zero charge to every compatible hidden history, including zero-belief
histories. This implication uses full authentic collection, not a claim that
owner observation by itself determines the audit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFinalAuditRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeBobIncentive LateOpeningRuntimeBobInformation LateOpeningRuntimeBobRationality
  LateOpeningRuntimeBobFinalFiberRationality LateOpeningRuntimeBobFinalAuditObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem fullCharge_one_of_ne_zero (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (charged : fullCharge control.execution ≠ 0) : fullCharge control.execution = 1 := by
  have binary : keyCharge (auditKey control.execution) = 0 ∨
      keyCharge (auditKey control.execution) = 1 := by
    unfold keyCharge
    split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  rw [← fullCharge_eq_keyCharge weight nonnegative control trace] at binary
  exact binary.resolve_left charged

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

private theorem canonical_charge_gap (history : DecisionHistory weight nonnegative)
    (forfeitNonnegative : 0 ≤ forfeit) (response : app.Action)
    (players future : Player → app.Policy) (final canonicalFinal : app.Execution)
    (reached : final ∈ (continuation weight nonnegative history response players).support)
    (canonicalReached : canonicalFinal ∈ (continuation weight nonnegative history
      (canonical weight nonnegative history) future).support) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
        (app.finished final) bob + fullCharge final * deposit bob ≤
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
        (app.finished canonicalFinal) bob := by
  have gross := (canonical_dominates weight nonnegative history reward forfeit forfeitNonnegative
    (fun actual => PMF.pure actual) (by
      intro actual observed present
      cases (PMF.mem_support_pure_iff _ _).mp present
      exact List.Subset.refl _)
    (fun _ => 0) (by rfl) response players future final canonicalFinal reached canonicalReached).1
  have clear := (canonical_clean weight nonnegative history (fun actual => PMF.pure actual)
    (by
      intro actual observed present
      cases (PMF.mem_support_pure_iff _ _).mp present
      exact List.Subset.refl _)
    future canonicalFinal canonicalReached).2
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility at gross ⊢
  simp only [mul_zero, sub_zero] at gross
  change _ - fullCharge final * deposit bob + fullCharge final * deposit bob ≤ _
  rw [clear, zero_mul, sub_zero]
  linarith

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨6, some bob, decision.execution⟩)

theorem final_audit_regret (forfeitNonnegative : 0 ≤ forfeit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    deposit bob * ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure {final | fullCharge final ≠ 0}).toReal ≤
    (context weight nonnegative site reward forfeit (fun actual => PMF.pure actual) deposit
      assessment).value
      (openingPolicy weight nonnegative site representative decision current assessment) -
    (context weight nonnegative site reward forfeit (fun actual => PMF.pure actual) deposit
      assessment).value (assessment.strategy bob) := by
  classical
  let recover := decisionOfInformation weight nonnegative site representative decision current
  let raw := fun history =>
    ((assessment.strategy bob site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
      continuation weight nonnegative (recover history) response (fun _ => app.silentPolicy)
  let comparator := fun history => continuation weight nonnegative (recover history)
    (canonical weight nonnegative (recover history)) (fun _ => app.silentPolicy)
  let payoff := fun final => LateOpeningRuntimeNash.payoff reward forfeit
    (fun actual => PMF.pure actual) deposit (app.finished final) bob
  have integrable (law : PMF app.Execution) : PayoffIntegrable law payoff :=
    payoffIntegrable_of_bounded _ _ fun final =>
      payoff_bounded reward forfeit (fun actual => PMF.pure actual) deposit (app.finished final)
  have regret := expect_failure_regret (assessment.belief bob site) raw comparator payoff payoff
    {final | fullCharge final ≠ 0} (deposit bob) (integrable _) (integrable _)
    (fun _ _ => integrable _) (fun _ _ => integrable _) (by
      intro history _ final reached canonicalFinal canonicalReached
      obtain ⟨response, _, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have bound := canonical_charge_gap weight nonnegative reward forfeit deposit (recover history)
        forfeitNonnegative response _ _ final canonicalFinal continued canonicalReached
      simp only [Set.mem_ofPred_eq]
      by_cases charged : fullCharge final ≠ 0
      · obtain ⟨trace⟩ := continuation_trace weight nonnegative (recover history) response _
          final continued
        have one := fullCharge_one_of_ne_zero weight nonnegative ⟨0, none, final⟩ trace charged
        rw [ite_eq_left charged, mul_one]
        simpa only [payoff, one, one_mul] using bound
      · rw [ite_eq_right charged, mul_zero, add_zero]
        simpa only [payoff, not_not.mp charged, zero_mul, add_zero] using bound)
  rw [context_value weight nonnegative site representative decision current,
    context_value weight nonnegative site representative decision current,
    opening_finalLaw weight nonnegative site representative decision current]
  exact regret

theorem rational_final_charge_probability_zero (forfeitNonnegative : 0 ≤ forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit (fun actual => PMF.pure actual) deposit
        assessment)) :
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure {final | fullCharge final ≠ 0}).toReal = 0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit (fun actual => PMF.pure actual)
      deposit assessment (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit
      (fun actual => PMF.pure actual) deposit assessment alternative)).mp rational
    (openingPolicy weight nonnegative site representative decision current assessment)
    (Set.mem_univ _)
  have regret := final_audit_regret weight nonnegative reward forfeit deposit site representative
    decision current forfeitNonnegative assessment
  have nonnegative := ENNReal.toReal_nonneg (a :=
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure {final | fullCharge final ≠ 0}))
  nlinarith

theorem finalLaw_charge_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (players : Player → app.Policy) :
    (finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).map fullCharge =
    (responseContinuationLaw weight nonnegative site assessment decision players).map
      fullCharge := by
  unfold finalLaw
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief bob site).bind (fun _ =>
        (responseContinuationLaw weight nonnegative site assessment decision players).map
          fullCharge) := by
      apply bind_congr_on_support _
      intro history _
      dsimp only [responseContinuationLaw]
      rw [PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro response _
      have compatible := decisionOfInformation_spec weight nonnegative site representative
        decision current history
      exact continuation_charge_same_information weight nonnegative _ decision
        compatible.2.1.symm compatible.2.2.symm response _ players
    _ = _ := PMF.bind_const _ _

/-- A supported final response incurs zero actual full audit charge on every
legal compatible hidden history, including histories with zero assessment belief. -/
theorem rational_supported_charge_zero (forfeitNonnegative : 0 ≤ forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit (fun actual => PMF.pure actual) deposit
        assessment))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) : fullCharge final = 0 := by
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  have assessed := rational_final_charge_probability_zero weight nonnegative reward forfeit deposit
    site representative decision current forfeitNonnegative depositPositive assessment rational
  have common := finalLaw_charge_law weight nonnegative site representative decision current
    assessment players
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have fixed : (responseContinuationLaw weight nonnegative site assessment decision players).map
      fullCharge =
    (responseContinuationLaw weight nonnegative site assessment recovered players).map
      fullCharge := by
    unfold responseContinuationLaw
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro selected _
    exact continuation_charge_same_information weight nonnegative _ _ compatible.2.1
      compatible.2.2 selected players players
  have same := common.trans fixed
  have mass := congrArg (fun law : PMF ℝ => (law.toOuterMeasure {charge | charge ≠ 0}).toReal) same
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] at mass
  have zero : (responseContinuationLaw weight nonnegative site assessment recovered
      players).toOuterMeasure {last | fullCharge last ≠ 0} = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp (mass.symm.trans assessed) |>.resolve_right
      (outerMeasure_ne_top _ _)
  have present : final ∈
      (responseContinuationLaw weight nonnegative site assessment recovered players).support := by
    rw [responseContinuationLaw, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨response, supported, reached⟩
  by_contra charged
  exact ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mp zero).le_bot ⟨present, charged⟩

/-- Whole-game rationality settles the immutable answer without receiver
collection on every legal hidden history of the clean final information site. -/
theorem sequentially_rational_supported_clean_publication (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) ∧
      fullCharge final = 0 := by
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact ⟨rational_supported_publication weight nonnegative site representative decision current
    reward forfeit (fun actual => PMF.pure actual) deposit forfeitPositive
      (by
        intro actual observed present
        cases (PMF.mem_support_pure_iff _ _).mp present
        exact List.Subset.refl _)
      depositPositive.le assessment localRational history response supported players final reached,
    rational_supported_charge_zero weight nonnegative reward forfeit deposit site representative
      decision current forfeitPositive.le depositPositive assessment localRational history response
        supported players final reached⟩

/-- The all-hidden-history settlement applies to every existing native
sequential equilibrium, including continuations reached by prior deviations. -/
theorem equilibrium_supported_clean_publication (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (response : app.Action)
    (supported : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (continuation weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) ∧
      fullCharge final = 0 :=
  sequentially_rational_supported_clean_publication weight nonnegative reward forfeit deposit site
    representative decision current forfeitPositive depositPositive assessment equilibrium.1 history
      response supported players final reached

end Vegas.Examples.LateOpeningRuntimeBobFinalAuditRationality
