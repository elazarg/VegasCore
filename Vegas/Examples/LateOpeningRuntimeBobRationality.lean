/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobInformation
import Interaction.ReactivePassiveDecision
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential rationality at an actual final native disclosure

The existing native assessment evaluates complete whole-policy deviations.
At a clean, ready and timely final Bob information site, its actual belief
and bounded response menu satisfy the checked disclosure regret bound. Any
positive publication forfeit therefore makes terminal disclosure failure
have zero probability. No equilibrium or earlier-site rationality is asserted.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeBobAudit LateOpeningRuntimeBobIncentive LateOpeningRuntimeBobInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨6, some bob, decision.execution⟩)

include current in
theorem site_information : site.1 =
    some (decision.execution.recall bob, decision.execution.observe app bob) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

/-- The truthful opening is a genuine choice at this bounded information
site; it is not an added action or a hypothetical unrestricted deviation. -/
def openingChoice : (LateOpeningRuntimeNash.model weight nonnegative).Choice bob site.1 := by
  refine ⟨some (canonical weight nonnegative decision), ?_⟩
  rw [site_information weight nonnegative site representative decision current]
  exact ⟨canonical weight nonnegative decision,
    canonical_available weight nonnegative representative.1 decision current, rfl⟩

def openingPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob := by
  classical
  exact (assessment.strategy bob).commit site.1
    (openingChoice weight nonnegative site representative decision current)

/-- The complete actual final-execution law under Bob's chosen whole policy
and the native posterior over precisely this information class. -/
def finalLaw (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    ((alternative site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
      continuation weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history)
        response (fun _ => app.silentPolicy)

theorem current_continuation_law
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom profile
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
      ((profile bob site.1).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        (continuation weight nonnegative
          (decisionOfInformation weight nonnegative site representative decision current history)
          response (fun _ => app.silentPolicy)).map app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have last := rawMenu.run_last_response initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20 (final_passive weight nonnegative)
      profile history.1 bob 6 recovered.execution valid.1 (by
        rw [final_cursor weight nonnegative recovered.execution recovered.trace])
  rw [history.2] at last
  exact last

variable (reward forfeit : ℝ)
  (sample : List (SettledEvidence setup .sequential) →
    PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state bob)
    (2 * LateOpeningRuntimeService.horizon + 1)

theorem context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    ((context weight nonnegative site reward forfeit sample deposit assessment).outcome
      alternative).map History.state =
    (finalLaw weight nonnegative site representative decision current assessment alternative).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief,
    InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  rw [current_continuation_law weight nonnegative site representative decision current,
    PMF.map_bind, Profile.update_same]

theorem context_integrable
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    Context.IntegrableAt
      (context weight nonnegative site reward forfeit sample deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    payoff_bounded reward forfeit sample deposit history.state

theorem context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy bob) :
    (context weight nonnegative site reward forfeit sample deposit assessment).value alternative =
    expect (finalLaw weight nonnegative site representative decision current assessment alternative)
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit sample deposit
        (app.finished final) bob) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit sample deposit assessment).outcome alternative)
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit sample deposit state bob)
  rw [context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  exact mapped.symm

theorem opening_finalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    finalLaw weight nonnegative site representative decision current assessment
      (openingPolicy weight nonnegative site representative decision current assessment) =
    (assessment.belief bob site).bind fun history =>
      continuation weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history)
        (canonical weight nonnegative
          (decisionOfInformation weight nonnegative site representative decision current history))
        (fun _ => app.silentPolicy) := by
  classical
  unfold finalLaw openingPolicy
  rw [InformationModel.BehavioralPolicy.commit_self, PMF.pure_map]
  apply bind_congr_on_support _
  intro history _
  rw [PMF.pure_bind]
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have same := canonical_same_information weight nonnegative decision
    (decisionOfInformation weight nonnegative site representative decision current history)
      valid.2.1 valid.2.2
  change continuation weight nonnegative _ (canonical weight nonnegative decision) _ = _
  rw [same]

/-- The native assessment's complete deviation value, rather than a separate
postulated one-step value, bounds actual terminal disclosure failure. -/
theorem final_failure_regret
    (forfeitNonnegative : 0 ≤ forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    forfeit * ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal ≤
    (context weight nonnegative site reward forfeit sample deposit assessment).value
      (openingPolicy weight nonnegative site representative decision current assessment) -
    (context weight nonnegative site reward forfeit sample deposit assessment).value
      (assessment.strategy bob) := by
  let recover := decisionOfInformation weight nonnegative site representative decision current
  have regret := canonical_regret weight nonnegative reward forfeit forfeitNonnegative
    sample authentic deposit depositNonnegative ((assessment.belief bob site).map recover)
      (fun _ => (assessment.strategy bob site.1).map (fun choice => choice.1.getD ⟨none⟩))
      (fun _ _ => app.silentPolicy) (fun _ _ => app.silentPolicy)
  simp only [PMF.bind_map] at regret
  rw [context_value weight nonnegative site representative decision current,
    context_value weight nonnegative site representative decision current,
    opening_finalLaw weight nonnegative site representative decision current]
  simpa only [finalLaw, PMF.bind_map, Function.comp_def, recover] using regret

/-- Existing sequential rationality at this site forces almost sure final
disclosure under its actual belief. The forfeit need only be positive. -/
theorem rational_final_failure_zero
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit sample deposit assessment)) :
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
      0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit sample deposit assessment
      (assessment.strategy bob))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit sample deposit
      assessment alternative)).mp rational
        (openingPolicy weight nonnegative site representative decision current assessment)
        (Set.mem_univ _)
  have regret := final_failure_regret weight nonnegative site representative decision current
    reward forfeit sample deposit forfeitPositive.le authentic depositNonnegative assessment
  have nonnegative := ENNReal.toReal_nonneg (a :=
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}))
  nlinarith

/-- Rationality in the existing well-founded native game implies the local
almost-sure publication result at any site with one clean final representative. -/
theorem sequentially_rational_final_failure_zero
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history =>
        LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state who)) :
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
      0 := by
  apply rational_final_failure_zero weight nonnegative site representative decision current
    reward forfeit sample deposit forfeitPositive authentic depositNonnegative assessment
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

/-- Every actual native sequential equilibrium discloses almost surely at
these final sites, including sites reached only by earlier deviations. -/
theorem equilibrium_final_failure_zero
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history =>
        LateOpeningRuntimeNash.payoff reward forfeit sample deposit history.state who)) :
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal =
      0 :=
  sequentially_rational_final_failure_zero weight nonnegative site representative decision current
    reward forfeit sample deposit forfeitPositive authentic depositNonnegative assessment
      equilibrium.1

/-- A bound on this genuine whole-policy deviation gives a quantitative
failure bound, without introducing a separate approximate assessment type. -/
theorem final_failure_le_of_deviation_regret
    (forfeitPositive : 0 < forfeit)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (epsilon : ℝ)
    (regret : (context weight nonnegative site reward forfeit sample deposit assessment).value
        (openingPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit sample deposit assessment).value
        (assessment.strategy bob) ≤ epsilon) :
    ((finalLaw weight nonnegative site representative decision current assessment
      (assessment.strategy bob)).toOuterMeasure
        {final | final.application.config.store (.inr bobRevealEvent) = some .failure}).toReal ≤
      epsilon / forfeit := by
  apply (le_div_iff₀ forfeitPositive).mpr
  have bound := final_failure_regret weight nonnegative site representative decision current
    reward forfeit sample deposit forfeitPositive.le authentic depositNonnegative assessment
  nlinarith

end Vegas.Examples.LateOpeningRuntimeBobRationality
