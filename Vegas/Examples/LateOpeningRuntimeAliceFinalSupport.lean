/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality

/-! # Actual supported opening responses of a sequentially rational profile

Any legal bounded representative realizing the empty final callback supplies
a genuine information site. Global sequential rationality therefore forces
the physical decoded policy to emit only genuine opening aliases there,
including when an earlier deviation has made this callback counterfactual.
Its complete native continuation has the same conservative lottery lower
bound, with every later Bob policy retained.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFinalSupport

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceEmptyDecision LateOpeningRuntimeAliceContinuation
  LateOpeningRuntimeAliceOpeningContinuation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
  (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
  (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
    weight reward forfeit deposit)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
  (rational : assessment.IsSequentiallyRational
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit history.state who))

include rational positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive in
theorem decoded_response_genuine (decision : DecisionHistory weight nonnegative)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, decision.execution⟩))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy alice
        (decision.execution.recall alice) (decision.execution.observe app alice)).support) :
    LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
      weight nonnegative decision response := by
  classical
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨18, some alice, decision.execution⟩, boundedTrace⟩
  obtain ⟨site, observed⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (18 = 0 ∧ some alice = none); simp) rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1 := ⟨history, observed.symm⟩
  have current : representative.1.state = some ⟨18, some alice, decision.execution⟩ := rfl
  have zero :=
    LateOpeningRuntimeAliceOpeningRationality.sequentially_rational_nongenuine_response_zero
      weight nonnegative site representative decision current reward forfeit deposit positive
        rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational
  have law : rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy alice
        (decision.execution.recall alice) (decision.execution.observe app alice) =
      LateOpeningRuntimeAliceOpeningRationality.responseLaw weight nonnegative site
        (assessment.strategy alice) := by
    unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
      ReactiveApplication.ResponseMenu.embedPolicy
    rw [PMF.map_comp, ← LateOpeningRuntimeAliceOpeningRationality.site_information
      weight nonnegative site representative decision current]
    rfl
  rw [law] at supported
  by_contra nongenuine
  have positiveMass := toOuterMeasure_toReal_pos
    (LateOpeningRuntimeAliceOpeningRationality.responseLaw weight nonnegative site
      (assessment.strategy alice))
    (s := {response | ¬ LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
      weight nonnegative decision response}) ⟨response, nongenuine, supported⟩
  rw [zero] at positiveMass
  exact (lt_irrefl 0) positiveMass

include rational positive rewardNonnegative forfeitNonnegative depositNonnegative marginPositive in
/-- The incumbent's real current response, followed by its entire remaining
policy, has the genuine late-opening payoff lower bound at every legal empty
final callback. No reach or posterior hypothesis is required. -/
theorem final_response_value_lower (decision : DecisionHistory weight nonnegative)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, decision.execution⟩)) :
    -(1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) *
        (forfeit + deposit alice) ≤
      expect ((app.invoke (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
          alice decision.execution).bind
            (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
              (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
                (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 18))
        (aliceUtility reward forfeit deposit) := by
  unfold ReactiveApplication.invoke
  rw [PMF.bind_map]
  apply expect_bind_ge_constant_on_support
  · exact aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative _
  · intro response supported
    have genuine := decoded_response_genuine weight nonnegative reward forfeit deposit positive
      rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational
        decision boundedTrace response supported
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact genuine.elim
    | some submission =>
        exact LateOpeningRuntimeAliceOpeningRationality.continuation_opening_lower
          weight nonnegative reward forfeit deposit positive decision submission genuine _
            rewardNonnegative forfeitNonnegative depositNonnegative

end Vegas.Examples.LateOpeningRuntimeAliceFinalSupport
