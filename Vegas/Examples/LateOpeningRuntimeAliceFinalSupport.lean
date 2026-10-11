/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication
import Vegas.Examples.LateOpeningRuntimeAliceResponseNormalization
import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality
import Vegas.Examples.LateOpeningRuntimeContinuationRationality

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
open LateOpeningRuntimeContinuationRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceEmptyDecision LateOpeningRuntimeAliceContinuation
  LateOpeningRuntimeAliceOpeningContinuation
open LateOpeningRuntimeAliceResponseNormalization

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
  (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
  (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
  (normalized : EmptyResponsesNormalized weight nonnegative assessment.strategy)
  (rational : ReceiverContinuationsRational weight nonnegative assessment
      (LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit))

include normalized in
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
    (LateOpeningRuntimeGame.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (18 = 0 ∧ some alice = none); simp) rfl
  let representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
      alice site.1 := ⟨history, observed.symm⟩
  have current : representative.1.state = some ⟨18, some alice, decision.execution⟩ := rfl
  have zero := normalized site representative decision current
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

include positive rewardNonnegative forfeitNonnegative depositNonnegative normalized in
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
    have genuine := decoded_response_genuine weight nonnegative assessment normalized
        decision boundedTrace response supported
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact genuine.elim
    | some submission =>
        exact LateOpeningRuntimeAliceOpeningRationality.continuation_opening_lower
          weight nonnegative reward forfeit deposit positive decision submission genuine _
            rewardNonnegative forfeitNonnegative depositNonnegative

include rational positive rewardNonnegative depositNonnegative normalized in
theorem final_response_value_floor (forfeitPositive : 0 < forfeit)
    (bobDepositPositive : 0 < deposit bob) (decision : DecisionHistory weight nonnegative)
    (low : (LateOpeningRuntimeBobSuccessPayoff.originalLabel decision.execution).val < 2)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, decision.execution⟩)) :
    LateOpeningRuntimeLateAcceptance.inclusionProbability weight * reward / 2 -
        (1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) *
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
  · exact aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit depositNonnegative _
  · intro response supported
    have genuine := decoded_response_genuine weight nonnegative assessment normalized
        decision boundedTrace response supported
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact genuine.elim
    | some submission =>
        have available := rawMenu.decode_embedPolicy_covered initial
          LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) alice (assessment.strategy alice)
          _ _ _ supported
        have lower := LateOpeningRuntimeAliceProtectedPublication.opening_payoff_floor weight
          nonnegative positive decision boundedTrace submission genuine available low reward forfeit
          deposit rewardNonnegative forfeitPositive bobDepositPositive assessment rational
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) rfl
          depositNonnegative
        rw [LateOpeningRuntimeAliceOpeningRationality.openingLaw_eq_continuation] at lower
        exact lower

end Vegas.Examples.LateOpeningRuntimeAliceFinalSupport
