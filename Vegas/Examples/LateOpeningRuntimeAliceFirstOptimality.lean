/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstFiber
import Vegas.Examples.LateOpeningRuntimeAliceFirstRationality
import Vegas.Examples.LateOpeningRuntimeFirstRetryComparison
import GameTheory.Analysis.Protocol.SupportedChoices

/-! # Optimal native timing responses at the first late sender callback

Every supported raw response maximizes its actual original continuation
value among all available raw responses. Genuine private aliases remain
separate legal actions. A strict send-versus-silence comparison therefore
fixes the genuine-emission probability once forbidden packets have zero mass.
The result uses the complete native information class, with no posterior
assumption and no replacement of a future behavioral policy.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeAliceFirstDecision LateOpeningRuntimeAliceFirstResponse
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeFirstObservation
  LateOpeningRuntimeReadout

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1) (bit : Bool) (label : Fin 3)
  (current : representative.1.state = some ⟨22, some alice, firstLateDecision bit label⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- A fixed current raw action followed by the entire original profile. -/
def responseValue
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action) : ℝ :=
  expect (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
    22 ((firstLateDecision bit label).respond app alice response))
    (aliceUtility reward forfeit deposit)

include current in
private theorem site_info : site.1 =
    some ((firstLateDecision bit label).recall alice,
      (firstLateDecision bit label).observe app alice) :=
  site_information weight nonnegative site representative
    (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label) current

include current in
private theorem current_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    responseLaw weight nonnegative site
    (assessment.strategy alice site.1) =
    LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative
      assessment.strategy bit label := by
  unfold LateOpeningRuntimeFirstRetryComparison.firstResponses
    LateOpeningRuntimeFirstRetryComparison.players ReactiveApplication.ResponseMenu.decodeProfile
    ReactiveApplication.decodePolicy ReactiveApplication.ResponseMenu.embedPolicy responseLaw
  rw [PMF.map_comp, site_info weight nonnegative site representative bit label current]
  rfl

include current in
private def responseChoice (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  refine ⟨some response, ?_⟩
  rw [site_info weight nonnegative site representative bit label current]
  exact ⟨response, available, rfl⟩

include current in
open Classical in
private theorem commit_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (choice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      ((assessment.strategy alice).commit site.1 choice) =
      responseValue weight nonnegative bit label reward forfeit deposit assessment
        (choice.1.getD ⟨none⟩) := by
  change (context weight nonnegative site reward forfeit deposit assessment).value
    ((assessment.strategy alice).withLaw site.1 (PMF.pure choice)) = _
  rw [LateOpeningRuntimeAliceFirstFiber.context_value_eq_physical weight nonnegative site
    representative bit label current reward forfeit deposit assessment (PMF.pure choice)]
  simp only [responseLaw, PMF.pure_map, PMF.pure_bind]
  rfl

private theorem local_rational
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment) := by
  have localRational := rational alice site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

theorem supported_response_available
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (response : app.Action)
    (supported : response ∈ (LateOpeningRuntimeFirstRetryComparison.firstResponses
      weight nonnegative assessment.strategy bit label).support) :
    response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice) :=
  rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) alice (assessment.strategy alice)
      _ _ response supported

include representative current in
/-- Current raw responses played with positive probability maximize the
actual physical continuation value against every available raw response. -/
theorem sequentially_rational_supported_response_maximal
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (LateOpeningRuntimeFirstRetryComparison.firstResponses
      weight nonnegative assessment.strategy bit label).support)
    (alternative : app.Action)
    (available : alternative ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    responseValue weight nonnegative bit label reward forfeit deposit assessment alternative ≤
      responseValue weight nonnegative bit label reward forfeit deposit assessment response := by
  classical
  rw [← current_law weight nonnegative site representative bit label current assessment]
    at supported
  obtain ⟨choice, played, same⟩ := PMF.support_map .. ▸ supported
  let candidate := responseChoice weight nonnegative site representative bit label current
    alternative available
  have factor := (LateOpeningRuntimeNash.model weight nonnegative).runnerFactorsAt_truncated
    (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) alice site)
    (2 * LateOpeningRuntimeService.horizon)
  have best := assessment.supported_choice_optimal
    ((LateOpeningRuntimeNash.model weight nonnegative).truncatedRunner
      (2 * LateOpeningRuntimeService.horizon + 1)) site factor
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state alice)
    (local_rational weight nonnegative site reward forfeit deposit assessment rational)
    (fun _ => payoffIntegrable_of_finite _ _) choice played
    ((assessment.strategy alice).commit site.1 candidate)
  change (context weight nonnegative site reward forfeit deposit assessment).value
    ((assessment.strategy alice).commit site.1 candidate) ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        ((assessment.strategy alice).commit site.1 choice) at best
  rw [commit_value weight nonnegative site representative bit label current reward forfeit deposit
    assessment candidate, commit_value weight nonnegative site representative bit label current
      reward forfeit deposit assessment choice] at best
  change choice.1.getD ⟨none⟩ = response at same
  change responseValue weight nonnegative bit label reward forfeit deposit assessment alternative ≤
    responseValue weight nonnegative bit label reward forfeit deposit assessment
      (choice.1.getD ⟨none⟩) at best
  exact same ▸ best

include representative current in
/-- The incumbent value is at least the value of each available current
response with the entire original future retained. -/
theorem sequentially_rational_value_ge_response
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    responseValue weight nonnegative bit label reward forfeit deposit assessment response ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy alice) := by
  classical
  let choice := responseChoice weight nonnegative site representative bit label current
    response available
  have best := (Context.isLocallyOptimal_iff_of_integrable
    (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mp
      (local_rational weight nonnegative site reward forfeit deposit assessment rational)
        ((assessment.strategy alice).commit site.1 choice) (Set.mem_univ _)
  rw [commit_value weight nonnegative site representative bit label current reward forfeit deposit
    assessment choice] at best
  exact best

private theorem canonical_genuine : GenuineResponse weight nonnegative
    (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
      (opening bit) := by
  refine ⟨disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩), rfl, ?_⟩
  change app.packet (firstLateDecision bit label).application alice []
    (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)) = _
  exact firstLate_opening_packet bit label

private theorem supported_permitted_of_zero
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (zero : ((LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative
      assessment.strategy bit label).toOuterMeasure {response | ¬ PermittedResponse
        weight nonnegative (LateOpeningRuntimeAliceFirstWitness.decisionHistory
          weight nonnegative bit label) response}).toReal = 0)
    (response : app.Action)
    (supported : response ∈ (LateOpeningRuntimeFirstRetryComparison.firstResponses
      weight nonnegative assessment.strategy bit label).support) :
    PermittedResponse weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response := by
  have absent := ((ENNReal.toReal_eq_zero_iff _).mp zero).resolve_right (outerMeasure_ne_top _ _)
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left] at absent
  exact Classical.byContradiction (fun forbidden => absent supported forbidden)

include representative current in
/-- A strictly better genuine opening forces total genuine-emission mass
when the actual raw law assigns zero mass to nongenuine packets. -/
theorem genuineProbability_one_of_preference
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (zero : ((LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative
      assessment.strategy bit label).toOuterMeasure {response | ¬ PermittedResponse
        weight nonnegative (LateOpeningRuntimeAliceFirstWitness.decisionHistory
          weight nonnegative bit label) response}).toReal = 0)
    (firstValue secondValue : ℝ)
    (openingValue : ∀ response ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
        ((firstLateDecision bit label).observe app alice),
      GenuineResponse weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response → responseValue weight nonnegative bit label reward forfeit deposit
            assessment response = firstValue)
    (silenceValue : responseValue weight nonnegative bit label reward forfeit deposit
      assessment ⟨none⟩ = secondValue)
    (better : secondValue < firstValue) :
    LateOpeningRuntimeFirstRetryComparison.genuineProbability weight nonnegative
      assessment.strategy bit label = 1 := by
  have full : (LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative
      assessment.strategy bit label).support ⊆ {response | GenuineResponse weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response} := by
    intro response supported
    have permitted := supported_permitted_of_zero weight nonnegative bit label assessment
      zero response supported
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        have best := sequentially_rational_supported_response_maximal weight nonnegative site
          representative bit label current reward forfeit deposit assessment rational ⟨none⟩
            supported (opening bit) (opening_in_raw_menu bit alice _ _)
        rw [openingValue (opening bit) (opening_in_raw_menu bit alice _ _)
          (canonical_genuine weight nonnegative bit label), silenceValue] at best
        exact (not_le_of_gt better best).elim
    | some submission => exact ⟨submission, rfl, permitted⟩
  unfold LateOpeningRuntimeFirstRetryComparison.genuineProbability
  rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr full, ENNReal.toReal_one]

include representative current in
/-- The checked native deterrence margin supplies the nongenuine-mass
condition for the strict first-opening preference. -/
theorem sequentially_rational_genuineProbability_one_of_preference
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (firstValue secondValue : ℝ)
    (openingValue : ∀ response ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
        ((firstLateDecision bit label).observe app alice),
      GenuineResponse weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response → responseValue weight nonnegative bit label reward forfeit deposit
            assessment response = firstValue)
    (silenceValue : responseValue weight nonnegative bit label reward forfeit deposit
      assessment ⟨none⟩ = secondValue)
    (better : secondValue < firstValue) :
    LateOpeningRuntimeFirstRetryComparison.genuineProbability weight nonnegative
      assessment.strategy bit label = 1 := by
  have zero := LateOpeningRuntimeAliceFirstRationality.sequentially_rational_nongenuine_packet_zero
    weight nonnegative site representative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label) current
      reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
        openingMarginPositive assessment rational
  rw [current_law weight nonnegative site representative bit label current assessment] at zero
  exact genuineProbability_one_of_preference weight nonnegative site representative bit label
    current reward forfeit deposit assessment rational zero firstValue secondValue
      openingValue silenceValue better

include representative current in
/-- A strictly better silent response excludes every genuine opening alias;
this implication does not require the nongenuine-packet exclusion premise. -/
theorem sequentially_rational_genuineProbability_zero_of_preference
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (firstValue secondValue : ℝ)
    (openingValue : ∀ response ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
        ((firstLateDecision bit label).observe app alice),
      GenuineResponse weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response → responseValue weight nonnegative bit label reward forfeit deposit
            assessment response = firstValue)
    (silenceValue : responseValue weight nonnegative bit label reward forfeit deposit
      assessment ⟨none⟩ = secondValue)
    (better : firstValue < secondValue) :
    LateOpeningRuntimeFirstRetryComparison.genuineProbability weight nonnegative
      assessment.strategy bit label = 0 := by
  have zero : (LateOpeningRuntimeFirstRetryComparison.firstResponses weight nonnegative
      assessment.strategy bit label).toOuterMeasure {response | GenuineResponse weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response} = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro response supported genuine
    have best := sequentially_rational_supported_response_maximal weight nonnegative site
      representative bit label current reward forfeit deposit assessment rational response
        supported ⟨none⟩ (bounds.silent_available LateOpeningRuntimeService.runtime leaks alice _ _)
    have available := supported_response_available weight nonnegative bit label assessment
      response supported
    rw [silenceValue, openingValue response available genuine] at best
    exact not_le_of_gt better best
  unfold LateOpeningRuntimeFirstRetryComparison.genuineProbability
  rw [zero, ENNReal.toReal_zero]

end Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality
