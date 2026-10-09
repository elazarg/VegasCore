/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceOpeningIncentive
import Vegas.Examples.LateOpeningRuntimeAliceRationality
import Vegas.Pending.ReactiveResponseRecall

/-! # Rational opening at an actual empty final Alice callback

Every member of the complete native information set has no previous Alice
transmission and an empty pending pool. The continuation keeps all later Bob
policies. A local repair preserves genuine opening aliases and replaces only
other responses with the legal initialized opening.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeAliceContinuation
  LateOpeningRuntimeAliceEmptyDecision LateOpeningRuntimeUtility LateOpeningRuntimeReadout
open LateOpeningRuntimeAliceIncentive (alice_absent)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨18, some alice, decision.execution⟩)

include current in
theorem site_information : site.1 =
    some (decision.execution.recall alice, decision.execution.observe app alice) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf alice representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

def continuation (decision : DecisionHistory weight nonnegative) (response : app.Action)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
    (decision.execution.respond app alice response)

def responseLaw
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    PMF app.Action := (alternative site.1).map (fun choice => choice.1.getD ⟨none⟩)

def finalLaw (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    PMF app.Execution :=
  (assessment.belief alice site).bind fun history =>
    (responseLaw weight nonnegative site alternative).bind fun response =>
      continuation weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history)
        response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)

theorem current_continuation_law
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom profile
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
      (responseLaw weight nonnegative site (profile alice)).bind fun response =>
        (continuation weight nonnegative
          (decisionOfInformation weight nonnegative site representative decision current history)
          response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) profile)).map
              app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have last := rawMenu.run_last_response_of_unactivated initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
      profile history.1 18 recovered.execution valid.1 (by rw [decision_cursor])
  rw [history.2] at last
  refine last.trans ?_
  apply bind_congr_on_support _
  intro response _
  unfold continuation
  rw [app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
    _ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) profile)
    (by intro who different; rw [Function.update_of_ne different]) 18 _
    (by change 8 ≤ recovered.execution.environmentRecall.length; rw [decision_cursor])]

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state alice) (2 * LateOpeningRuntimeService.horizon + 1)

theorem context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome alternative).map
      History.state =
    (finalLaw weight nonnegative site representative decision current assessment alternative).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  rw [current_continuation_law weight nonnegative site representative decision current,
    PMF.map_bind, Profile.update_same]
  apply bind_congr_on_support _
  intro response _
  unfold continuation
  rw [app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
    _ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
    (by
      intro who different
      change app.decodePolicy _ = app.decodePolicy _
      rw [Profile.update_of_ne _ _ different]) 18 _
    (by
      change 8 ≤ (decisionOfInformation weight nonnegative site representative decision current
        history).execution.environmentRecall.length
      rw [decision_cursor])]

theorem context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    (context weight nonnegative site reward forfeit deposit assessment).value alternative =
    expect (finalLaw weight nonnegative site representative decision current assessment alternative)
      (aliceUtility reward forfeit deposit) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome alternative)
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state alice)
  rw [context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  exact mapped.symm


theorem context_integrable
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    Context.IntegrableAt
      (context weight nonnegative site reward forfeit deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    LateOpeningRuntimeAliceRationality.payoff_bounded reward forfeit deposit
      rewardNonnegative forfeitNonnegative depositNonnegative history.state

/-- The initialized opening is already in the complete raw menu. -/
def openingChoice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  classical
  refine ⟨some (LateOpeningRuntimeLatePrefix.opening decision.bit), ?_⟩
  rw [site_information weight nonnegative site representative decision current]
  refine ⟨LateOpeningRuntimeLatePrefix.opening decision.bit, ?_, rfl⟩
  exact LateOpeningRuntimeLatePrefix.opening_in_raw_menu _ _ _ _

def GenuineResponse (response : app.Action) : Prop :=
  match response.transmission with
  | none => False
  | some submission => LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening
      weight nonnegative decision submission

/-- Genuine private aliases are retained exactly. -/
def repairResponse (response : app.Action) : app.Action := by
  classical
  exact if GenuineResponse weight nonnegative decision response then response
    else LateOpeningRuntimeLatePrefix.opening decision.bit

def repairChoice (choice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1) :
    (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  classical
  exact if GenuineResponse weight nonnegative decision (choice.1.getD ⟨none⟩) then choice
    else openingChoice weight nonnegative site representative decision current

theorem repairChoice_response
    (choice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1) :
    (repairChoice weight nonnegative site representative decision current choice).1.getD ⟨none⟩ =
      repairResponse weight nonnegative decision (choice.1.getD ⟨none⟩) := by
  classical
  unfold repairChoice repairResponse
  split <;> rfl

def openingPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice := by
  classical
  exact (assessment.strategy alice).withLaw site.1
    ((assessment.strategy alice site.1).map
      (repairChoice weight nonnegative site representative decision current))

theorem repaired_responseLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    responseLaw weight nonnegative site
      (openingPolicy weight nonnegative site representative decision current assessment) =
        (responseLaw weight nonnegative site (assessment.strategy alice)).map
          (repairResponse weight nonnegative decision) := by
  classical
  unfold responseLaw openingPolicy
  rw [InformationModel.BehavioralPolicy.withLaw_self, PMF.map_comp, PMF.map_comp]
  congr 1
  funext choice
  exact repairChoice_response weight nonnegative site representative decision current choice

theorem genuine_of_information
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1)
    (response : app.Action) :
    GenuineResponse weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response ↔ GenuineResponse weight nonnegative decision response := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have facts := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have own := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  have other := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) recovered.trace
  change decision.execution.InputRecall app at own
  change recovered.execution.InputRecall app at other
  have known := LateOpeningRuntimeService.runtime.known_eq_of_input_eq leaks
    decision.execution recovered.execution alice own other facts.2.1 facts.2.2.1
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      have packet := LateOpeningRuntimeService.runtime.response_packet_eq_of_input_eq leaks
        decision.execution recovered.execution alice submission facts.2.2.1 known
      change (_ = (LateOpeningRuntimeLatePrefix.openingMessage recovered.bit).payload) ↔
        (_ = (LateOpeningRuntimeLatePrefix.openingMessage decision.bit).payload)
      change app.packet (app.submit decision.execution.application alice submission) alice
        (decision.execution.network.known alice) submission =
          app.packet (app.submit recovered.execution.application alice submission) alice
            (recovered.execution.network.known alice) submission at packet
      rw [← packet, ← facts.2.2.2]


/-- Later Alice policies do not alter this genuine-opening continuation. -/
theorem openingLaw_eq_continuation (recovered : DecisionHistory weight nonnegative)
    (submission : app.Submission) (players : Player → app.Policy) :
    LateOpeningRuntimeAliceOpeningContinuation.openingLaw weight nonnegative recovered
      submission players = continuation weight nonnegative recovered ⟨some submission⟩ players := by
  unfold LateOpeningRuntimeAliceOpeningContinuation.openingLaw continuation
  rw [app.continuation_policy_independent_of_unactivated
    (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
      (alice_absent weight nonnegative)
    _ players (by
      intro who different
      simp only [quietAgainst, ite_eq_right different]) 18 _
    (by change 8 ≤ recovered.execution.environmentRecall.length; rw [decision_cursor])]
  rfl

theorem continuation_opening_lower (positive : 0 < weight)
    (recovered : DecisionHistory weight nonnegative) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening
      weight nonnegative recovered submission) (players : Player → app.Policy)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice) :
    -(1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) *
        (forfeit + deposit alice) ≤
      expect (continuation weight nonnegative recovered ⟨some submission⟩ players)
        (aliceUtility reward forfeit deposit) := by
  have lower := LateOpeningRuntimeAliceOpeningContinuation.opening_payoff_lower
    weight nonnegative positive recovered submission genuine players rewardNonnegative
      forfeitNonnegative deposit depositNonnegative
  rw [openingLaw_eq_continuation] at lower
  exact lower

theorem continuation_silence_upper (recovered : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice) :
    expect (continuation weight nonnegative recovered ⟨none⟩ players)
      (aliceUtility reward forfeit deposit) ≤ reward - forfeit :=
  LateOpeningRuntimeAliceSilentContinuation.silence_payoff_upper weight nonnegative recovered
    players rewardNonnegative forfeitNonnegative deposit depositNonnegative


def margin : ℝ := min forfeit (deposit alice) - reward -
  (1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) * (forfeit + deposit alice)

/-- The repaired current law is a genuine whole behavioral-policy deviation.
It improves only the nongenuine branches and retains every genuine alias. -/
theorem opening_regret
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    margin weight reward forfeit deposit *
        ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
          {response | ¬ GenuineResponse weight nonnegative decision response}).toReal ≤
      (context weight nonnegative site reward forfeit deposit assessment).value
        (openingPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy alice) := by
  classical
  let belief := assessment.belief alice site
  let actions := responseLaw weight nonnegative site (assessment.strategy alice)
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  let recover := decisionOfInformation weight nonnegative site representative decision current
  let utility := aliceUtility reward forfeit deposit
  let row := fun pair :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action => expect
    (continuation weight nonnegative (recover pair.1) pair.2 players) utility
  let repaired := fun pair :
      (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action => (pair.1, repairResponse weight nonnegative decision pair.2)
  let joint := belief.bind fun history => actions.map fun response => (history, response)
  let bad : Set
      ((LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1 ×
        app.Action) := {pair | ¬ GenuineResponse weight nonnegative decision pair.2}
  let indicator := fun pair =>
    @ite ℝ (pair ∈ bad) (Classical.propDecidable _) 1 0
  have constantNonnegative : 0 ≤ reward + forfeit + deposit alice := by positivity
  have bound : ∀ final, |utility final| ≤ reward + forfeit + deposit alice := by
    intro final
    obtain ⟨lower, upper⟩ := aliceUtility_bounds rewardNonnegative forfeitNonnegative
      deposit depositNonnegative final
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have rowBound : ∀ pair, |row pair| ≤ reward + forfeit + deposit alice := by
    intro pair
    exact expect_abs_le_of_bounded constantNonnegative bound
  have domination : ∀ pair,
      row pair + margin weight reward forfeit deposit * indicator pair ≤
        row (repaired pair) := by
    intro pair
    by_cases genuine : GenuineResponse weight nonnegative decision pair.2
    · simp [indicator, bad, repaired, repairResponse, genuine]
    · have nongenuine := (genuine_of_information weight nonnegative site representative
        decision current pair.1 pair.2).not.mpr genuine
      have facts := decisionOfInformation_spec weight nonnegative site representative decision
        current pair.1
      have lower := continuation_opening_lower weight nonnegative reward forfeit deposit positive
        (recover pair.1)
        (disclosureSubmission (.opening aliceEvent
          aliceCandidate ⟨.bool, (recover pair.1).bit⟩))
        (LateOpeningRuntimeAliceOpeningContinuation.canonical_emits_opening
          weight nonnegative (recover pair.1)) players rewardNonnegative forfeitNonnegative
            depositNonnegative
      change -(1 - LateOpeningRuntimeLateAcceptance.inclusionProbability weight) *
          (forfeit + deposit alice) ≤
        row (pair.1, LateOpeningRuntimeLatePrefix.opening (recover pair.1).bit) at lower
      have sameBit : decision.bit = (recover pair.1).bit := facts.2.2.2
      simp only [indicator, bad, Set.mem_ofPred_eq, genuine, not_false_eq_true, ↓reduceIte,
        mul_one, repaired, repairResponse]
      have upper : row pair ≤ reward - min forfeit (deposit alice) := by
        rcases pair with ⟨history, ⟨transmission⟩⟩
        cases transmission with
        | none =>
            have silent := continuation_silence_upper weight nonnegative reward forfeit deposit
              (recover history) players rewardNonnegative forfeitNonnegative depositNonnegative
            exact silent.trans (sub_le_sub_left (min_le_left _ _) reward)
        | some submission =>
            change ¬ LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening
              weight nonnegative (recover history) submission at nongenuine
            have raw := LateOpeningRuntimeAliceOpeningIncentive.nongenuine_payoff_upper
              weight nonnegative (recover history) submission nongenuine players
                rewardNonnegative forfeitNonnegative deposit depositNonnegative
            exact raw.trans (sub_le_sub_left (min_le_right _ _) reward)
      rw [← sameBit] at lower
      dsimp only [margin]
      linarith
  have indicatorIntegrable : PayoffIntegrable joint indicator :=
    payoffIntegrable_ite_one_zero joint (· ∈ bad)
  have scaledIntegrable : PayoffIntegrable joint
      (fun pair => margin weight reward forfeit deposit * indicator pair) :=
    payoffIntegrable_const_mul indicatorIntegrable
  have augmentedIntegrable : PayoffIntegrable joint
      (fun pair => row pair + margin weight reward forfeit deposit * indicator pair) :=
    payoffIntegrable_add (payoffIntegrable_of_bounded _ _ rowBound) scaledIntegrable
  have inequality := expect_mono (μ := joint) (fun pair _ => domination pair)
    augmentedIntegrable
    (payoffIntegrable_of_bounded _ _ (fun pair => rowBound (repaired pair)))
  rw [expect_add (payoffIntegrable_of_bounded _ _ rowBound) scaledIntegrable,
    expect_const_mul] at inequality
  have indicatorMean : expect joint indicator = (joint.toOuterMeasure bad).toReal :=
    expect_indicator joint bad
  rw [indicatorMean] at inequality
  have marginal : joint.map Prod.snd = actions := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    change actions.map id = actions
    exact PMF.map_id actions
  have mass : (joint.toOuterMeasure bad).toReal =
      (actions.toOuterMeasure {response |
        ¬ GenuineResponse weight nonnegative decision response}).toReal := by
    rw [← marginal, PMF.toOuterMeasure_map_apply]
    rfl
  have rawMean : expect joint row = expect
      (finalLaw weight nonnegative site representative decision current assessment
        (assessment.strategy alice)) utility := by
    rw [expect_bind_tower_bounded belief _ _ rowBound]
    unfold finalLaw
    rw [expect_bind_tower_bounded _ _ _ bound]
    apply expect_congr_on_support
    intro history _
    rw [expect_map, expect_bind_tower_bounded _ _ _ bound]
    rfl
  have repairedMean : expect joint (fun pair => row (repaired pair)) = expect
      (finalLaw weight nonnegative site representative decision current assessment
        (openingPolicy weight nonnegative site representative decision current assessment))
        utility := by
    rw [expect_bind_tower_bounded belief _ _ (fun pair => rowBound (repaired pair))]
    unfold finalLaw
    rw [repaired_responseLaw, expect_bind_tower_bounded _ _ _ bound]
    apply expect_congr_on_support
    intro history _
    rw [expect_map, expect_bind_tower_bounded _ _ _ bound, expect_map]
    rfl
  rw [mass, rawMean, repairedMean] at inequality
  rw [context_value weight nonnegative site representative decision current,
    context_value weight nonnegative site representative decision current]
  linarith

include representative decision current in
theorem rational_nongenuine_response_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | ¬ GenuineResponse weight nonnegative decision response}).toReal = 0 := by
  have comparison := (Context.isLocallyOptimal_iff_of_integrable
    (context_integrable weight nonnegative site reward forfeit deposit rewardNonnegative
      forfeitNonnegative depositNonnegative assessment (assessment.strategy alice))
    (fun alternative _ => context_integrable weight nonnegative site reward forfeit deposit
      rewardNonnegative forfeitNonnegative depositNonnegative assessment alternative)).mp rational
        (openingPolicy weight nonnegative site representative decision current assessment)
        (Set.mem_univ _)
  have regret := opening_regret weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      assessment
  have nonnegative := ENNReal.toReal_nonneg (a :=
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | ¬ GenuineResponse weight nonnegative decision response}))
  nlinarith

include representative decision current in
theorem sequentially_rational_nongenuine_response_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | ¬ GenuineResponse weight nonnegative decision response}).toReal = 0 := by
  apply rational_nongenuine_response_zero weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      marginPositive assessment
  have localRational := rational alice site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

include representative decision current in
theorem equilibrium_nongenuine_response_zero
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | ¬ GenuineResponse weight nonnegative decision response}).toReal = 0 :=
  sequentially_rational_nongenuine_response_zero weight nonnegative site representative decision
    current reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      marginPositive assessment equilibrium.1


/-- Approximate optimality of the same attainable repair bounds the probability
of nongenuine responses, without changing the equilibrium definition. -/
theorem nongenuine_le_of_deviation_regret
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < margin weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (epsilon : ℝ)
    (regret : (context weight nonnegative site reward forfeit deposit assessment).value
        (openingPolicy weight nonnegative site representative decision current assessment) -
      (context weight nonnegative site reward forfeit deposit assessment).value
        (assessment.strategy alice) ≤ epsilon) :
    ((responseLaw weight nonnegative site (assessment.strategy alice)).toOuterMeasure
      {response | ¬ GenuineResponse weight nonnegative decision response}).toReal ≤
        epsilon / margin weight reward forfeit deposit := by
  apply (le_div_iff₀ marginPositive).mpr
  have bound := opening_regret weight nonnegative site representative decision current
    reward forfeit deposit positive rewardNonnegative forfeitNonnegative depositNonnegative
      assessment
  nlinarith

end Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality
