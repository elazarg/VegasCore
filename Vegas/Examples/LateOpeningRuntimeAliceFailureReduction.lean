/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation

/-! # Observable receiver guesses on omitted-opening branches

The empty receiver transcript determines one actual raw binding law shared
by every initialized bit and private label and by either unseen send time.
At a transcript containing an authentic opening, the unique maximizing
logical guess is the certified bit. No posterior formula is assumed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFailureReduction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance LateOpeningRuntimeBindingObservation
  LateOpeningRuntimeAliceFailureContinuation
open LateOpeningRuntimeBobRawBinding (serviced response_result_same_information)
open LateOpeningRuntimeBobBindingDecision (bitGuess context)
open LateOpeningRuntimeEarlyBobSafeMenu (answerFinitePolicy)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def bindingLaw (players : Player → app.Policy) (execution : app.Execution) :
    PMF (Option (PublicationResult Answer)) :=
  (players bob (execution.recall bob) (execution.observe app bob)).map
    (fun response => (serviced execution response).application.config.store (.inr bobBindEvent))

/-- Equal native receiver information gives the same actual immediate
logical binding law for every raw response, including malformed aliases. -/
theorem bindingLaw_same_information (players : Player → app.Policy)
    (first second : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative)
    (same : bobInformation first.execution = bobInformation second.execution) :
    bindingLaw players first.execution = bindingLaw players second.execution := by
  have recalled : first.execution.recall bob = second.execution.recall bob :=
    congrArg Prod.fst same
  have viewed : first.execution.observe app bob = second.execution.observe app bob :=
    congrArg Prod.snd same
  have results : (fun response : app.Action =>
      (serviced first.execution response).application.config.store (.inr bobBindEvent)) =
      fun response => (serviced second.execution response).application.config.store
        (.inr bobBindEvent) := by
    funext response
    exact response_result_same_information weight nonnegative first second recalled viewed response
  unfold bindingLaw
  rw [recalled, viewed, results]

def emptyBindingLaw (players : Player → app.Policy) : PMF (Option (PublicationResult Answer)) :=
  bindingLaw players (failedAnswerDecision false 0 0 false false)

include weight nonnegative in
/-- The empty transcript's receiver law is independent of Alice's private
label, immutable bit, and which late callback emitted the omitted opening. -/
theorem failed_empty_binding_law (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) :
    bindingLaw players (failedAnswerDecision bit label slot false false) =
      emptyBindingLaw players := by
  apply bindingLaw_same_information weight nonnegative players
    (decisionHistory weight nonnegative bit label slot false false (Or.inr rfl))
    (decisionHistory weight nonnegative false 0 0 false false (Or.inl rfl))
  fin_cases slot
  · exact failed_empty_information_inputs bit false label 0
  · exact (failed_unseen_timing_information bit label label false).symm.trans
      (failed_empty_information_inputs bit false label 0)

def emptyTrueProbability (players : Player → app.Policy) : ℝ :=
  ((emptyBindingLaw players) (some (.success (bitGuess true)))).toReal

theorem emptyTrueProbability_mem_Icc (players : Player → app.Policy) :
    emptyTrueProbability players ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, pmf_toReal_apply_le_one _ _⟩

/-- Either native pending sample can provide the original opening
certificate; its permanent absence from the ledger does not erase it. -/
theorem failed_observes_bit (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool)
    (seen : finalSeen = true ∨ (earlySeen = true ∧ slot.val = 0)) :
    LateOpeningRuntimeBobKnownBit.ObservesBit
      ((failedAnswerDecision bit label slot earlySeen finalSeen).observe app bob) bit := by
  refine ⟨aliceCandidate, ?_, ?_⟩
  · change (failedAnswerDecision bit label slot earlySeen finalSeen).application.accepted
      aliceBinding.field = some aliceCandidate
    rw [failedAnswerDecision_physical]
    rfl
  · change (⟨aliceCandidate, ⟨.bool, bit⟩⟩ : OpeningFact nativeGraph) ∈
      List.flatMap (fun message : Message Player app.Payload => message.payload.evidence.toList)
        (((failedAnswerDecision bit label slot earlySeen finalSeen).network.observe bob).leaked ++
          ((failedAnswerDecision bit label slot earlySeen finalSeen).network.observe bob).ledger)
    rw [failedAnswerDecision_network, ite_eq_left seen]
    simp [openingMessage]

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include representative decision current in
theorem opposite_guess_value_zero (bit : Bool)
    (observed : LateOpeningRuntimeBobKnownBit.ObservesBit
      (decision.execution.observe app bob) bit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative (bitGuess (!bit))) = 0 := by
  have total := LateOpeningRuntimeBobBindingDecision.bit_guess_context_values_sum weight
    nonnegative site representative decision current reward forfeit deposit assessment
  have correct := LateOpeningRuntimeBobKnownBit.correct_guess_context_value weight nonnegative
    site representative decision current reward forfeit deposit bit observed assessment
  cases bit <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

include representative decision current in
/-- An authentic opening makes the current logical guess unique throughout
the complete receiver information class, not just on positive belief support. -/
theorem rational_supported_known_binding (bit : Bool)
    (observed : LateOpeningRuntimeBobKnownBit.ObservesBit
      (decision.execution.observe app bob) bit)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (LateOpeningRuntimeBobBindingOptimization.currentResponses
      weight nonnegative decision assessment).support) :
    (serviced decision.execution response).application.config.store (.inr bobBindEvent) =
      some (.success (bitGuess bit)) := by
  obtain ⟨_, answer, _, _, selected, ⟨guessed, answerEq⟩, maximizing, _, _, _⟩ :=
    LateOpeningRuntimeBobFailedBindingClean.rational_supported_clean_binding weight nonnegative
      site representative decision current reward forfeit deposit forfeitPositive depositPositive
        assessment rational response supported
  have same : guessed = bit := by
    by_contra different
    have opposite : guessed = !bit := by
      cases guessed <;> cases bit <;> first | rfl | exact (different rfl).elim
    have zero := opposite_guess_value_zero weight nonnegative site representative decision current
      reward forfeit deposit bit observed assessment
    rw [answerEq, opposite, zero] at maximizing
    have positive := LateOpeningRuntimeBobBindingOptimization.bestGuessValue_ge_half weight
      nonnegative site representative decision current reward forfeit deposit assessment
    linarith
  rwa [answerEq, same] at selected

omit site representative decision current in
/-- On a certificate-bearing actual failure branch, the original receiver
current law fixes the correct bit with certainty across every raw alias. -/
theorem rational_known_binding_law
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (samplePossible : slot = 0 ∨ earlySeen = false)
    (seen : finalSeen = true ∨ (earlySeen = true ∧ slot.val = 0))
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob) :
    bindingLaw players (failedAnswerDecision bit label slot earlySeen finalSeen) =
      PMF.pure (some (.success (bitGuess bit))) := by
  let decision := decisionHistory weight nonnegative bit label slot earlySeen finalSeen
    samplePossible
  obtain ⟨boundedTrace⟩ := LateOpeningRuntimeBindingObservationWitness.failedAnswerDecision_trace
    weight nonnegative bit label slot earlySeen finalSeen samplePossible
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨14, some bob, decision.execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (14 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeNash.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨14, some bob, decision.execution⟩ := rfl
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨response, selected, rfl⟩ := PMF.support_map .. ▸ supported
  have currentSupported : response ∈ (LateOpeningRuntimeBobBindingOptimization.currentResponses
      weight nonnegative decision assessment).support := by
    rw [bobPolicy] at selected
    exact selected
  exact rational_supported_known_binding weight nonnegative site representative decision current
    reward forfeit deposit bit (failed_observes_bit bit label slot earlySeen finalSeen seen)
      forfeitPositive depositPositive assessment localRational response currentSupported

omit site representative decision current in
theorem receiver_known_expected_value
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (samplePossible : slot = 0 ∨ earlySeen = false)
    (seen : finalSeen = true ∨ (earlySeen = true ∧ slot.val = 0))
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob) :
    expect (LateOpeningRuntimeSettlementContinuation.receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot earlySeen finalSeen))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
      failureValue reward label (bitGuess bit) - forfeit - deposit alice := by
  rw [receiver_expected_value weight nonnegative bit label slot earlySeen finalSeen samplePossible
    reward forfeit deposit rewardNonnegative forfeitPositive aliceDepositNonnegative
      bobDepositPositive assessment rational players bobPolicy]
  have mapped : expect (bindingLaw players
      (failedAnswerDecision bit label slot earlySeen finalSeen))
      (failureBindingValue reward label) =
      expect (players bob ((failedAnswerDecision bit label slot earlySeen finalSeen).recall bob)
        ((failedAnswerDecision bit label slot earlySeen finalSeen).observe app bob))
        (fun response => failureBindingValue reward label
          ((serviced (failedAnswerDecision bit label slot earlySeen finalSeen)
            response).application.config.store (.inr bobBindEvent))) := expect_map _ _ _
  rw [← mapped, rational_known_binding_law weight nonnegative reward forfeit deposit bit label slot
    earlySeen finalSeen samplePossible seen forfeitPositive bobDepositPositive assessment rational
      players bobPolicy, expect_pure]
  rfl

omit site representative decision current in
/-- An omitted opening missed by both samples uses the same actual
receiver binding distribution at every hidden type and either late time. -/
theorem receiver_empty_expected_value
    (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob) :
    expect (LateOpeningRuntimeSettlementContinuation.receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot false false))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
      expect (emptyBindingLaw players) (failureBindingValue reward label) -
        forfeit - deposit alice := by
  rw [receiver_expected_value weight nonnegative bit label slot false false (Or.inr rfl)
    reward forfeit deposit rewardNonnegative forfeitPositive aliceDepositNonnegative
      bobDepositPositive assessment rational players bobPolicy]
  have mapped : expect (bindingLaw players (failedAnswerDecision bit label slot false false))
      (failureBindingValue reward label) =
      expect (players bob ((failedAnswerDecision bit label slot false false).recall bob)
        ((failedAnswerDecision bit label slot false false).observe app bob))
        (fun response => failureBindingValue reward label
          ((serviced (failedAnswerDecision bit label slot false false)
            response).application.config.store (.inr bobBindEvent))) := expect_map _ _ _
  rw [← mapped, failed_empty_binding_law weight nonnegative players bit label slot]

omit site representative decision current in
theorem empty_false_probability
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob) :
    ((emptyBindingLaw players) (some (.success (bitGuess false)))).toReal =
      1 - emptyTrueProbability players := by
  classical
  let law := emptyBindingLaw players
  let left : Option (PublicationResult Answer) → ℝ :=
    fun result => if some (.success (bitGuess true)) = result then 1 else 0
  let right : Option (PublicationResult Answer) → ℝ :=
    fun result => if some (.success (bitGuess false)) = result then 1 else 0
  have support : ∀ result ∈ law.support,
      result = some (.success (bitGuess false)) ∨ result = some (.success (bitGuess true)) := by
    intro result present
    obtain ⟨response, selected, rfl⟩ := PMF.support_map .. ▸ present
    obtain ⟨answer, bound, ⟨guessed, answerEq⟩, _⟩ := rational_response_payoff weight nonnegative
      false 0 0 false false (Or.inl rfl) reward forfeit deposit forfeitPositive depositPositive
        assessment rational players bobPolicy response selected
    have chosen := bound.trans
      (congrArg (fun actual : Answer => some (PublicationResult.success actual)) answerEq)
    cases guessed
    · exact Or.inl chosen
    · exact Or.inr chosen
  have leftIntegrable : PayoffIntegrable law left := payoffIntegrable_ite_one_zero law _
  have rightIntegrable : PayoffIntegrable law right := payoffIntegrable_ite_one_zero law _
  have leftValue : expect law left = emptyTrueProbability players := by
    simpa only [left, emptyTrueProbability, law, mul_one] using
      expect_ite_eq law (some (.success (bitGuess true))) (1 : ℝ)
  have rightValue : expect law right =
      ((emptyBindingLaw players) (some (.success (bitGuess false)))).toReal := by
    simpa only [right, law, mul_one] using
      expect_ite_eq law (some (.success (bitGuess false))) (1 : ℝ)
  have total : emptyTrueProbability players +
      ((emptyBindingLaw players) (some (.success (bitGuess false)))).toReal = 1 := by
    rw [← leftValue, ← rightValue, ← expect_add leftIntegrable rightIntegrable]
    calc
      _ = expect law (fun _ => (1 : ℝ)) := by
        apply expect_congr_on_support
        intro result present
        rcases support result present with rfl | rfl <;> norm_num [left, right, bitGuess]
      _ = _ := expect_constant _ _
  linarith

omit weight nonnegative site representative decision current reward forfeit deposit in
theorem failureBindingValue_zero (reward : ℝ) (binding : Option (PublicationResult Answer)) :
    failureBindingValue reward 0 binding =
      if some (.success (bitGuess true)) = binding then reward else 0 := by
  classical
  cases binding with
  | none => simp [failureBindingValue]
  | some binding =>
      cases binding with
      | failure => simp [failureBindingValue]
      | success answer =>
          simp [failureBindingValue, failureValue, bitGuess, Subtype.ext_iff, eq_comm]

omit weight nonnegative site representative decision current reward forfeit deposit in
theorem failureBindingValue_one (reward : ℝ) (binding : Option (PublicationResult Answer)) :
    failureBindingValue reward 1 binding =
      if some (.success (bitGuess false)) = binding then reward else 0 := by
  classical
  cases binding with
  | none => simp [failureBindingValue]
  | some binding =>
      cases binding with
      | failure => simp [failureBindingValue]
      | success answer =>
          simp [failureBindingValue, failureValue, bitGuess, Subtype.ext_iff, eq_comm]

omit weight nonnegative site representative decision current reward forfeit deposit in
theorem failureBindingValue_two (reward : ℝ) (binding : Option (PublicationResult Answer)) :
    failureBindingValue reward 2 binding = 0 := by
  cases binding with
  | none => rfl
  | some binding => cases binding <;> simp [failureBindingValue, failureValue]

omit site representative decision current in
/-- The single actual empty-transcript probability gives the complete
sender payoff table for all three private labels and both initialized bits. -/
theorem receiver_empty_expected_value_closed
    (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (rewardNonnegative : 0 ≤ reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobDepositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob) :
    expect (LateOpeningRuntimeSettlementContinuation.receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot false false))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
      (if label.val = 0 then emptyTrueProbability players * reward
        else if label.val = 1 then (1 - emptyTrueProbability players) * reward else 0) -
          forfeit - deposit alice := by
  classical
  rw [receiver_empty_expected_value weight nonnegative reward forfeit deposit bit label slot
    rewardNonnegative forfeitPositive aliceDepositNonnegative bobDepositPositive assessment rational
      players bobPolicy]
  fin_cases label
  · have score : failureBindingValue reward (0 : Fin 3) = fun binding =>
        if some (.success (bitGuess true)) = binding then reward else 0 :=
      funext (failureBindingValue_zero reward)
    change expect (emptyBindingLaw players) (failureBindingValue reward (0 : Fin 3)) -
      forfeit - deposit alice = emptyTrueProbability players * reward - forfeit - deposit alice
    rw [score, expect_ite_eq]
    rfl
  · have score : failureBindingValue reward (1 : Fin 3) = fun binding =>
        if some (.success (bitGuess false)) = binding then reward else 0 :=
      funext (failureBindingValue_one reward)
    change expect (emptyBindingLaw players) (failureBindingValue reward (1 : Fin 3)) -
      forfeit - deposit alice =
        (1 - emptyTrueProbability players) * reward - forfeit - deposit alice
    rw [score, expect_ite_eq, empty_false_probability weight nonnegative reward forfeit deposit
      forfeitPositive bobDepositPositive assessment rational players bobPolicy]
  · have score : failureBindingValue reward (2 : Fin 3) = fun _ => (0 : ℝ) :=
      funext (failureBindingValue_two reward)
    change expect (emptyBindingLaw players) (failureBindingValue reward (2 : Fin 3)) -
      forfeit - deposit alice = 0 - forfeit - deposit alice
    rw [score, expect_constant]

end Vegas.Examples.LateOpeningRuntimeAliceFailureReduction
