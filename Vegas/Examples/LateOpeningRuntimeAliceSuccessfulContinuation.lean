/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor
import Vegas.Examples.LateOpeningRuntimeSettlementContinuation
import Vegas.Examples.LateOpeningRuntimeAliceIncentive

/-! # Exact sender value after accepted single-opening inclusion

Alice's accepted opening is her sole signed packet. The remaining runtime
never invokes Alice again, so arbitrary receiver responses preserve zero
sender audit charge. Under the original rational receiver policy, every
supported logical answer is published. Sender value is therefore exactly
the source successful-answer score of the actual immediate binding law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLateHistories
  LateOpeningRuntimeUtility LateOpeningRuntimeAliceContinuation
open LateOpeningRuntimeBobRawBinding (serviced)
open LateOpeningRuntimeSettlementContinuation (receiverCompletion)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def decisionHistory (positive : 0 < weight) (bit : Bool) (label : Fin 3)
    (slot : Fin 2) (seen : Bool) (samplePossible : slot = 0 ∨ seen = false) :
    LateOpeningRuntimeBobSuccessInformation.DecisionHistory weight nonnegative where
  execution := answerDecision bit label slot seen
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (answerDecision_trace weight nonnegative positive bit label slot seen samplePossible).some
  quiet := by
    intro entry member
    rw [answerDecision_bobRecall] at member
    fin_cases slot
    · change entry ∈ (bobObserved bit label 0 seen).recall bob at member
      rw [bobObserved_first_recall] at member
      cases List.mem_singleton.mp member
      rfl
    · have noSeen : seen = false := samplePossible.resolve_left (by decide)
      rw [noSeen] at member
      change entry ∈ (bobObserved bit label 1 false).recall bob at member
      rw [bobObserved_second_recall] at member
      cases List.mem_singleton.mp member
      rfl
  bit := bit
  published := by
    rw [answerDecision_physical]
    exact openedPhysical_bit bit label
  ready := LateOpeningRuntimeBobSuffix.answer_ready bit label slot seen
  timely := by
    rw [answerDecision_physical]
    change 3 - 2 < 3
    decide

private theorem onlyAlice_after_response (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (seen : Bool) (response : app.Action) :
    OnlyAlicePacket bit ((answerDecision bit label slot seen).respond app bob response) := by
  have only : OnlyAlicePacket bit (answerDecision bit label slot seen) := by
    intro message member _
    rw [LateOpeningRuntimeBobSuffix.answer_inputs] at member
    exact List.mem_singleton.mp member
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact only
  | some material =>
      intro message member authored
      change message ∈ (answerDecision bit label slot seen).network.inputs ++ [_] at member
      rcases List.mem_append.mp member with old | fresh
      · exact only message old authored
      · cases List.mem_singleton.mp fresh
        exact (show bob ≠ alice by decide) authored |>.elim

/-- Any raw receiver continuation preserves the accepted sender singleton;
zero sender charge does not require receiver rationality or clean traffic. -/
theorem continuation_charge_zero (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (response : app.Action)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 ((answerDecision bit label slot seen).respond app bob response)).support)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample)
        (app.finished final) alice = 0 := by
  let first := (answerDecision bit label slot seen).respond app bob response
  have quietLaw : app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (quietAgainst players) 14 first = app.runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) players 14 first := by
    apply app.continuation_policy_independent_of_unactivated
      (LateOpeningRuntimeService.scheduler weight nonnegative) 8 alice
        (LateOpeningRuntimeAliceIncentive.alice_absent weight nonnegative)
        (quietAgainst players) players
    · intro who different
      exact ite_eq_right different
    · change 8 ≤ (answerDecision bit label slot seen).environmentRecall.length
      change 8 ≤ 12
      decide
  have quietReached := quietLaw.symm ▸ reached
  have only := (quiet_onlyAlicePacket bit players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 first final
      (onlyAlice_after_response bit label slot seen response) quietReached
  obtain ⟨boundedTrace⟩ := answerDecision_trace weight nonnegative positive bit label slot seen
    samplePossible
  have rawTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ bob response rawTrace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 first final respondedTrace
      reached
  have initialReceipt : ((alice, 0), true) ∈ first.receipts :=
    acceptedLottery_receipt bit label slot seen
  have receipt := (app.receipt_policyInvariant players ((alice, 0), true)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 first final initialReceipt reached
  apply alice_audit_charge_zero sample authentic ⟨0, none, final⟩
  intro traffic member owner
  have input : traffic.envelope ∈ final.network.inputs := by
    have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) finalTrace
    change (app.executionTraffic final).map ReactiveApplication.TrafficRecord.envelope =
      final.network.inputs at inputs
    rw [← inputs]
    exact List.mem_map.mpr ⟨traffic, member, rfl⟩
  rw [only traffic.envelope input owner]
  exact accepted_alice_opening_permitted _ (alice, 0) bit (some ⟨aliceEvent⟩) receipt

def successfulValue (reward : ℝ) (label : Fin 3) (answer : Answer) : ℝ :=
  if answer.val = 0 then reward / 2
  else if 1 ≤ answer.val ∧ answer.val ≤ 3 ∧ label.val < 2 then reward else 0

def successfulBindingValue (reward : ℝ) (label : Fin 3) :
    Option (PublicationResult Answer) → ℝ
  | some (.success answer) => successfulValue reward label answer
  | _ => 0

theorem sourceUtility_successfulValue (reward forfeit : ℝ) (bit publishedBit : Bool)
    (label : Fin 3) (binding : PublicationResult Answer) (answer : Answer) :
    sourceUtility reward forfeit
      (terminalStateOf bit label (.success publishedBit) binding (.success answer)) alice =
        successfulValue reward label answer := by
  rw [sourceUtility_alice, parameterOutcome_terminalStateOf]
  change successfulValue reward label answer - 0 = successfulValue reward label answer
  exact sub_zero _

/-- Once the actual chosen answer is published, sender native payoff equals
its source successful-opening score under every authentic audit sample. -/
theorem continuation_payoff_of_publication (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (response : app.Action)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 ((answerDecision bit label slot seen).respond app bob response)).support)
    (answer : Answer)
    (published : final.application.config.store (.inr bobRevealEvent) = some (.success answer))
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) alice =
      successfulValue reward label answer := by
  let decision := decisionHistory weight nonnegative positive bit label slot seen samplePossible
  obtain ⟨actualBit, actualLabel, binding, publication, _, labelEq, _, _, stored, readout⟩ :=
    LateOpeningRuntimeBobSuccessPayoff.continuation_readout weight nonnegative
      decision.execution decision.trace decision.bit
      decision.published response
      players final reached
  have actualLabelEq : actualLabel = label := by
    rw [← labelEq]
    change LateOpeningRuntimeBobSuccessPayoff.originalLabel
      (answerDecision bit label slot seen) = label
    apply Fin.ext
    change Int.toNat
      ((answerDecision bit label slot seen).application.config.inputs labelInput : Label).val =
        label.val
    rw [answerDecision_physical]
    rfl
  have publicationEq := Option.some.inj (stored.symm.trans published)
  subst publication
  have clear := continuation_charge_zero weight nonnegative positive bit label slot seen
    samplePossible response players final reached sample authentic
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [clear, zero_mul, sub_zero, nativeBaseUtility_of_readout reward forfeit _ _ readout alice,
    sourceUtility_successfulValue, actualLabelEq]

/-- Every supported first-binding response of the rational native policy
has its exact successful-opening sender value on all physical branches. -/
theorem rational_response_payoff (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (response : app.Action)
    (supported : response ∈ (players bob ((answerDecision bit label slot seen).recall bob)
      ((answerDecision bit label slot seen).observe app bob)).support) :
    ∃ answer : Answer,
      (serviced (answerDecision bit label slot seen) response).application.config.store
        (.inr bobBindEvent) = some (.success answer) ∧
      (answer = safe ∨ ∃ guessed : Fin 3,
        answer = LateOpeningRuntimeBobSuccessDecision.labelGuess guessed) ∧
      ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14
        ((answerDecision bit label slot seen).respond app bob response)).support,
        LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
          deposit (app.finished final) alice = successfulValue reward label answer := by
  let decision := decisionHistory weight nonnegative positive bit label slot seen samplePossible
  obtain ⟨boundedTrace⟩ := answerDecision_trace weight nonnegative positive bit label slot seen
    samplePossible
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
  have currentSupported : response ∈ (LateOpeningRuntimeBobSuccessOptimization.currentResponses
      weight nonnegative decision assessment).support := by
    rw [bobPolicy] at supported
    exact supported
  obtain ⟨material, answer, responseEq, packet, selected, shape, _, _, _, _⟩ :=
    LateOpeningRuntimeBobSuccessBindingClean.rational_supported_clean_binding weight nonnegative
      site representative decision current reward forfeit deposit forfeitPositive depositPositive
        assessment localRational response currentSupported
  refine ⟨answer, selected, shape, ?_⟩
  intro final reached
  have available := rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob (assessment.strategy bob)
      _ _ response currentSupported
  rw [responseEq] at available selected reached
  have published := LateOpeningRuntimeBobDisclosurePublication.binding_publication weight
    nonnegative reward forfeit deposit assessment decision.execution boundedTrace decision.quiet
      decision.ready material answer available selected packet forfeitPositive depositPositive
        rational players bobPolicy final reached
  apply continuation_payoff_of_publication weight nonnegative positive bit label slot seen
    samplePossible response players final _ answer published reward forfeit deposit
      (fun actual => PMF.pure actual)
      (by
        intro actual observed present
        cases (PMF.mem_support_pure_iff _ _).mp present
        exact List.Subset.refl _)
  rwa [responseEq]

theorem successfulBindingValue_abs_le (reward : ℝ) (rewardNonnegative : 0 ≤ reward)
    (label : Fin 3) (binding : Option (PublicationResult Answer)) :
    |successfulBindingValue reward label binding| ≤ reward := by
  cases binding with
  | none => simpa only [successfulBindingValue, abs_zero] using rewardNonnegative
  | some binding =>
      cases binding with
      | failure => simpa only [successfulBindingValue, abs_zero] using rewardNonnegative
      | success answer =>
          change |successfulValue reward label answer| ≤ reward
          unfold successfulValue
          split
          · rw [abs_of_nonneg (by positivity)]
            linarith
          · split
            · exact le_of_eq (abs_of_nonneg rewardNonnegative)
            · simpa only [abs_zero] using rewardNonnegative

/-- Exact expected sender value is evaluated from the original current raw
response law and its actual immediate logical binding result. -/
theorem receiver_expected_value (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
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
    expect (receiverCompletion weight nonnegative players (answerDecision bit label slot seen))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) =
    expect (players bob ((answerDecision bit label slot seen).recall bob)
      ((answerDecision bit label slot seen).observe app bob)) (fun response =>
        successfulBindingValue reward label
          ((serviced (answerDecision bit label slot seen) response).application.config.store
            (.inr bobBindEvent))) := by
  unfold receiverCompletion ReactiveApplication.invoke
  rw [PMF.bind_map]
  have integrable : PayoffIntegrable
      ((players bob ((answerDecision bit label slot seen).recall bob)
        ((answerDecision bit label slot seen).observe app bob)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 14 ∘
          (answerDecision bit label slot seen).respond app bob))
      (fun final => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice) :=
    aliceUtility_integrable rewardNonnegative forfeitPositive.le deposit aliceDepositNonnegative _
  rw [expect_bind_tower _ _ _ integrable]
  apply expect_congr_on_support
  intro response supported
  obtain ⟨answer, selected, _, exactValue⟩ := rational_response_payoff weight nonnegative positive
    bit label slot seen samplePossible reward forfeit deposit forfeitPositive bobDepositPositive
      assessment rational players bobPolicy response supported
  rw [selected]
  change _ = successfulValue reward label answer
  calc
    _ = expect _ (fun _ => successfulValue reward label answer) :=
      expect_congr_on_support exactValue
    _ = _ := expect_constant _ _

end Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation
