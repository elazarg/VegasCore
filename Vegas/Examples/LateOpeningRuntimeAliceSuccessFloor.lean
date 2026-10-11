/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit
import Vegas.Examples.LateOpeningRuntimeGame
import Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement

/-! # Sender payoff bounds by immutable private label

For the third label, every source result has gross reward at most half.
For either of Alice's first two labels, successful Safe or label answers give
at least half of her reward. Her own runtime audit deduction is retained
explicitly: optimal Bob settlement alone does not certify Alice's traffic.
The assessment conclusion concerns positive belief and physical support.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSuccessPayoff LateOpeningRuntimeBobSuccessDecision
  LateOpeningRuntimeBobSuccessOptimization LateOpeningRuntimeBobSuccessSettlement
open LateOpeningRuntimeBobBindingDecision (context)

theorem grossUtility_highLabel_upper (reward : ℝ) (nonnegative : 0 ≤ reward)
    (result : Parameter × PublicOutcome program) (high : 2 ≤ result.1.2.val) :
    grossUtility reward result alice ≤ reward / 2 := by
  have notLow : ¬ result.1.2.val < 2 := by omega
  have notZero : result.1.2.val ≠ 0 := by omega
  have notOne : result.1.2.val ≠ 1 := by omega
  unfold grossUtility
  cases answer : bobResult result.2 with
  | failure => linarith
  | success opened =>
      simp only [ite_true]
      by_cases published : (aliceResult result.2).isSuccess
      · rw [ite_eq_left published]
        by_cases safe : opened.val = 0
        · rw [ite_eq_left safe]
        · rw [ite_eq_right safe, ite_eq_right (by simp only [notLow, and_false, not_false_eq_true])]
          linarith
      · rw [ite_eq_right published]
        simp only [notZero, notOne, false_and, or_self, ite_false]
        linarith


/-- Alice cannot receive more than half the reward at the third label;
failed opening forfeits can only reduce that amount. -/
theorem sourceUtility_highLabel_upper (reward forfeit : ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (terminal : State simpleExpr program.terminalCtx)
    (high : 2 ≤ (setup.parameterOutcome parameter terminal).1.2.val) :
    sourceUtility reward forfeit terminal alice ≤ reward / 2 := by
  have upper := grossUtility_highLabel_upper reward rewardNonnegative
    (setup.parameterOutcome parameter terminal) high
  rw [sourceUtility_alice]
  split_ifs <;> linarith

theorem sourceUtility_floor (reward forfeit : ℝ) (rewardNonnegative : 0 ≤ reward)
    (bit publishedBit : Bool) (label : Fin 3) (labelLow : label.val < 2)
    (binding : PublicationResult Answer) (answer : Answer)
    (shape : answer = safe ∨ ∃ guessed : Fin 3, answer = labelGuess guessed) :
    reward / 2 ≤ sourceUtility reward forfeit
      (terminalStateOf bit label (.success publishedBit) binding (.success answer)) alice := by
  rw [sourceUtility_alice, parameterOutcome_terminalStateOf]
  change reward / 2 ≤ (if answer.val = 0 then reward / 2
    else if 1 ≤ answer.val ∧ answer.val ≤ 3 ∧ label.val < 2 then reward else 0) - 0
  rcases shape with rfl | ⟨guessed, rfl⟩
  · simp only [show safe.val = 0 from rfl, ↓reduceIte, sub_zero]
    exact le_refl _
  · have guessedBound := guessed.isLt
    have nonzero : (labelGuess guessed).val ≠ 0 := by dsimp only [labelGuess]; omega
    have within : 1 ≤ (labelGuess guessed).val ∧ (labelGuess guessed).val ≤ 3 := by
      dsimp only [labelGuess]
      constructor <;> omega
    rw [ite_eq_right nonzero, ite_eq_left ⟨within.1, within.2, labelLow⟩, sub_zero]
    linarith

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- Actual sender payoff keeps its own audit deduction, without assuming
that Bob's zero audit charge clears Alice's earlier or later packets. -/
theorem continuation_payoff_floor
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨14, some bob, execution⟩))
    (publishedBit : Bool)
    (publishedAlice : execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool))
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14
      (execution.respond app bob response)).support)
    (answer : Answer)
    (publishedBob : final.application.config.store (.inr bobRevealEvent) = some (.success answer))
    (shape : answer = safe ∨ ∃ guessed : Fin 3, answer = labelGuess guessed)
    (labelLow : (originalLabel execution).val < 2)
    (reward forfeit : ℝ) (rewardNonnegative : 0 ≤ reward) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) :
    reward / 2 - TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation
      leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) (app.finished final) alice *
        deposit alice ≤
      LateOpeningRuntimeGame.payoff reward forfeit sample deposit (app.finished final) alice := by
  obtain ⟨bit, label, binding, publication, _bitEq, labelEq, _reachable,
    _bound, stored, readout⟩ := continuation_readout weight nonnegative execution trace
      publishedBit publishedAlice response players final reached
  have same : publication = PublicationResult.success answer :=
    Option.some.inj (stored.symm.trans publishedBob)
  subst publication
  have low : label.val < 2 := by rwa [← labelEq]
  have floor := LateOpeningRuntimeAliceSuccessFloor.sourceUtility_floor reward forfeit
    rewardNonnegative bit publishedBit label low binding answer shape
  unfold LateOpeningRuntimeGame.payoff TerminalAudit.utility
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout alice]
  linarith

variable
  (site : (LateOpeningRuntimeGame.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- Optimal successful-publication bindings give the sender floor throughout
the actual joint support for her first two immutable private labels. -/
theorem rational_supported_payoff_floor (rewardNonnegative : 0 ≤ reward)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeGame.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (history : (LateOpeningRuntimeGame.model weight nonnegative).InformationHistory bob site.1)
    (believed : history ∈ (assessment.belief bob site).support)
    (labelLow : (originalLabel (decisionOfInformation weight nonnegative site representative
      decision current history).execution).val < 2)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) 14
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob response)).support) :
    reward / 2 - TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) alice * deposit alice ≤
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice := by
  obtain ⟨answer, selected, shape, maximizing, clean⟩ := rational_supported_clean_settlement
    weight nonnegative site representative decision current reward forfeit deposit
      forfeitPositive depositPositive assessment rational response supported
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  exact continuation_payoff_floor weight nonnegative recovered.execution recovered.trace
    recovered.bit recovered.published response _ final reached answer
    (clean history believed final reached).1 shape labelLow reward forfeit rewardNonnegative
      deposit (fun actual => PMF.pure actual)

end Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor

namespace Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeUtility LateOpeningRuntimeLatePrefix

theorem nativeBaseUtility_upper {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (high : 2 ≤ (control.execution.application.config.inputs labelInput).val.toNat) :
    nativeBaseUtility reward forfeit (some control) alice ≤ reward / 2 := by
  have completed := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
    control trace
  obtain ⟨aliceResult, binding, answer, decoded⟩ := terminal_decode_exists
    control.execution.application bit label valid completed
  have readout : serviceSourceReadout setup .sequential deadline leaks (some control) =
      some (terminalStateOf bit label aliceResult binding answer) := by
    unfold serviceSourceReadout
    rw [Option.bind_some, ite_eq_left completed]
    exact decoded
  have labelHigh : 2 ≤ label.val := by
    rw [valid.reachable.inputs_eq] at high
    exact high
  have bound := LateOpeningRuntimeAliceSuccessFloor.sourceUtility_highLabel_upper reward forfeit
    rewardNonnegative forfeitNonnegative (terminalStateOf bit label aliceResult binding answer)
    (by simpa only [parameterOutcome_terminalStateOf] using labelHigh)
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout alice]
  exact bound

theorem nongenuine_envelope_utility_upper {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (high : 2 ≤ (control.execution.application.config.inputs labelInput).val.toNat)
    (bit : Bool)
    (bound : aliceBinding.get? control.execution.application.config.store = some (.success bit))
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice)
    (nongenuine : traffic.envelope.payload ≠ (openingMessage bit).payload) :
    LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (some control) alice ≤ reward / 2 - deposit alice := by
  have base := nativeBaseUtility_upper rewardNonnegative forfeitNonnegative weight nonnegative
    control trace terminal high
  have charged := LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_full_charge weight
    nonnegative control trace terminal bit bound traffic present owner nongenuine
  have penalty := mul_le_mul_of_nonneg_right charged depositNonnegative
  unfold LateOpeningRuntimeGame.payoff TerminalAudit.utility
  linarith

end Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor
