/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement

/-! # Sender payoffs after a successful opening and optimal answer

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
theorem continuation_payoff_floor (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (decision.execution.respond app bob response)).support)
    (answer : Answer)
    (published : final.application.config.store (.inr bobRevealEvent) = some (.success answer))
    (shape : answer = safe ∨ ∃ label : Fin 3, answer = labelGuess label)
    (labelLow : (originalLabel decision.execution).val < 2)
    (reward forfeit : ℝ) (rewardNonnegative : 0 ≤ reward) (deposit : Player → ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) :
    reward / 2 - TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) (app.finished final) alice *
        deposit alice ≤
      LateOpeningRuntimeNash.payoff reward forfeit sample deposit (app.finished final) alice := by
  obtain ⟨bit, label, binding, publication, bitEq, labelEq, reachable,
    bound, stored, readout⟩ := continuation_readout weight nonnegative decision response players
      final reached
  have same : publication = PublicationResult.success answer :=
    Option.some.inj (stored.symm.trans published)
  subst publication
  have low : label.val < 2 := by rwa [← labelEq]
  have floor := sourceUtility_floor reward forfeit rewardNonnegative bit decision.bit label low
    binding answer shape
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [nativeBaseUtility_of_readout reward forfeit _ _ readout alice]
  linarith

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- Optimal successful-publication bindings give the sender floor throughout
the actual joint support for her first two immutable private labels. -/
theorem rational_supported_payoff_floor (rewardNonnegative : 0 ≤ reward)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
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
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice := by
  obtain ⟨answer, selected, shape, maximizing, clean⟩ := rational_supported_clean_settlement
    weight nonnegative site representative decision current reward forfeit deposit
      forfeitPositive depositPositive assessment rational response supported
  exact continuation_payoff_floor weight nonnegative _ response _ final reached answer
    (clean history believed final reached).1 shape labelLow reward forfeit rewardNonnegative
      deposit (fun actual => PMF.pure actual)

end Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor
