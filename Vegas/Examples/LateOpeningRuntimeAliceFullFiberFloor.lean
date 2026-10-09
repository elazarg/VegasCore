/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication
import Vegas.Examples.LateOpeningRuntimeBobSuccessBindingClean
import Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor

/-! # Sender reward on every compatible successful-opening history

The actual optimal first-binding packet is clean throughout its complete
information class. The optional and final disclosure implications therefore
publish its selected answer on every physical continuation of the original
receiver policy, including histories assigned zero posterior belief. For
Alice's first two labels this gives half her reward before her own audit
deduction; receiver rationality does not clear sender traffic.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobSuccessInformation LateOpeningRuntimeBobSuccessDecision
  LateOpeningRuntimeBobSuccessOptimization LateOpeningRuntimeBobSuccessBindingClean
  LateOpeningRuntimeBobSuccessPayoff
open LateOpeningRuntimeBobRawBinding (serviced)
open LateOpeningRuntimeBobBindingDecision (context)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- No belief-positive restriction occurs in the selected answer's actual
disclosure law. Only the receiver follows the original assessed policy. -/
theorem sequentially_rational_supported_publication (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    ∃ answer : Answer,
      (serviced decision.execution response).application.config.store (.inr bobBindEvent) =
        some (.success answer) ∧
      (answer = safe ∨ ∃ label : Fin 3, answer = labelGuess label) ∧
      ∀ (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
        (players : Player → app.Policy),
        players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob →
        ∀ final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          players 14 ((decisionOfInformation weight nonnegative site representative decision
            current history).execution.respond app bob response)).support,
          final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  have localRational := rational bob site
  dsimp only at localRational
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  obtain ⟨material, answer, responseEq, _, selected, shape, _, _, _, fullFiber⟩ :=
    rational_supported_clean_binding weight nonnegative site representative decision current
      reward forfeit deposit forfeitPositive depositPositive assessment localRational response
        supported
  refine ⟨answer, selected, shape, ?_⟩
  intro history players bobPolicy final reached
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, recovered.execution⟩) := compatible.1 ▸ history.1.trace
  have nextSelected := (response_result_same_information weight nonnegative decision recovered
    compatible.2.1 compatible.2.2 response).symm.trans selected
  have nextSupported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (recovered.execution.recall bob) (recovered.execution.observe app bob)).support := by
    rw [← compatible.2.1, ← compatible.2.2]
    exact supported
  have available := rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bob (assessment.strategy bob)
      _ _ response nextSupported
  rw [responseEq] at available nextSelected reached
  exact LateOpeningRuntimeBobDisclosurePublication.binding_publication weight nonnegative
    reward forfeit deposit assessment recovered.execution boundedTrace recovered.quiet
      recovered.ready material answer available nextSelected (fullFiber history).1 forfeitPositive
        depositPositive rational players bobPolicy final reached

/-- The half-reward floor applies even to hidden histories with zero belief,
and retains exactly Alice's own full-record audit deduction. -/
theorem sequentially_rational_supported_payoff_floor (rewardNonnegative : 0 ≤ reward)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (labelLow : (originalLabel (decisionOfInformation weight nonnegative site representative
      decision current history).execution).val < 2)
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob response)).support) :
    reward / 2 - TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) alice * deposit alice ≤
      LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
        deposit (app.finished final) alice := by
  obtain ⟨answer, _, shape, published⟩ := sequentially_rational_supported_publication weight
    nonnegative site representative decision current reward forfeit deposit forfeitPositive
      depositPositive assessment rational response supported
  exact LateOpeningRuntimeAliceSuccessFloor.continuation_payoff_floor weight nonnegative
    _ response players final reached answer (published history players bobPolicy final reached)
      shape labelLow reward forfeit rewardNonnegative deposit (fun actual => PMF.pure actual)

end Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor
