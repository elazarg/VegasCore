/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceNormalization
import Vegas.Examples.LateOpeningRuntimeEarlyBobRationality
import Vegas.Examples.LateOpeningRuntimeBobBindingDecision
import Vegas.Examples.LateOpeningRuntimeBobRationality
import Vegas.Examples.LateOpeningRuntimeEquilibrium

/-! # Native equilibrium constraints after collateral is fixed

One finite public lottery service satisfies the complete raw service contract
and packet-erasure independence. Its canonical late omission probability is
strictly positive but smaller than any requested positive bound. The existing
bounded raw game has a sequential equilibrium, and every such equilibrium
satisfies both final sender response laws, stays quiet at the receiver's early
unresolved-publication callback, and has value at least one half at the
receiver's first binding decision after sender publication fails.
At every clean, ready, timely final receiver disclosure class, publication
failure also has probability zero under its actual continuation law.

The payoff constants precede the service choice. The response conditions
quantify actual native information classes through actual representative
histories. They do not assert a complete equilibrium classification or
preservation or exclusion of any source equilibrium law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLateAcceptance

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- Checked response and value constraints on an assessment of the existing
native game. This predicate changes neither the game nor its equilibrium notion. -/
def NativeResponseConstraints
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    Prop :=
  LateOpeningRuntimeAliceNormalization.LastAliceResponsesNormalized
      weight nonnegative assessment.strategy ∧
  (∀ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1)
      (decision : LateOpeningRuntimeEarlyBobInformation.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨21, some bob, decision.execution⟩ →
        LateOpeningRuntimeEarlyBobDecision.responseLaw weight nonnegative site
          (assessment.strategy bob site.1) = PMF.pure ⟨none⟩) ∧
  (∀ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1)
      (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨14, some bob, decision.execution⟩ →
        (1 / 2 : ℝ) ≤ (LateOpeningRuntimeBobBindingDecision.context
          weight nonnegative site reward forfeit deposit assessment).value
            (assessment.strategy bob)) ∧
  (∀ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1)
      (decision : LateOpeningRuntimeBobIncentive.DecisionHistory weight nonnegative)
      (current : representative.1.state = some ⟨6, some bob, decision.execution⟩),
      ((LateOpeningRuntimeBobRationality.finalLaw weight nonnegative site representative
        decision current assessment (assessment.strategy bob)).toOuterMeasure
          {final | final.application.config.store (.inr bobRevealEvent) =
            some .failure}).toReal = 0)

/-- These constraints use sequential rationality alone. No consistency
condition or posterior restriction is needed for the local comparisons. -/
theorem sequentially_rational_constraints
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitPositive : 0 < forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit) (bobCollateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    NativeResponseConstraints weight nonnegative reward forfeit deposit assessment := by
  refine ⟨LateOpeningRuntimeAliceNormalization.sequentially_rational_last_responses
    weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitPositive.le
      depositNonnegative marginPositive assessment rational, ?_, ?_, ?_⟩
  · intro site representative decision current
    exact LateOpeningRuntimeEarlyBobRationality.sequentially_rational_early_response_law
      weight nonnegative site representative decision current reward forfeit deposit
        forfeitPositive.le bobCollateral assessment rational
  · intro site representative decision current
    apply LateOpeningRuntimeBobBindingDecision.rational_binding_value_ge_half
      weight nonnegative site representative decision current reward forfeit deposit
        assessment
    have localRational := rational bob site
    dsimp only at localRational
    rw [assessment.continuationContext_eq_truncated_of_bounded
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
    exact localRational
  · intro site representative decision current
    apply LateOpeningRuntimeBobRationality.sequentially_rational_final_failure_zero
      weight nonnegative site representative decision current reward forfeit
        (fun actual => PMF.pure actual) deposit forfeitPositive ?_ (by linarith)
          assessment rational
    intro actual observed supported
    have same := (PMF.mem_support_pure_iff _ _).mp supported
    subst observed
    exact List.Subset.refl _

/-- All four constraints hold simultaneously in each native sequential
equilibrium, including its information classes outside the realized path. -/
theorem equilibrium_constraints
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitPositive : 0 < forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit) (bobCollateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    NativeResponseConstraints weight nonnegative reward forfeit deposit assessment :=
  sequentially_rational_constraints weight nonnegative reward forfeit deposit positive
    rewardNonnegative forfeitPositive depositNonnegative marginPositive bobCollateral
      assessment equilibrium.1

omit weight nonnegative in
/-- All finite payoff constants are fixed before the service is chosen.
The same actual service has arbitrarily small positive canonical late
omission, a native sequential equilibrium, and the listed constraints for
every native sequential equilibrium. -/
theorem exists_service_with_constraints
    (rewardNonnegative : 0 ≤ reward) (largeForfeit : reward < forfeit)
    (aliceCollateral : reward < deposit alice) (bobCollateral : 1 < deposit bob)
    (failureFloor : ℝ) (floorPositive : 0 < failureFloor) :
    ∃ (weight : ℝ) (nonnegative : 0 ≤ weight),
      0 < weight ∧
      LateOpeningRuntimeService.runtime.AsyncContract leaks initial
        LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          delay bound ∧
      LateOpeningRuntimeService.runtime.BlindToLatePackets leaks bound
        (LateOpeningRuntimeService.scheduler weight nonnegative) ∧
      (∀ (bit : Bool) (label : Fin 3) (slot : Fin 2),
        LateOpeningRuntimeLatePrefix.initialPhysical bit label ∈ initial.support ∧
        0 < 1 - (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (LateOpeningRuntimeLatePrefix.latePlayers bit slot) LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeLatePrefix.initialExecution bit label)).map
              LateOpeningRuntimeReliability.accepted) true).toReal ∧
        1 - (((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (LateOpeningRuntimeLatePrefix.latePlayers bit slot) LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeLatePrefix.initialExecution bit label)).map
              LateOpeningRuntimeReliability.accepted) true).toReal < failureFloor) ∧
      (∃ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit history.state who)) ∧
      ∀ assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
          (rawMenu.bounded initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
          (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
            (fun actual => PMF.pure actual) deposit history.state who) →
          NativeResponseConstraints weight nonnegative reward forfeit deposit assessment := by
  obtain ⟨weight, nonnegative, positive, contract, blind, failurePositive,
      failureSmall, marginPositive, _⟩ :=
    LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized
      reward forfeit deposit rewardNonnegative largeForfeit aliceCollateral
        failureFloor floorPositive
  refine ⟨weight, nonnegative, positive, contract, blind, ?_, ?_, ?_⟩
  · intro bit label slot
    refine ⟨LateOpeningRuntimeLatePrefix.initialPhysical_supported bit label, ?_, ?_⟩
    · rw [LateOpeningRuntimeTerminalReceipt.terminal_receipt_probability]
      exact failurePositive
    · rw [LateOpeningRuntimeTerminalReceipt.terminal_receipt_probability]
      exact failureSmall
  · exact LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium weight nonnegative
      reward forfeit (fun actual => PMF.pure actual) deposit
  · intro assessment equilibrium
    exact equilibrium_constraints weight nonnegative reward forfeit deposit positive
      rewardNonnegative (by linarith) (by linarith) marginPositive bobCollateral
        assessment equilibrium

end Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints
