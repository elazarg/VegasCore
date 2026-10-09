/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingPosterior
import Vegas.Examples.LateOpeningRuntimeBobBindingOptimization

/-! # Optimal native guesses in terms of actual hidden-bit probabilities

The clean whole-policy bit guesses attain the actual assessment probabilities
of the immutable initial bit. The all-raw optimization theorem therefore gives
their maximum. For a fully mixed Bayes assessment these probabilities are
conditional probabilities in the unchanged runtime execution distribution.
This does not assume that the bit keeps its prior after a pending observation.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingInformation
  LateOpeningRuntimeBobBindingDecision LateOpeningRuntimeBobAnswerPayoff
  LateOpeningRuntimeEarlyBobSafeMenu LateOpeningRuntimeBindingPrefix
  LateOpeningRuntimeBindingPosterior LateOpeningRuntimeBobBindingOptimization

/-- A mathematical readout of the initialized bit; the raw policy cannot use
this readout in place of its actual view. -/
def initializedBit (state : app.ProtocolState) : Option Bool :=
  state.map (fun control => originalBit control.execution)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

include representative decision current in
theorem bit_guess_value_eq_belief_probability
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (bit : Bool) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (answerFinitePolicy weight nonnegative (bitGuess bit)) =
        readoutBelief weight nonnegative site assessment initializedBit (some bit) := by
  classical
  rw [answer_context_value weight nonnegative site representative decision current,
    expect_eq_sum]
  unfold readoutBelief InformationModel.finiteHistoryBelief readoutHistories
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history _
  have actual := (decisionOfInformation_spec weight nonnegative site representative decision
    current history).1
  rw [initializedBit, actual, Option.map_some]
  cases bit <;>
    cases originalBit (decisionOfInformation weight nonnegative site representative decision current
      history).execution <;>
      simp [bitGuess]

include representative decision current in
theorem best_value_eq_posterior_max
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    bestGuessValue weight nonnegative site reward forfeit deposit assessment =
      max (readoutBelief weight nonnegative site assessment initializedBit (some false))
        (readoutBelief weight nonnegative site assessment initializedBit (some true)) := by
  unfold bestGuessValue
  rw [bit_guess_value_eq_belief_probability weight nonnegative site representative decision current,
    bit_guess_value_eq_belief_probability weight nonnegative site representative decision current]

include representative decision current in
theorem best_value_eq_conditional_probability_max
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (LateOpeningRuntimeNash.model weight nonnegative) assessment
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))) :
    bestGuessValue weight nonnegative site reward forfeit deposit assessment =
      max (conditionalPrefixProbability weight nonnegative site assessment.strategy initializedBit
          (some false))
        (conditionalPrefixProbability weight nonnegative site assessment.strategy initializedBit
          (some true)) := by
  rw [best_value_eq_posterior_max weight nonnegative site representative decision current]
  rw [bayes_readout_belief_eq_conditional_probability weight nonnegative site representative
    decision.execution current decision.ready assessment mixed bayes,
    bayes_readout_belief_eq_conditional_probability weight nonnegative site representative
    decision.execution current decision.ready assessment mixed bayes]

include representative decision current in
theorem rational_value_eq_posterior_max (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
        max (readoutBelief weight nonnegative site assessment initializedBit (some false))
          (readoutBelief weight nonnegative site assessment initializedBit (some true)) := by
  rw [rational_value_eq_bestGuessValue weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational,
    best_value_eq_posterior_max weight nonnegative site representative decision current]

include representative decision current in
/-- Consistency and whole-policy rationality identify the receiver value as
the limit of optimal guesses from actual native prefix probabilities. -/
theorem consistent_value_limit
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (consistent : assessment.IsSequentiallyConsistent
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))) :
    ∃ sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed ∧
        InformationModel.BehavioralAssessment.IsBayesConsistent
          (LateOpeningRuntimeNash.model weight nonnegative) (sequence n)
          (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative))) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment ∧
      Tendsto (fun n =>
        max (conditionalPrefixProbability weight nonnegative site (sequence n).strategy
            initializedBit (some false))
          (conditionalPrefixProbability weight nonnegative site (sequence n).strategy
            initializedBit (some true))) atTop
              (nhds ((context weight nonnegative site reward forfeit deposit assessment).value
                (assessment.strategy bob))) := by
  obtain ⟨sequence, approximate, converges, limits⟩ :=
    consistent_conditional_probabilities (Label := Option Bool) weight nonnegative site
      representative decision.execution current decision.ready assessment consistent
  refine ⟨sequence, approximate, converges, ?_⟩
  rw [rational_value_eq_posterior_max weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational]
  exact (limits initializedBit (some false)).max (limits initializedBit (some true))

end Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization
