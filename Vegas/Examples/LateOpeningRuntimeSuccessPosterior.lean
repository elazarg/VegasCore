/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingPosterior
import Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization

/-! # Native success values from actual conditional label probabilities

Safe and the three label guesses exhaust optimal logical answers at a fresh
timely binding after sender success. Their values use the actual full native
information class. Along any common mixed Bayes consistency witness these
values are limits of physical prefix conditional probabilities, including at
unreached classes. The initialized uniform label prior is not substituted for
these posteriors.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSuccessPosterior

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobSuccessInformation
  LateOpeningRuntimeBobSuccessDecision LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeBobSuccessOptimization LateOpeningRuntimeBindingPrefix
  LateOpeningRuntimeBindingPosterior
open LateOpeningRuntimeBobBindingDecision (context)

/-- A mathematical readout, rather than an additional observation available
to the receiver's raw policy. -/
def initializedLabel (state : app.ProtocolState) : Option (Fin 3) :=
  state.map (fun control => originalLabel control.execution)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem label_mass_eq_readout
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (label : Fin 3) :
    labelMass weight nonnegative site representative decision current assessment label =
      readoutBelief weight nonnegative site assessment initializedLabel (some label) := by
  classical
  unfold labelMass
  rw [expect_eq_sum]
  unfold readoutBelief InformationModel.finiteHistoryBelief readoutHistories
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history _
  have actual := (decisionOfInformation_spec weight nonnegative site representative decision
    current history).1
  rw [initializedLabel, actual, Option.map_some]
  simp

include representative decision current in
theorem best_value_eq_posterior_max
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    bestAnswerValue weight nonnegative site reward forfeit deposit assessment =
      max (2 / 5) (max (readoutBelief weight nonnegative site assessment initializedLabel (some 0))
        (max (readoutBelief weight nonnegative site assessment initializedLabel (some 1))
          (readoutBelief weight nonnegative site assessment initializedLabel (some 2)))) := by
  rw [bestAnswerValue_formula weight nonnegative site representative decision current]
  rw [label_mass_eq_readout weight nonnegative site representative decision current,
    label_mass_eq_readout weight nonnegative site representative decision current,
    label_mass_eq_readout weight nonnegative site representative decision current]

include representative decision current in
theorem rational_value_eq_posterior_max (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (assessment.strategy bob) =
        max (2 / 5)
          (max (readoutBelief weight nonnegative site assessment initializedLabel (some 0))
          (max (readoutBelief weight nonnegative site assessment initializedLabel (some 1))
            (readoutBelief weight nonnegative site assessment initializedLabel (some 2)))) := by
  rw [rational_value_eq_bestAnswerValue weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational,
    best_value_eq_posterior_max weight nonnegative site representative decision current]

include representative decision current in
/-- This consumes any given common consistency sequence; it does not select
independent posterior witnesses for the three label guesses. -/
theorem conditional_value_tendsto (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      (LateOpeningRuntimeNash.model weight nonnegative) (sequence n)
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)))
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment) :
    Tendsto (fun n => max (2 / 5 : ℝ)
      (max (conditionalPrefixProbability weight nonnegative site (sequence n).strategy
          initializedLabel (some 0))
        (max (conditionalPrefixProbability weight nonnegative site (sequence n).strategy
            initializedLabel (some 1))
          (conditionalPrefixProbability weight nonnegative site (sequence n).strategy
            initializedLabel (some 2))))) atTop
              (nhds ((context weight nonnegative site reward forfeit deposit assessment).value
                (assessment.strategy bob))) := by
  rw [rational_value_eq_posterior_max weight nonnegative site representative decision current
    reward forfeit deposit forfeitNonnegative depositNonnegative assessment rational]
  have limits (label : Fin 3) := conditional_probability_tendsto weight nonnegative site
    representative decision.execution current decision.ready sequence assessment mixed bayes
      converges initializedLabel (some label)
  exact tendsto_const_nhds.max ((limits 0).max ((limits 1).max (limits 2)))

end Vegas.Examples.LateOpeningRuntimeSuccessPosterior
