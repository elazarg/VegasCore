/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame
import Interaction.ReactiveEquilibriumExistence
import GameTheoryExtensions.Analysis.Protocol.PrescribedCompletion
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Sequential-equilibrium existence in the actual late-opening runtime

The complete bounded raw menu, initialized prior, partial pending observations
and public lottery builder define a finite decision-recall game. It has a
sequential equilibrium for every finite lottery weight and every audit payoff.
Existence does not imply preservation of a specified source equilibrium law.
Against a fixed full Bob policy, coherent completion makes Alice rational
at all legal sites while retaining Bob's decision laws. Bob's optimality and
the selected initialized terminal law remain separate obligations.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEquilibrium

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeGame

/-- The actual partially public runtime has a sequential equilibrium, with
all bounded raw deviations available. No payoff-sign, collateral-margin or
authentic-audit hypothesis is needed for finite-game existence. -/
theorem exists_sequential_equilibrium (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ) :
    ∃ assessment : (model weight nonnegative).BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
        (fun who history => payoff reward forfeit sample deposit history.state who) :=
  rawMenu.exists_sequentialEquilibrium initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (fun who history => payoff reward forfeit sample deposit history.state who)


/-- Against any fixed full native Bob policy, Alice has a coherent rational
completion on all legal information fibers. Bob's decision laws are retained.
The assessment obeys Bayes' rule wherever initialized play has positive mass;
neither Bob's rationality nor a prescribed terminal law is claimed. -/
theorem exists_consistent_alice_completion (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (policy : (model weight nonnegative).BehavioralPolicy bob) :
    ∃ assessment : (model weight nonnegative).BehavioralAssessment,
      assessment.IsSequentiallyConsistent
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      InformationModel.BehavioralAssessment.IsBayesConsistent (model weight nonnegative)
        assessment (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      (∀ site : (model weight nonnegative).InformationSite bob,
        assessment.strategy bob site.1 = policy site.1) ∧
      ∀ site : (model weight nonnegative).InformationSite alice,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext
            (rawMenu.bounded initial LateOpeningRuntimeService.horizon
              (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories site
            (fun history => payoff reward forfeit sample deposit history.state alice)) := by
  classical
  let prescribed : ∀ who, (model weight nonnegative).BehavioralPolicy who := fun who =>
    if same : who = bob then same.symm ▸ policy
    else rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
  obtain ⟨assessment, consistent, kept, rational⟩ :=
    (model weight nonnegative).exists_consistent_player_completion
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))
      (fun who info => Classical.choice (inferInstance :
        Nonempty ((model weight nonnegative).Choice who info)))
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => payoff reward forfeit sample deposit history.state who)
      {alice} prescribed
  refine ⟨assessment, consistent, consistent.isBayesConsistent _, ?_, ?_⟩
  · intro site
    simpa [prescribed] using kept bob site (by decide)
  · exact rational alice (by simp)

end Vegas.Examples.LateOpeningRuntimeEquilibrium
