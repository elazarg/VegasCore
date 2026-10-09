/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeNash
import Interaction.ReactiveEquilibriumExistence

/-! # Sequential-equilibrium existence in the actual late-opening runtime

The complete bounded raw menu, initialized prior, partial pending observations
and public lottery builder define a finite decision-recall game. It has a
sequential equilibrium for every finite lottery weight and every audit payoff.
Existence does not imply preservation of a specified source equilibrium law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEquilibrium

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeNash

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

end Vegas.Examples.LateOpeningRuntimeEquilibrium
