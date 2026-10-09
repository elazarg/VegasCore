/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveOwnPlay
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Sequential equilibria in finite reactive runtimes

Existing finite-history and decision-recall laws discharge the hypotheses of
finite-game equilibrium existence. No source game or prescribed outcome is
assumed, and the scheduler need satisfy only the finite nature requirement.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol

variable {Principal : Type} [Fintype Principal] [DecidableEq Principal]
    {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Every finite-horizon response-menu runtime with finitely branching nature
has a sequential equilibrium for arbitrary realized payoffs. This is existence
in the runtime, without an assertion about any source equilibrium or outcome. -/
theorem exists_sequentialEquilibrium [app.FiniteNature initial scheduler]
    (payoff : Principal → (menu.protocol initial horizon scheduler).History → ℝ) :
    ∃ assessment : (menu.information initial horizon scheduler).BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (menu.decisionRecall initial horizon scheduler).decisionInformationAntichain
        (menu.bounded initial horizon scheduler).wellFoundedHistories payoff := by
  classical
  obtain ⟨assessment, rational, consistent⟩ :=
    (menu.information initial horizon scheduler).exists_sequentialEquilibrium
      (menu.decisionRecall initial horizon scheduler)
      (fun who info => Classical.choice (inferInstance :
        Nonempty ((menu.information initial horizon scheduler).Choice who info)))
      payoff (menu.bounded initial horizon scheduler).wellFoundedHistories
  exact ⟨assessment, rational, consistent⟩

end Interaction.ReactiveApplication.ResponseMenu
