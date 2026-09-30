/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Inactive forgetting does not prevent sequential equilibrium

The existing terminal decision protocol uses the same inactive information at
the initial and terminal histories. Global perfect recall fails after an action,
but decision recall holds. The library existence theorem applies to every real
payoff without changing that information model.
-/

noncomputable section

namespace GameTheoryExtensionsTests.DecisionRecall

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.DecisionExperiment.Protocol

def prior : PMF Unit := PMF.pure ()

abbrev arena := GameTheory.DecisionExperiment.Protocol.arena (Action := Bool) prior

abbrev model := GameTheory.DecisionExperiment.Protocol.model (Action := Bool) prior id

theorem decisionRecall : model.DecisionRecall := by
  intro who site first second
  cases who
  obtain ⟨left, leftPresent, leftEq, _⟩ := history_at_site prior id site first
  obtain ⟨right, rightPresent, rightEq, _⟩ := history_at_site prior id site second
  rw [leftEq, rightEq]

theorem not_perfectRecall : ¬ model.PerfectRecall := by
  intro strongRecall
  let last := terminalHistory prior () ((PMF.mem_support_pure_iff _ _).mpr rfl) true
  have impossible := strongRecall () arena.initHistory.trace last.trace rfl
  change ([] : List (Option Unit × Bool)) = [(some (), true)] at impossible
  cases impossible

/-- The general existence theorem applies to the original inactive
observations, for arbitrary utilities of the completed history. -/
theorem exists_sequential_equilibrium (payoff : Unit → arena.History → ℝ) :
    ∃ assessment : model.BehavioralAssessment,
      assessment.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        (bounded (Action := Bool) prior).wellFoundedHistories payoff :=
  model.exists_sequentialEquilibrium decisionRecall
    (fun who info => ((reference prior id).strategy who info).support_nonempty.choose) payoff _

end GameTheoryExtensionsTests.DecisionRecall
