/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment
import GameTheoryExtensions.Analysis.Protocol.SequentialExistence

/-! # Inactive forgetting does not prevent sequential equilibrium

The existing terminal decision protocol uses the same inactive information at
the initial and terminal histories. Global perfect recall fails after an action,
but decision recall holds. The generic existence theorem applies to every real
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

theorem clock (who : Unit) (site : model.InformationSite who) :
    InformationModel.InformationSite.CommonDepth model site 1 := by
  intro history
  cases who
  obtain ⟨state, supported, same, _⟩ := history_at_site prior id site history
  rw [same]
  rfl

/-- The general completion and one-shot construction works with the original
inactive observations, for arbitrary utilities of the completed history. -/
theorem exists_sequential_equilibrium (payoff : Unit → arena.History → ℝ) :
    ∃ assessment : model.BehavioralAssessment,
      assessment.IsSequentialEquilibriumFor decisionRecall.decisionInformationAntichain
        (fun who site => assessment.continuationContext site (payoff who) 1) := by
  simpa only [Nat.reduceSub] using model.exists_sequential_equilibrium
    (reference prior id) (reference_mixed prior id) decisionRecall 2 payoff
    (fun _ _ => 1) clock (fun _ _ => by decide)

end GameTheoryExtensionsTests.DecisionRecall
