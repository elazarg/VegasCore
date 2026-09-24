/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationPayoff
import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment

/-! # Fixed-payoff sequential preservation for terminal decisions

The common-maximizer criterion is exact for preservation of every abstract SE's
retained outcome law against full information, with the payoff fixed in advance.
The target assessment may depend on that payoff. Consistency and whole-policy
rationality use the existing terminal protocol correspondence.
-/

noncomputable section

namespace GameTheory.DecisionExperiment.Protocol

open Math.Probability

variable {State Signal Fact Action : Type}
  [Finite State] [Finite Action] [Nonempty Action]

theorem preserves_fixed_payoff_sequentialEquilibria_iff_commonMaximizer
    (prior : FinDist State) (observe : State → Signal) (fact : State → Fact)
    (utility : Fact → Action → ℝ) :
    (∀ source : (model (Action := Action) prior observe).BehavioralAssessment,
      source.IsSequentialEquilibriumFor (antichain prior observe)
        (fun _ site => source.continuationContext site
          (fun history => payoff (fun state => utility (fact state)) history.state) 2) →
      ∃ target : (model (Action := Action) prior id).BehavioralAssessment,
        target.IsSequentialEquilibriumFor (antichain prior id)
          (fun _ site => target.continuationContext site
            (fun history => payoff (fun state => utility (fact state)) history.state) 2) ∧
        observedLaw prior id fact target = observedLaw prior observe fact source) ↔
      HasCommonMaximizer prior observe (fun state => utility (fact state)) := by
  rw [← preserves_fixed_payoff_iff_commonMaximizer prior observe fact utility]
  constructor
  · intro preserves source optimal
    obtain ⟨target, equilibrium, lawEq⟩ := preserves (assessment prior observe source)
      ((isSequentialEquilibrium_iff prior observe source _).mpr optimal)
    refine ⟨response prior id (target.strategy ()),
      optimal_of_sequentialEquilibrium prior id target _ equilibrium, ?_⟩
    rw [observedLaw_eq, observedLaw_eq] at lawEq
    simpa only [assessment, response_policy] using lawEq
  · intro preserves source equilibrium
    obtain ⟨target, optimal, lawEq⟩ := preserves
      (response prior observe (source.strategy ()))
      (optimal_of_sequentialEquilibrium prior observe source _ equilibrium)
    refine ⟨assessment prior id target,
      (isSequentialEquilibrium_iff prior id target _).mpr optimal, ?_⟩
    rw [observedLaw_eq, observedLaw_eq]
    simpa only [assessment, response_policy] using lawEq

end GameTheory.DecisionExperiment.Protocol
