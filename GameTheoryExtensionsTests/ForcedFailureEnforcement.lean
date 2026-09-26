/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcementThreshold
import GameTheoryExtensions.Analysis.FailureEnforcement

/-! # Why forcing future source actions to fail is not a universal punishment

The first result uses the existing finite disclosure game and standard
sequential equilibrium. The informed sender has no source information sites,
so suppressing all its remaining source actions imposes no restriction. Even
then optional disclosure destroys a source equilibrium's retained joint law.
Excluding the sender cannot revoke evidence already available to the receiver.

The numerical test exhibits an obligation whose failure utility exceeds its
successful continuation utility. The imported reusable expected-value criterion
does not identify a public failure result with any particular utility or
implement detection, global abort, collateral or an extended-real payoff.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ForcedFailureEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol
open AmbientEnforcement

/-- Actual source SE and all-target-SE obstruction coexist with the complete
absence of future source decisions by the player who discloses. This refutes
actor exclusion as a uniform repair, even when the exclusion is certain. It
does not refute aborting or changing the receiver's continuation as well. -/
theorem exclusion_without_source_actions_insufficient :
    (∀ _site : (model false).InformationSite false, False) ∧
    ∃ source : (model false).BehavioralAssessment,
      source.IsSequentialEquilibriumFor (antichain false) (fun who site =>
        source.continuationContext site (fun history => payoff 0 history.state who) 3) ∧
      ¬ ∃ target : (model true).BehavioralAssessment,
        isEquilibrium 0 target ∧
          (((model true).runSingleMoverBehavioralFrom (single true) target.strategy 3
            (arena true).initHistory).map History.state).map retained =
          (((model false).runSingleMoverBehavioralFrom (single false) source.strategy 3
            (arena false).initHistory).map History.state).map retained := by
  refine ⟨source_no_alice_site,
    sourceAssessment (sourceProfile (FinDist.uniformOfFintype (α := Bool))),
    source_sequential_equilibrium _, ?_⟩
  rintro ⟨target, equilibrium, matching⟩
  apply no_unpenalized_fair_law
  refine ⟨target, equilibrium, ?_⟩
  change _ = (((model false).runSingleMoverBehavioralFrom (single false)
    (sourceProfile (FinDist.uniformOfFintype (α := Bool))) 3
      (arena false).initHistory).map History.state).map retained at matching
  rwa [source_initialized_law, source_profile_guess] at matching

/-- If lawful continuation costs one and aborting avoids that cost, certain
detection followed by abort makes the deviation strictly better. This is a
continuation-payoff test, not a claim about every game's failure convention. -/
theorem abort_avoids_obligation :
    (-1 : ℝ) < (Enforcement.caughtContinuation (FinDist.pure true) 0 1).expect id :=
  Enforcement.certain_failure_can_reward 0 (-1) (by norm_num) 1

/-- The guessing pilot's four-unit failed-opening loss would suffice at
half-probability detection, if a service actually enforces this caught payoff.
This is the continuation calculation, not an implementation of forced failure. -/
theorem failed_opening_loss_suffices :
    (Enforcement.caughtContinuation (FinDist.uniformOfFintype (α := Bool)) (-4) 1).expect id ≤
      (0 : ℝ) := by
  rw [Enforcement.caught_continuation_value, FinDist.prob_uniformOfFintype]
  norm_num

end GameTheoryExtensionsTests.ForcedFailureEnforcement
