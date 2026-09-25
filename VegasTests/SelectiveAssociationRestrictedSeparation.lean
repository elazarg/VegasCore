/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedEquilibrium
import VegasTests.SelectiveAssociationPayoffSeparation

/-! # Declared payouts in the observation comparison

Both sides execute the same compiled graph, bounded response adapter and
service calendar. The native payout evaluator is parameterized by the passive
observation rule. Thus this comparison retains the actual returned payout,
rather than assigning a separate utility to message traffic.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem profile_payout_zero : (nativePayoutLaw (observation := leaks) profile).expect id = 0 := by
  rw [native_payout_expectation]
  have value := congrArg (fun law : FinDist ℝ => law.expect id) (initialized_payoff_law alice)
  simpa only [FinDist.expect_map, FinDist.expect_pure, id_eq, ↓reduceIte] using value

/-- Restoring passive observation can prevent every sequentially rational
assessment from matching the restricted game's equilibrium payout law.
Utilities are exactly the fixed program-declared payoffs on both sides. -/
theorem exists_equilibrium_no_native_payout_match :
    ∃ restricted : model.BehavioralAssessment,
      restricted.IsSequentialEquilibriumFor
        (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler)
        (fun who site => restricted.continuationContext site
          (fun history => nativeUtility who history.state) (2 * nativeHorizon + 1)) ∧
      (nativePayoutLaw (observation := leaks) restricted.strategy).expect id = 0 ∧
      ∀ target : nativeModel.BehavioralAssessment,
        target.IsSequentiallyRationalWithin
          (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1) →
        nativePayoutLaw (observation := leaks) restricted.strategy ≠
          nativePayoutLaw target.strategy := by
  obtain ⟨restricted, strategy, equilibrium⟩ := exists_sequentialEquilibrium
  have zero : (nativePayoutLaw (observation := leaks) restricted.strategy).expect id = 0 := by
    rw [strategy, profile_payout_zero]
  refine ⟨restricted, equilibrium, zero, fun target rational sameLaw => ?_⟩
  have gain := native_sequential_payout_bound target rational
  rw [← sameLaw, zero] at gain
  norm_num at gain

end VegasTests.SelectiveAssociation.Restricted
