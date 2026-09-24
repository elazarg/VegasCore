/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.SequentialBeliefs
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # Consistency cannot repair an irrational continuation

Apply the general completion theorem to the hidden-bit SPE with a strictly
inferior off-path response. It produces a consistent assessment of exactly
that profile, yet no completion can make it sequentially rational.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ConsistencyCompletion

open GameTheory.Protocol
open OffPathDisclosure SequentialCredibility SequentialBeliefs

/-- Consistency existence leaves the continuation-incentive obligation intact,
even for a profile that already satisfies ordinary SPE. -/
theorem consistent_but_not_rational :
    ∃ assessment : (model false).BehavioralAssessment,
      assessment.strategy = prescribed false ∧
      assessment.IsSequentiallyConsistent antichain ∧
      ¬ assessment.IsSequentiallyRationalWithin
        (fun who history => SequentialCredibility.payoff history who) 3 := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      (.ofStrategy (perturbedProfile 0)) (perturbed_full 0) antichain (prescribed false)
  exact ⟨assessment, strategy, consistent,
    no_sequentially_rational_assessment assessment strategy⟩

end GameTheoryExtensionsTests.ConsistencyCompletion
