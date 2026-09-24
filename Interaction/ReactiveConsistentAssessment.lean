/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # Consistent completions of finite native profiles

Every profile in a bounded response-menu instance admits sequentially consistent
beliefs. The construction perturbs every local choice and extracts one common
subsequence. Native chance laws, observations and scheduling stay fixed.
Continuation incentives under the limiting beliefs require a separate proof.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Complete any prescribed native profile without changing any strategy
coordinate, including its behavior after earlier deviations. -/
theorem exists_consistent_assessment
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who) :
    ∃ assessment : (menu.information initial horizon scheduler).BehavioralAssessment,
      assessment.strategy = profile ∧ assessment.IsSequentiallyConsistent
        (menu.decisionInformationAntichain initial horizon scheduler) :=
  (menu.uniformAssessment initial horizon scheduler).exists_consistent_completion
    (menu.uniform_fullyMixed initial horizon scheduler)
    (menu.decisionInformationAntichain initial horizon scheduler) profile

end Interaction.ReactiveApplication.ResponseMenu
