/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastQuietProperReward

/-! # The positive expected payoff of initialized quiet proper play -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Averaging the actual native terminal comparison over the initialized
independent service experiment gives the strict initial incentive. -/
theorem quiet_initialized_proper_clock_two_value_lower
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (owner : Player) (players : Player → app.Policy)
    (selected : players owner = scheduledProperPolicy 2 owner)
    (foreign : ∀ other, other ≠ owner → players other =
      countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
        other)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (waited : ∀ who, players who ((initialCallback who).recall who)
      ((initialCallback who).observe app who) = PMF.pure ⟨none⟩) :
    (21 / 1000 : ℝ) ≤ expect (app.runRounds scheduler players horizon initialExecution)
      (fun final => netPayoff (app.finished final) owner) := by
  classical
  have bounded (final : app.Execution) :
      |netPayoff (app.finished final) owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc (app.finished final) owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  have realization : app.runRounds scheduler players horizon initialExecution =
      nativeSeedLaw.bind (fun seed => app.runRounds (family seed) players horizon
        initialExecution) := (original_realize players horizon initialState).symm
  rw [realization, expect_bind_tower_bounded _ _ _ bounded,
    ← nativeSeedLaw_survival_reward_expectation owner]
  apply expect_mono ?_ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  intro seed supportedSeed
  rw [← expect_constant (app.runRounds (family seed) players horizon initialExecution)
    (if seed.2 owner then
      if ∃ other : Player, other ≠ owner ∧ seed.2 other = false then (1 : ℝ) else 0
      else -(3 / 2))]
  apply expect_mono ?_ (payoffIntegrable_constant _ _)
    (payoffIntegrable_of_bounded _ _ bounded)
  intro final reached
  exact quiet_initialized_proper_clock_two_payoff_lower assessment equilibrium seed supportedSeed
    owner players selected foreign covered waited final reached

end Vegas.Examples.CommitSeedBroadcast
