/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstRetryComparison

/-! # Exact first-prefix law under native sequential rationality

When the checked retry-deterrence margin is positive, the original whole
first-late prefix equals its quiet-retry comparison law. Every first sender
response and early receiver response keeps its original probability and
private representation. The equality uses the actual native information
classes of every admitted genuine alias, including unreached classes.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstRetryRationality

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeFirstRetryComparison

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- This is an equality of the original physical laws, rather than merely
an approximation or a chosen posterior at an unreached information set. -/
theorem rational_comparison_law
    (positive : 0 < weight) (rewardNonnegative : 0 ≤ reward)
    (forfeitNonnegative : 0 ≤ forfeit) (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (bit : Bool) (label : Fin 3) :
    originalLaw weight nonnegative assessment.strategy bit label =
      comparisonLaw weight nonnegative assessment.strategy bit label := by
  have bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative assessment.strategy actual.1 ≤ 0 := by
    intro actual
    obtain ⟨decision, history, current⟩ := actual.2
    have zero := LateOpeningRuntimeAliceRationality.sequentially_rational_second_packet_zero
      weight nonnegative actual.1 history decision current reward forfeit deposit positive
        rewardNonnegative forfeitNonnegative depositNonnegative marginPositive assessment rational
    exact zero.le
  have close := original_close_comparison weight nonnegative assessment.strategy bit label
    0 (le_refl _) bound
  exact (show PMF.WithinTV 0 _ _ by simpa only [zero_mul] using close).eq_of_zero

end Vegas.Examples.LateOpeningRuntimeFirstRetryRationality
