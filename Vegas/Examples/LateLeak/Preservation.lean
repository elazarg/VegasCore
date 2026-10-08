/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Intended

/-! # Late sends with leaked openings break sequential-equilibrium preservation

The intended game, in which the sender can only open at the protected turn,
has sequential equilibria, and all of them have the intended outcome law. The
late-turn game adds two late turns with a content-blind inclusion coin of
probability `q` and a listener who sees openings pending between them. It has
no sequential equilibrium with that outcome law as soon as deferring pays:
`R > 0`, `q (D - R) > (1 - q) c` and `q R - (1 - q) (D + c) > R/2`.

For every reward scale `R > 0`, forfeit `D > R` and charge `c ≥ 0` both margins
hold for every `q` above an explicit threshold below one, so no margin on the
forfeit and the charge alone restores preservation. The sample parameters
`R = 2`, `D = 6 = 3R`, `c = 3 > R` and `q = 99/100` are one instance.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol

/-- **No sequential equilibrium of the late-turn game preserves the intended
outcome when deferring pays.** The intended game has a sequential equilibrium;
each of its sequential equilibria has the intended outcome law, in which every
type opens at the protected turn and the listener answers safely; and, when
`R > 0`, `q (D - R) > (1 - q) c` and `q R - (1 - q) (D + c) > R/2`, no
sequential equilibrium of the late-turn game has that outcome law. -/
theorem lateLeak_intended_outcome_not_preserved (G : LateLeakParameters)
    (pays : G.DeferralPays) :
    (∃ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
        (lateLeakPayoff G false)) ∧
    (∀ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
          (lateLeakPayoff G false) →
        lateLeakOutcomeLaw G false A.strategy = lateLeakIntendedOutcome) ∧
    ∀ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true) (lateLeak_terminates G true)
          (lateLeakPayoff G true) →
        lateLeakOutcomeLaw G true A.strategy ≠ lateLeakIntendedOutcome :=
  ⟨(lateLeak_intended_equilibria G).1, (lateLeak_intended_equilibria G).2,
    lateLeak_no_intended_equilibrium pays⟩

/-! ## Every margin -/

/-- An inclusion probability above which deferring pays, for reward scale `R`,
forfeit `D` and charge `c`: the larger of `c / (D - R + c)`, above which
`q (D - R) > (1 - q) c`, and `(D + c + R/2) / (D + c + R)`, above which
`q R - (1 - q) (D + c) > R/2`. -/
def lateLeakInclusionThreshold (R D c : ℝ) : ℝ :=
  max (c / (D - R + c)) ((D + c + R / 2) / (D + c + R))

/-- For `R > 0`, `D > R` and `c ≥ 0` the threshold is below one. -/
theorem lateLeakInclusionThreshold_lt_one {R D c : ℝ} (reward_pos : 0 < R) (margin : R < D)
    (charge : 0 ≤ c) : lateLeakInclusionThreshold R D c < 1 :=
  max_lt ((div_lt_one (by linarith)).mpr (by linarith))
    ((div_lt_one (by linarith)).mpr (by linarith))

/-- Above the threshold deferring pays. -/
theorem lateLeak_deferralPays_of_threshold {R D c : ℝ} (reward_pos : 0 < R) (margin : R < D)
    (charge : 0 ≤ c) (q : Set.Ioo (0 : ℝ) 1) (above : lateLeakInclusionThreshold R D c < q) :
    (⟨R, D, c, q⟩ : LateLeakParameters).DeferralPays := by
  obtain ⟨sending, guessing⟩ := max_lt_iff.mp above
  rw [div_lt_iff₀ (by linarith)] at sending guessing
  refine ⟨reward_pos, ?_, ?_⟩ <;> simp only [lateLeakInclusionProb] <;> linarith

/-- **No margin on the forfeit and the charge restores preservation.** For
every reward scale `R > 0`, forfeit `D > R` and charge `c ≥ 0`, the inclusion
threshold is below one, and for every inclusion probability `q` above it the
intended game has a sequential equilibrium, all its sequential equilibria have
the intended outcome law, and no sequential equilibrium of the late-turn game
with parameters `R`, `D`, `c` and `q` has that law. -/
theorem lateLeak_not_preserved_for_every_margin (R D c : ℝ) (reward_pos : 0 < R)
    (margin : R < D) (charge : 0 ≤ c) :
    lateLeakInclusionThreshold R D c < 1 ∧
    ∀ q : Set.Ioo (0 : ℝ) 1, lateLeakInclusionThreshold R D c < q →
      (∃ A : (lateLeakModel ⟨R, D, c, q⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ false)
          (lateLeak_terminates ⟨R, D, c, q⟩ false) (lateLeakPayoff ⟨R, D, c, q⟩ false)) ∧
      (∀ A : (lateLeakModel ⟨R, D, c, q⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ false)
            (lateLeak_terminates ⟨R, D, c, q⟩ false) (lateLeakPayoff ⟨R, D, c, q⟩ false) →
          lateLeakOutcomeLaw ⟨R, D, c, q⟩ false A.strategy = lateLeakIntendedOutcome) ∧
      ∀ A : (lateLeakModel ⟨R, D, c, q⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ true)
            (lateLeak_terminates ⟨R, D, c, q⟩ true) (lateLeakPayoff ⟨R, D, c, q⟩ true) →
          lateLeakOutcomeLaw ⟨R, D, c, q⟩ true A.strategy ≠ lateLeakIntendedOutcome :=
  ⟨lateLeakInclusionThreshold_lt_one reward_pos margin charge, fun q above =>
    lateLeak_intended_outcome_not_preserved _
      (lateLeak_deferralPays_of_threshold reward_pos margin charge q above)⟩

/-! ## The sample parameters -/

/-- The sample parameters: reward scale `R = 2`, forfeit `D = 6 = 3R`, charge
`c = 3 > R` and inclusion probability `q = 99/100`. -/
def LateLeakParameters.sample : LateLeakParameters :=
  ⟨2, 6, 3, ⟨99 / 100, by norm_num, by norm_num⟩⟩

/-- Deferring pays at the sample parameters: `q (D - R) = 396/100` exceeds
`(1 - q) c = 3/100`, and `q R - (1 - q) (D + c) = 189/100` exceeds
`R/2 = 1`. -/
theorem LateLeakParameters.sample_deferralPays : LateLeakParameters.sample.DeferralPays := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [LateLeakParameters.sample, lateLeakInclusionProb]

end Vegas
