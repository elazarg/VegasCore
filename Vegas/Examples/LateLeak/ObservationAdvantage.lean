/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Impossibility
import GameTheoryExtensions.Analysis.DisclosureReliability

/-! # Strict preferences from unequal disclosure probabilities

Failed first and second emissions can both be disclosed with positive
probability. Any strict advantage in first-emission disclosure separates
some types' timing preferences, even when unseen failures have distinct
timing metadata and arbitrary bit guesses. This is a checked comparison of
primitive payoffs, not a new native-runtime equilibrium theorem.
-/

noncomputable section

namespace Vegas

variable {G : LateLeakParameters}

/-- Bit-one answer probability after a failure: a disclosed bit is answered
truthfully, while an unseen packet receives an arbitrary bit guess. -/
def lateLeakObservedBitOne (seen guess : ℝ) (bit : Bool) : ℝ :=
  seen * (if bit then 1 else 0) + (1 - seen) * guess

/-- Expected sender payoff of a single emission with partial failure
disclosure, including its common forfeit and dropped-packet charge. -/
def lateLeakPartialObservationSendValue (G : LateLeakParameters)
    (safe seen guess : ℝ) (bit : Bool) (label : LateLeakLabel) : ℝ :=
  lateLeakInclusionProb G *
      (safe * (G.reward / 2) + (1 - safe) * lateLeakGuessGain G label) +
    (1 - lateLeakInclusionProb G) *
      (lateLeakObservedBitOne seen guess bit * lateLeakBitOneGain G label +
        (1 - lateLeakObservedBitOne seen guess bit) * lateLeakBitZeroGain G label -
          G.forfeit - G.dropCharge)

/-- Difference between the two failure branches' probabilities of a bit-one
answer, allowing a different unseen-failure reply at each transmission time. -/
def lateLeakObservationPull (firstSeen secondSeen firstGuess secondGuess : ℝ)
    (bit : Bool) : ℝ :=
  (firstSeen - secondSeen) * (if bit then 1 else 0) +
    (1 - firstSeen) * firstGuess - (1 - secondSeen) * secondGuess

theorem lateLeak_observation_pull_bit_gap (firstSeen secondSeen firstGuess secondGuess : ℝ) :
    lateLeakObservationPull firstSeen secondSeen firstGuess secondGuess true -
      lateLeakObservationPull firstSeen secondSeen firstGuess secondGuess false =
        firstSeen - secondSeen := by
  simp only [lateLeakObservationPull, Bool.false_eq_true, ite_false, ite_true,
    mul_one, mul_zero]
  ring

/-- The common charges cancel; successful answers move labels A/B together
and C oppositely, while partially observed failure moves A/B apart. -/
theorem lateLeak_partial_observation_send_difference
    (firstSafe secondSafe firstSeen secondSeen firstGuess secondGuess : ℝ)
    (bit : Bool) (label : LateLeakLabel) :
    lateLeakPartialObservationSendValue G firstSafe firstSeen firstGuess bit label -
      lateLeakPartialObservationSendValue G secondSafe secondSeen secondGuess bit label =
      lateLeakLabelPreference
        (lateLeakInclusionProb G * (secondSafe - firstSafe) * (G.reward / 2))
        ((1 - lateLeakInclusionProb G) *
          lateLeakObservationPull firstSeen secondSeen firstGuess secondGuess bit * G.reward)
        label := by
  cases label <;>
    simp only [lateLeakPartialObservationSendValue, lateLeakObservedBitOne,
      lateLeakObservationPull, lateLeakLabelPreference, lateLeakGuessGain,
      lateLeakBitOneGain, lateLeakBitZeroGain, reduceCtorEq, ite_true, ite_false] <;>
    ring

/-- Every strict disclosure advantage forces two labels at one common bit
to prefer opposite transmission times. No guess or safe-answer probabilities
are assumed: the algebra holds for every choice of those replies. -/
theorem lateLeak_partial_observation_opposite_preferences
    (reward : 0 < G.reward) (firstSeen secondSeen : ℝ)
    (advantage : secondSeen < firstSeen)
    (firstSafe secondSafe : Bool → ℝ) (firstGuess secondGuess : ℝ) :
    ∃ bit sender holder,
      lateLeakPartialObservationSendValue G (secondSafe bit) secondSeen secondGuess bit sender <
        lateLeakPartialObservationSendValue G (firstSafe bit) firstSeen firstGuess bit sender ∧
      lateLeakPartialObservationSendValue G (firstSafe bit) firstSeen firstGuess bit holder <
        lateLeakPartialObservationSendValue G (secondSafe bit)
          secondSeen secondGuess bit holder := by
  obtain ⟨bit, nonzero⟩ : ∃ bit,
      lateLeakObservationPull firstSeen secondSeen firstGuess secondGuess bit ≠ 0 := by
    by_cases first : lateLeakObservationPull firstSeen secondSeen firstGuess secondGuess true = 0
    · refine ⟨false, ?_⟩
      intro second
      have gap := lateLeak_observation_pull_bit_gap firstSeen secondSeen firstGuess secondGuess
      rw [first, second] at gap
      linarith
    · exact ⟨true, first⟩
  have separates : (1 - lateLeakInclusionProb G) *
      lateLeakObservationPull firstSeen secondSeen firstGuess secondGuess bit * G.reward ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_pos.mpr (lateLeakInclusionProb_lt_one G)).ne' nonzero)
      reward.ne'
  obtain ⟨sender, holder, positive, negative⟩ :=
    lateLeak_opposite_label_preferences
      (lateLeakInclusionProb G * (secondSafe bit - firstSafe bit) * (G.reward / 2))
      _ separates
  refine ⟨bit, sender, holder, ?_, ?_⟩
  · have difference := lateLeak_partial_observation_send_difference
      (G := G) (firstSafe bit) (secondSafe bit) firstSeen secondSeen firstGuess secondGuess
      bit sender
    linarith
  · have difference := lateLeak_partial_observation_send_difference
      (G := G) (firstSafe bit) (secondSafe bit) firstSeen secondSeen firstGuess secondGuess
      bit holder
    linarith

/-- A positive polling hazard gives an earlier pending packet strictly more
disclosure probability after any positive number of additional polls. -/
theorem lateLeak_polling_disclosure_advantage (hazard : ℝ) (positive : 0 < hazard)
    (belowOne : hazard < 1) (extraPolls : Nat) (additional : 0 < extraPolls) :
    hazard < 1 - (1 - hazard) ^ (extraPolls + 1) := by
  have smaller := pow_lt_pow_right_of_lt_one₀
    (show 0 < 1 - hazard by linarith) (show 1 - hazard < 1 by linarith)
    (show 1 < extraPolls + 1 by omega)
  rw [pow_one] at smaller
  linarith

/-- An emitted opening strictly dominates any immediately failed choice
when its uniform expected forfeit advantage exceeds the base-payoff range.
Success, failed emission, and no emission may have different continuations. -/
theorem lateLeak_observation_send_beats_failed_choice
    (success failure never : ℝ) (successNonnegative : 0 ≤ success)
    (failureNonnegative : 0 ≤ failure) (neverUpper : never ≤ G.reward)
    (margin : G.reward < lateLeakInclusionProb G * G.forfeit -
      (1 - lateLeakInclusionProb G) * G.dropCharge) :
    never - G.forfeit < lateLeakInclusionProb G * success +
      (1 - lateLeakInclusionProb G) * (failure - G.forfeit - G.dropCharge) := by
  have lower := GameTheory.DisclosureReliability.value_lower
    (lateLeakInclusionProb G) success failure (G.forfeit + G.dropCharge) 0
    (lateLeakInclusionProb_pos G).le (lateLeakInclusionProb_lt_one G).le
    successNonnegative failureNonnegative
  unfold GameTheory.DisclosureReliability.value at lower
  nlinarith

end Vegas
