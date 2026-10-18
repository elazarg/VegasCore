/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationPrefixWeights
import GameTheory.Math.Probability.ConditionalObservation

/-! # Original two-bit Bayes law at Bob's actual quiet callback

The joint keeps both original service coins. The final coin is projected out
only after constructing the actual native activation/input law.
-/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The original service draw paired with the actual clock-two input kernel
following the literal initial WAIT prefix. -/
def originalBobPrefixJoint (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) : PMF (Seeds × (List app.PlayerEntry × app.PlayerView)) :=
  bindPairLaw (seedLaw failure) fun seed => bobClockTwoInputLaw seed bit players

/-- This readout retains Bob's entire input and the original poll coin. -/
def bobInputGoodJoint (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) : PMF ((List app.PlayerEntry × app.PlayerView) × Bool) :=
  (originalBobPrefixJoint failure bit players).map fun outcome => (outcome.2, outcome.1.1)

theorem bob_clock_two_input_final_independent (good final bit : Bool)
    (players : Player → app.Policy) :
    bobClockTwoInputLaw (good, final) bit players =
      bobClockTwoInputLaw (good, false) bit players := by
  cases good
  · rw [bad_bob_clock_two_input_law, bad_bob_clock_two_input_law]
  · rw [good_bob_clock_two_input_law, good_bob_clock_two_input_law]

/-- The projection is a theorem about the original joint, rather than a
replacement service law at the callback. -/
theorem bobInputGoodJoint_eq (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) :
    bobInputGoodJoint failure bit players =
      (bindPairLaw goodPollLaw fun good => bobClockTwoInputLaw (good, false) bit players).map
        Prod.swap := by
  unfold bobInputGoodJoint originalBobPrefixJoint seedLaw bindPairLaw
  simp only [PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support
  intro good _supported
  simp_rw [bob_clock_two_input_final_independent good]
  rw [PMF.bind_const]
  rfl

/-- Bad worlds reach this quiet input regardless of Alice's current policy. -/
theorem bob_quiet_bad_joint_mass (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) :
    bobInputGoodJoint failure bit players (nativeInput bob (bobBeforeBad bit), false) =
      (1 / 10 : ENNReal) := by
  rw [bobInputGoodJoint_eq, bindPairLaw_swap_apply, bad_bob_clock_two_quiet_mass, mul_one]
  norm_num [goodPollLaw, mix_apply, PMF.pure_apply,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10), add_comm]

/-- Good worlds reach the same full input precisely when Alice WAITs at her
common empty clock-two input. -/
theorem bob_quiet_good_joint_mass (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) :
    bobInputGoodJoint failure bit players (nativeInput bob (bobBeforeBad bit), true) =
      (9 / 10 : ENNReal) * players alice ((aliceEmptyGood bit).recall alice)
        ((aliceEmptyGood bit).observe app alice) ⟨none⟩ := by
  rw [bobInputGoodJoint_eq, bindPairLaw_swap_apply, good_bob_clock_two_quiet_mass]
  norm_num [goodPollLaw, mix_apply, PMF.pure_apply,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10), add_comm]

theorem bob_quiet_input_mass (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) :
    ((bobInputGoodJoint failure bit players).map Prod.fst)
        (nativeInput bob (bobBeforeBad bit)) =
      (1 / 10 : ENNReal) + (9 / 10 : ENNReal) *
        players alice ((aliceEmptyGood bit).recall alice)
          ((aliceEmptyGood bit).observe app alice) ⟨none⟩ := by
  rw [bobInputGoodJoint_eq, PMF.map_comp]
  change ((bindPairLaw goodPollLaw fun good =>
    bobClockTwoInputLaw (good, false) bit players).map Prod.snd) _ = _
  rw [bindPairLaw_map_snd, PMF.bind_apply, tsum_fintype, Fintype.sum_bool,
    good_bob_clock_two_quiet_mass, bad_bob_clock_two_quiet_mass]
  norm_num [goodPollLaw, mix_apply, PMF.pure_apply,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10), add_comm]

/-- The quiet fiber has a uniformly positive original likelihood even when
Alice's empty-input WAIT probability is zero. -/
theorem bob_quiet_input_present (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) :
    nativeInput bob (bobBeforeBad bit) ∈
      ((bobInputGoodJoint failure bit players).map Prod.fst).support := by
  apply (PMF.mem_support_iff _ _).mpr
  rw [bob_quiet_input_mass]
  rw [ne_eq, add_eq_zero]
  rintro ⟨impossible, _⟩
  norm_num at impossible

/-- Exact Bayes odds for the original poll bit, with the complete quiet input
as the observation and the original final coin integrated only by readout. -/
theorem bob_quiet_bad_posterior (failure : Set.Ioo (0 : ℝ) 1) (bit : Bool)
    (players : Player → app.Policy) :
    ((fiberPosterior (bobInputGoodJoint failure bit players) Prod.fst
        (nativeInput bob (bobBeforeBad bit))).map Prod.snd) false =
      (1 / 10 : ENNReal) /
        ((1 / 10 : ENNReal) + (9 / 10 : ENNReal) *
          players alice ((aliceEmptyGood bit).recall alice)
            ((aliceEmptyGood bit).observe app alice) ⟨none⟩) := by
  rw [fiberPosterior_map_snd_apply _ _ (bob_quiet_input_present failure bit players),
    bob_quiet_bad_joint_mass, bob_quiet_input_mass]
  simp only [div_eq_mul_inv]

end Vegas.Examples.CommitTimingInformation
