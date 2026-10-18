/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialPacketOrigins
import Vegas.Examples.CommitSeedBroadcastFirstLateLaw
import GameTheory.Math.Probability.Expectation

/-! # The original quiet-prefix density under arbitrary raw behavior -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The three literal initial WAIT probabilities, at their actual native inputs. -/
def initialQuietReach (players : Player → app.Policy) : ℝ :=
  (players alice [] (initialAliceCallback.observe app alice) ⟨none⟩).toReal *
    (players bob [] ((initialBobCallback ⟨none⟩).observe app bob) ⟨none⟩).toReal *
      (players carol [] ((initialCarolCallback ⟨none⟩ ⟨none⟩).observe app carol) ⟨none⟩).toReal

theorem initialQuietReach_nonnegative (players : Player → app.Policy) :
    0 ≤ initialQuietReach players := by
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg

open Classical in
private theorem initialQuietReward (reward : app.Execution → ℝ)
    (first second third : app.Action) :
    (if (afterInitialResponses first second third).network.inputs = [] then
      reward (afterInitialResponses first second third) else 0) =
      if (⟨none⟩ : app.Action) = first then
        if (⟨none⟩ : app.Action) = second then
          if (⟨none⟩ : app.Action) = third then reward quietAfterCallbacks else 0
        else 0
      else 0 := by
  classical
  by_cases firstWait : (⟨none⟩ : app.Action) = first
  · subst first
    by_cases secondWait : (⟨none⟩ : app.Action) = second
    · subst second
      by_cases thirdWait : (⟨none⟩ : app.Action) = third
      · subst third
        have empty : (afterInitialResponses ⟨none⟩ ⟨none⟩ ⟨none⟩).network.inputs = [] :=
          (afterInitialResponses_inputs_empty _ _ _).mpr ⟨rfl, rfl, rfl⟩
        have same : reward (afterInitialResponses ⟨none⟩ ⟨none⟩ ⟨none⟩) =
            reward quietAfterCallbacks := rfl
        simpa only [empty, ite_true] using same
      · have nonempty : (afterInitialResponses ⟨none⟩ ⟨none⟩ third).network.inputs ≠ [] := by
          intro empty
          exact thirdWait ((afterInitialResponses_inputs_empty _ _ _).mp empty).2.2.symm
        simp only [nonempty, thirdWait, ite_false, ite_true]
    · have nonempty : (afterInitialResponses ⟨none⟩ second third).network.inputs ≠ [] := by
        intro empty
        exact secondWait ((afterInitialResponses_inputs_empty _ _ _).mp empty).2.1.symm
      simp only [nonempty, secondWait, ite_false, ite_true]
  · have nonempty : (afterInitialResponses first second third).network.inputs ≠ [] := by
      intro empty
      exact firstWait ((afterInitialResponses_inputs_empty _ _ _).mp empty).1.symm
    simp only [nonempty, firstWait, ite_false]

/-- Conditioning on the literal quiet initial subevent multiplies every bounded
continuation reward by the same original density. Later response kernels remain
the original kernels, including at inputs unreached by the limiting strategy. -/
theorem initial_quiet_expect (seed : Seeds) (players : Player → app.Policy)
    (reward : app.Execution → ℝ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ execution, |reward execution| ≤ bound) :
    expect (app.runRounds (family seed) players 3 initialExecution)
      (fun execution => if execution.network.inputs = [] then reward execution else 0) =
      initialQuietReach players * reward quietAfterCallbacks := by
  classical
  let gated : app.Execution → ℝ := fun execution =>
    if execution.network.inputs = [] then reward execution else 0
  have gatedBound (execution : app.Execution) : |gated execution| ≤ bound := by
    dsimp only [gated]
    split
    · exact bounded execution
    · simpa only [abs_zero] using nonnegative
  change expect (app.runRounds (family seed) players 3 initialExecution) gated = _
  rw [first_three_rounds]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ gatedBound)]
  have branch (first : app.Action) :
      expect
        ((players bob [] ((initialBobCallback first).observe app bob)).bind fun second =>
          (players carol [] ((initialCarolCallback first second).observe app carol)).map
            (afterInitialResponses first second)) gated =
        if (⟨none⟩ : app.Action) = first then
          (players bob [] ((initialBobCallback ⟨none⟩).observe app bob) ⟨none⟩).toReal *
            (players carol []
              ((initialCarolCallback ⟨none⟩ ⟨none⟩).observe app carol) ⟨none⟩).toReal *
                reward quietAfterCallbacks
        else 0 := by
    rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ gatedBound)]
    simp_rw [expect_map, Function.comp_def]
    change expect (players bob [] ((initialBobCallback first).observe app bob))
      (fun second => expect
        (players carol [] ((initialCarolCallback first second).observe app carol))
        (fun third => if (afterInitialResponses first second third).network.inputs = [] then
          reward (afterInitialResponses first second third) else 0)) = _
    simp_rw [initialQuietReward]
    by_cases firstWait : (⟨none⟩ : app.Action) = first
    · subst first
      simp only [ite_true]
      have inner (second : app.Action) :
          expect (players carol [] ((initialCarolCallback ⟨none⟩ second).observe app carol))
            (fun third => if (⟨none⟩ : app.Action) = second then
              if (⟨none⟩ : app.Action) = third then reward quietAfterCallbacks else 0 else 0) =
            if (⟨none⟩ : app.Action) = second then
              (players carol []
                ((initialCarolCallback ⟨none⟩ ⟨none⟩).observe app carol) ⟨none⟩).toReal *
                  reward quietAfterCallbacks
            else 0 := by
        by_cases secondWait : (⟨none⟩ : app.Action) = second
        · subst second
          simp only [ite_true]
          exact expect_ite_eq _ _ _
        · simp only [secondWait, ite_false, expect_constant]
      simp_rw [inner]
      rw [expect_ite_eq]
      ring
    · simp only [firstWait, ite_false, expect_constant]
  change expect (players alice [] (initialAliceCallback.observe app alice))
    (fun first => expect _ gated) = _
  simp_rw [branch]
  rw [expect_ite_eq]
  unfold initialQuietReach
  ring

/-- Original initialized prefix and its unchanged remaining eleven rounds,
restricted to the actual initial quiet subevent and one complete late input. -/
def initialQuietFirstLateMass (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) (seed : Seeds) : ℝ :=
  expect (app.runRounds (family seed) players 3 initialExecution) fun before =>
    if before.network.inputs = [] then
      (((app.runRounds (family seed) players 11 before).map (firstLateInput owner)) input).toReal
    else 0

/-- The original quiet-prefix density is independent of all original service
seeds. Its remaining complete-input likelihood is the actual native replay. -/
theorem initialQuietFirstLateMass_eq (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) (seed : Seeds) :
    initialQuietFirstLateMass players owner input seed = initialQuietReach players *
      firstLateLikelihood players owner input (nativePartitionedOrder seed) := by
  unfold initialQuietFirstLateMass
  rw [initial_quiet_expect seed players _ 1 zero_le_one (fun _ => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact pmf_toReal_apply_le_one _ _)]
  have tail : app.runRounds (family seed) players 11 quietAfterCallbacks =
      app.runRounds (family seed) players 9 quietStart := by
    rw [show 11 = 2 + 9 by decide, app.runRounds_add,
      quiet_initial_advances seed players, PMF.pure_bind]
  rw [tail, nohelper_first_late_input_kernel]
  rfl

/-- The same arbitrary raw profile, before conditioning or taking a limit,
obeys the bad-service mass bound on its original quiet subevent. -/
theorem initial_quiet_firstLate_bad_mass_le (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) :
    expect nativeSeedLaw (fun seed => if seed.2 owner = false then
      initialQuietFirstLateMass players owner input seed else 0) ≤
      (271 / 1000 : ℝ) * expect nativeSeedLaw
        (initialQuietFirstLateMass players owner input) := by
  classical
  have mass := funext (initialQuietFirstLateMass_eq players owner input)
  rw [mass]
  have numerator : (fun seed => if seed.2 owner = false then
      initialQuietReach players *
        firstLateLikelihood players owner input (nativePartitionedOrder seed) else 0) =
      fun seed => initialQuietReach players * (if seed.2 owner = false then
        firstLateLikelihood players owner input (nativePartitionedOrder seed) else 0) := by
    funext seed
    split <;> simp only [mul_zero]
  rw [numerator, expect_const_mul, expect_const_mul]
  have bound := mul_le_mul_of_nonneg_left
    (nativeSeedLaw_bad_likelihood_le owner (firstLateLikelihood players owner input)
      (firstLateLikelihood_nonnegative players owner input))
    (initialQuietReach_nonnegative players)
  nlinarith

theorem initial_quiet_firstLate_all_good_mass (players : Player → app.Policy) (owner : Player)
    (input : FirstLateInformation) :
    expect nativeSeedLaw (fun seed => if nativeGoodCount seed = 3 then
      initialQuietFirstLateMass players owner input seed else 0) =
      (729 / 1000 : ℝ) * expect nativeSeedLaw
        (initialQuietFirstLateMass players owner input) := by
  classical
  have mass := funext (initialQuietFirstLateMass_eq players owner input)
  rw [mass]
  have numerator : (fun seed => if nativeGoodCount seed = 3 then
      initialQuietReach players *
        firstLateLikelihood players owner input (nativePartitionedOrder seed) else 0) =
      fun seed => initialQuietReach players * (if nativeGoodCount seed = 3 then
        firstLateLikelihood players owner input (nativePartitionedOrder seed) else 0) := by
    funext seed
    split <;> simp only [mul_zero]
  rw [numerator, expect_const_mul, expect_const_mul,
    nativeSeedLaw_all_good_likelihood]
  ring

end Vegas.Examples.CommitSeedBroadcast
