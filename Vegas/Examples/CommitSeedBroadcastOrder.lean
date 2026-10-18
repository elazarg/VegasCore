/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Joint
import GameTheory.Math.Probability.Mixture
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # The original three-owner seed and callback-order kernel -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open scoped BigOperators
open GameTheory.Math.Probability

/-- The original independent good-service bits, in owner order. -/
abbrev TimingBits := Bool × Bool × Bool

/-- The bit of the actual owner, without consulting the callback order. -/
def timingGood (bits : TimingBits) (owner : Fin 3) : Bool :=
  match owner.val with
  | 0 => bits.1
  | 1 => bits.2.1
  | _ => bits.2.2

/-- The six possible remainder orders, each used with probability one sixth. -/
def callbackOrder (index : Fin 6) : List (Fin 3) :=
  match index.val with
  | 0 => [0, 1, 2]
  | 1 => [0, 2, 1]
  | 2 => [1, 0, 2]
  | 3 => [1, 2, 0]
  | 4 => [2, 0, 1]
  | _ => [2, 1, 0]

/-- The actual first-late callback word: good bits before the middle slot,
bad bits after it, preserving the original remainder order within each part. -/
def partitionedOrder (bits : TimingBits) (index : Fin 6) : List (Fin 3) :=
  (callbackOrder index).filter (timingGood bits) ++
    (callbackOrder index).filter (fun owner => !(timingGood bits owner))

/-- The middle slot occurs after this many good-service callbacks. -/
def goodCount (bits : TimingBits) : Nat :=
  (if bits.1 then 1 else 0) + (if bits.2.1 then 1 else 0) +
    (if bits.2.2 then 1 else 0)

theorem callbackOrder_injective : Function.Injective callbackOrder := by decide

theorem callbackOrder_complete (index : Fin 6) :
    (callbackOrder index).Nodup ∧ (callbackOrder index).toFinset = Finset.univ := by
  fin_cases index <;> decide

theorem partitionedOrder_is_callbackOrder (bits : TimingBits) (index : Fin 6) :
    ∃ result, partitionedOrder bits index = callbackOrder result := by
  rcases bits with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;> fin_cases index <;> decide

theorem all_good_of_goodCount (bits : TimingBits) (count : goodCount bits = 3)
    (owner : Fin 3) : timingGood bits owner = true := by
  rcases bits with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;>
    fin_cases owner <;> simp_all [goodCount, timingGood]

/-- Exact integer fiber weights for the original forty-eight chance outcomes.
The factor counts the possible interleavings of the two preserved subwords. -/
theorem partitionedOrder_cut_weight (result : Fin 6) (cut : Fin 4) :
    (∑ bits : TimingBits, ∑ index : Fin 6,
      if partitionedOrder bits index = callbackOrder result ∧ goodCount bits = cut.val
      then 9 ^ goodCount bits else 0) = Nat.choose 3 cut.val * 9 ^ cut.val := by
  fin_cases result <;> fin_cases cut <;> decide

/-- An original good-service bit has probability nine tenths. -/
def timingCoin : PMF Bool :=
  PMF.ofFintype (fun bit => ENNReal.ofReal (if bit then (9 / 10 : ℝ) else 1 / 10))
    (by
      norm_num only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 9 / 10)
        (by norm_num : (0 : ℝ) ≤ 1 / 10)]
      norm_num)

/-- All three bits are drawn independently before the physical run. -/
def timingBitsLaw : PMF TimingBits :=
  bindPairLaw timingCoin fun _ => bindPairLaw timingCoin fun _ => timingCoin

/-- The independent original bit vector and the uniform remainder order. -/
def callbackSeedLaw : PMF (TimingBits × Fin 6) :=
  bindPairLaw timingBitsLaw fun _ => PMF.uniformOfFintype (Fin 6)

theorem callbackSeedLaw_atom (bits : TimingBits) (index : Fin 6) :
    (callbackSeedLaw (bits, index)).toReal = (9 : ℝ) ^ goodCount bits / 6000 := by
  rcases bits with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;>
    norm_num [callbackSeedLaw, timingBitsLaw, timingCoin, bindPairLaw_apply,
      PMF.ofFintype_apply, ENNReal.toReal_mul, PMF.uniformOfFintype_apply, goodCount]

/-- The actual PMF has the uniform callback word independent of the binomial
cut. This identity permits an arbitrary continuation kernel of the two outputs. -/
theorem callbackSeedLaw_partition_expect (continuation : List (Fin 3) → Nat → ℝ) :
    expect callbackSeedLaw (fun seed =>
      continuation (partitionedOrder seed.1 seed.2) (goodCount seed.1)) =
      ∑ index : Fin 6,
        (continuation (callbackOrder index) 0 +
          27 * continuation (callbackOrder index) 1 +
          243 * continuation (callbackOrder index) 2 +
          729 * continuation (callbackOrder index) 3) / 6000 := by
  rw [expect_eq_sum, Fintype.sum_prod_type]
  simp_rw [callbackSeedLaw_atom]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, goodCount,
    partitionedOrder, callbackOrder, timingGood]
  ring

/-- A full observed callback history may contribute any likelihood depending
on the callback word. It does not change the binomial cut distribution. -/
theorem callbackSeedLaw_order_likelihood (likelihood : List (Fin 3) → ℝ) :
    expect callbackSeedLaw (fun seed => likelihood (partitionedOrder seed.1 seed.2)) =
      (∑ index : Fin 6, likelihood (callbackOrder index)) / 6 := by
  rw [callbackSeedLaw_partition_expect (fun order _ => likelihood order)]
  norm_num [Fin.sum_univ_succ]
  ring

/-- Conditional behavioral likelihoods retain the exact mass of the all-good
original draw, including likelihoods of histories of vanishing probability. -/
theorem callbackSeedLaw_all_good_likelihood (likelihood : List (Fin 3) → ℝ) :
    expect callbackSeedLaw (fun seed => if goodCount seed.1 = 3 then
      likelihood (partitionedOrder seed.1 seed.2) else 0) =
      (729 / 1000 : ℝ) *
        expect callbackSeedLaw (fun seed => likelihood (partitionedOrder seed.1 seed.2)) := by
  rw [callbackSeedLaw_partition_expect
    (fun order count => if count = 3 then likelihood order else 0),
      callbackSeedLaw_order_likelihood]
  norm_num [Fin.sum_univ_succ]
  ring

/-- Under any nonnegative full-history likelihood independent of the cut,
the focal bad mass is at most the mass of a non-all-good original draw. -/
theorem callbackSeedLaw_bad_likelihood_le (owner : Fin 3)
    (likelihood : List (Fin 3) → ℝ) (nonnegative : ∀ order, 0 ≤ likelihood order) :
    expect callbackSeedLaw (fun seed => if timingGood seed.1 owner = false then
      likelihood (partitionedOrder seed.1 seed.2) else 0) ≤
      (271 / 1000 : ℝ) *
        expect callbackSeedLaw (fun seed => likelihood (partitionedOrder seed.1 seed.2)) := by
  have pointwise (seed : TimingBits × Fin 6) :
      (if timingGood seed.1 owner = false then likelihood (partitionedOrder seed.1 seed.2)
        else 0) ≤ likelihood (partitionedOrder seed.1 seed.2) -
          if goodCount seed.1 = 3 then likelihood (partitionedOrder seed.1 seed.2) else 0 := by
    by_cases allGood : goodCount seed.1 = 3
    · rw [all_good_of_goodCount seed.1 allGood owner]
      simp only [Bool.true_eq_false, ite_false, allGood, ite_true, sub_self, le_refl]
    · simp only [allGood, ite_false, sub_zero]
      split_ifs
      · exact le_rfl
      · exact nonnegative _
  have bound := expect_mono (μ := callbackSeedLaw) (fun seed _ => pointwise seed)
    (payoffIntegrable_of_finite callbackSeedLaw _) (payoffIntegrable_of_finite callbackSeedLaw _)
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    callbackSeedLaw_all_good_likelihood] at bound
  linarith

/-- Normalizing any positive behavioral likelihood gives the uniform bad-bit
posterior bound. No positive lower bound on the conditioning mass is required. -/
theorem callbackSeedLaw_bad_posterior_le (owner : Fin 3)
    (likelihood : List (Fin 3) → ℝ) (nonnegative : ∀ order, 0 ≤ likelihood order)
    (positive : 0 < expect callbackSeedLaw
      (fun seed => likelihood (partitionedOrder seed.1 seed.2))) :
    expect callbackSeedLaw (fun seed => if timingGood seed.1 owner = false then
      likelihood (partitionedOrder seed.1 seed.2) else 0) /
      expect callbackSeedLaw (fun seed => likelihood (partitionedOrder seed.1 seed.2)) ≤
        (271 / 1000 : ℝ) :=
  (div_le_iff₀ positive).mpr (callbackSeedLaw_bad_likelihood_le owner likelihood nonnegative)

/-- The same normalized full-history likelihood retains all-good probability
exactly, which is the chance lower bound for the original no-reset branch. -/
theorem callbackSeedLaw_all_good_posterior (likelihood : List (Fin 3) → ℝ)
    (positive : 0 < expect callbackSeedLaw
      (fun seed => likelihood (partitionedOrder seed.1 seed.2))) :
    expect callbackSeedLaw (fun seed => if goodCount seed.1 = 3 then
      likelihood (partitionedOrder seed.1 seed.2) else 0) /
      expect callbackSeedLaw (fun seed => likelihood (partitionedOrder seed.1 seed.2)) =
        (729 / 1000 : ℝ) := by
  rw [callbackSeedLaw_all_good_likelihood]
  exact mul_div_cancel_right₀ _ (ne_of_gt positive)

/-- The original uniform order as an actual permutation of the native owners. -/
def callbackPermutationFunction (index : Fin 6) (position : Fin 3) : Fin 3 :=
  match index.val with
  | 0 => ![0, 1, 2] position
  | 1 => ![0, 2, 1] position
  | 2 => ![1, 0, 2] position
  | 3 => ![1, 2, 0] position
  | 4 => ![2, 0, 1] position
  | _ => ![2, 1, 0] position

def callbackPermutation (index : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (callbackPermutationFunction index) (by fin_cases index <;> decide)

theorem callbackPermutation_word (index : Fin 6) :
    List.ofFn (callbackPermutation index) = callbackOrder index := by
  fin_cases index <;> rfl

/-- The concrete original prior consumed by the native scheduler. It retains
the one initialized independent order and all three original event seeds. -/
def nativeSeedLaw : PMF ((Equiv.Perm (Fin 3)) × (Fin 3 → Bool)) :=
  callbackSeedLaw.map fun seed => (callbackPermutation seed.2, timingGood seed.1)

/-- The literal good-before-middle, bad-after-middle callback word read by
the native command selector. -/
def nativePartitionedOrder (seed : (Equiv.Perm (Fin 3)) × (Fin 3 → Bool)) :
    List (Fin 3) :=
  (List.ofFn seed.1).filter seed.2 ++ (List.ofFn seed.1).filter (fun owner => !(seed.2 owner))

def nativeGoodCount (seed : (Equiv.Perm (Fin 3)) × (Fin 3 → Bool)) : Nat :=
  ((List.ofFn seed.1).filter seed.2).length

theorem nativePartitionedOrder_original (bits : TimingBits) (index : Fin 6) :
    nativePartitionedOrder (callbackPermutation index, timingGood bits) =
      partitionedOrder bits index := by
  simp only [nativePartitionedOrder, callbackPermutation_word, partitionedOrder]

theorem nativeGoodCount_original (bits : TimingBits) (index : Fin 6) :
    nativeGoodCount (callbackPermutation index, timingGood bits) = goodCount bits := by
  rcases bits with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;> fin_cases index <;> decide

/-- The native original chance kernel has the exact uniform-order and
binomial-cut factorization, for every real continuation readout. -/
theorem nativeSeedLaw_partition_expect (continuation : List (Fin 3) → Nat → ℝ) :
    expect nativeSeedLaw (fun seed =>
      continuation (nativePartitionedOrder seed) (nativeGoodCount seed)) =
      ∑ index : Fin 6,
        (continuation (callbackOrder index) 0 +
          27 * continuation (callbackOrder index) 1 +
          243 * continuation (callbackOrder index) 2 +
          729 * continuation (callbackOrder index) 3) / 6000 := by
  rw [nativeSeedLaw, expect_map]
  simpa only [Function.comp_def, nativePartitionedOrder_original, nativeGoodCount_original] using
    callbackSeedLaw_partition_expect continuation

/-- Arbitrary nonnegative behavioral likelihoods of the actual native
callback word retain the same uniform bad-seed bound before normalization. -/
theorem nativeSeedLaw_bad_likelihood_le (owner : Fin 3)
    (likelihood : List (Fin 3) → ℝ) (nonnegative : ∀ order, 0 ≤ likelihood order) :
    expect nativeSeedLaw (fun seed => if seed.2 owner = false then
      likelihood (nativePartitionedOrder seed) else 0) ≤
      (271 / 1000 : ℝ) * expect nativeSeedLaw
        (fun seed => likelihood (nativePartitionedOrder seed)) := by
  simp only [nativeSeedLaw, expect_map, Function.comp_def, nativePartitionedOrder_original]
  exact callbackSeedLaw_bad_likelihood_le owner likelihood nonnegative

/-- In the same initialized native kernel, the weighted no-failure chance
is exact and never uses a newly sampled event seed at the callback. -/
theorem nativeSeedLaw_all_good_likelihood (likelihood : List (Fin 3) → ℝ) :
    expect nativeSeedLaw (fun seed => if nativeGoodCount seed = 3 then
      likelihood (nativePartitionedOrder seed) else 0) =
      (729 / 1000 : ℝ) * expect nativeSeedLaw
        (fun seed => likelihood (nativePartitionedOrder seed)) := by
  simp only [nativeSeedLaw, expect_map, Function.comp_def, nativePartitionedOrder_original,
    nativeGoodCount_original]
  exact callbackSeedLaw_all_good_likelihood likelihood

theorem nativeSeedLaw_bad_posterior_le (owner : Fin 3)
    (likelihood : List (Fin 3) → ℝ) (nonnegative : ∀ order, 0 ≤ likelihood order)
    (positive : 0 < expect nativeSeedLaw (fun seed => likelihood (nativePartitionedOrder seed))) :
    expect nativeSeedLaw (fun seed => if seed.2 owner = false then
      likelihood (nativePartitionedOrder seed) else 0) /
      expect nativeSeedLaw (fun seed => likelihood (nativePartitionedOrder seed)) ≤
        (271 / 1000 : ℝ) :=
  (div_le_iff₀ positive).mpr (nativeSeedLaw_bad_likelihood_le owner likelihood nonnegative)

end Vegas.Examples.CommitSeedBroadcast
