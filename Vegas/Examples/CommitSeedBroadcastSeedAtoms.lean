/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAllGoodPrefix
import Vegas.Examples.CommitSeedBroadcastSeedIndependence

/-! # Original native atom bounds for the forty-eight timing draws -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open GameTheory.Math.Probability

theorem callbackPermutation_injective : Function.Injective callbackPermutation := by
  intro left right same
  apply callbackOrder_injective
  rw [← callbackPermutation_word left, ← callbackPermutation_word right, same]

theorem callbackPermutation_surjective : Function.Surjective callbackPermutation := by
  exact ((Fintype.bijective_iff_injective_and_card callbackPermutation).mpr
    ⟨callbackPermutation_injective, by norm_num [Fintype.card_perm]⟩).surjective

private theorem originalSeedMap_injective : Function.Injective
    (fun draw : TimingBits × Fin 6 => (callbackPermutation draw.2, timingGood draw.1)) := by
  intro left right same
  apply Prod.ext
  · exact timingGood_injective (Prod.mk.inj same).2
  · exact callbackPermutation_injective (Prod.mk.inj same).1

theorem nativeSeedLaw_atom (bits : TimingBits) (index : Fin 6) :
    (nativeSeedLaw (callbackPermutation index, timingGood bits)).toReal =
      (9 : ℝ) ^ goodCount bits / 6000 := by
  rw [nativeSeedLaw, pmf_map_apply_of_injective _ originalSeedMap_injective (bits, index)]
  exact callbackSeedLaw_atom bits index

theorem nativeSeedLaw_allGood_atom (order : Equiv.Perm Player) :
    (nativeSeedLaw (allGoodSeed order)).toReal = (729 : ℝ) / 6000 := by
  obtain ⟨index, rfl⟩ := callbackPermutation_surjective order
  have goods : timingGood (true, true, true) = fun _ => true := by
    funext owner
    fin_cases owner <;> rfl
  rw [allGoodSeed, ← goods, nativeSeedLaw_atom]
  norm_num [goodCount]

/-- The repaired all-good draw has at least the mass of every original draw.
The independent permutation is retained as an actual coordinate. -/
theorem nativeSeedLaw_atom_le_allGood (seed : Seeds) (order : Equiv.Perm Player) :
    (nativeSeedLaw seed).toReal ≤ (nativeSeedLaw (allGoodSeed order)).toReal := by
  rcases seed with ⟨permutation, assignment⟩
  obtain ⟨index, rfl⟩ := callbackPermutation_surjective permutation
  obtain ⟨bits, rfl⟩ := timingGood_surjective assignment
  rw [nativeSeedLaw_atom, nativeSeedLaw_allGood_atom]
  rcases bits with ⟨first, second, third⟩
  cases first <;> cases second <;> cases third <;> norm_num [goodCount]

theorem native_seed_card : Fintype.card Seeds = 48 := by
  change Fintype.card (Equiv.Perm (Fin 3) × (Fin 3 → Bool)) = 48
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_bool]
  norm_num

end Vegas.Examples.CommitSeedBroadcast
