/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOrder
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Support

/-! # Independence of the actual original service coordinates and remainder order -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open scoped BigOperators
open GameTheory.Math.Probability

theorem timingGood_injective : Function.Injective timingGood := by
  intro first second same
  apply Prod.ext
  · exact congrFun same 0
  · apply Prod.ext
    · exact congrFun same 1
    · exact congrFun same 2

theorem timingGood_surjective : Function.Surjective timingGood := by
  intro assignment
  refine ⟨(assignment 0, assignment 1, assignment 2), ?_⟩
  funext owner
  fin_cases owner <;> rfl

/-- The actual three service bits are a product of their original fixed laws. -/
theorem timingBitsLaw_function :
    timingBitsLaw.map timingGood = independentProduct (fun _ : Fin 3 => timingCoin) := by
  ext assignment
  obtain ⟨bits, rfl⟩ := timingGood_surjective assignment
  rw [pmf_map_apply_of_injective timingBitsLaw timingGood_injective,
    independentProduct_apply]
  rcases bits with ⟨first, second, third⟩
  simp [timingBitsLaw, bindPairLaw_apply, Fin.prod_univ_succ, timingGood]

def remainderOrderLaw : PMF (Equiv.Perm (Fin 3)) :=
  (PMF.uniformOfFintype (Fin 6)).map callbackPermutation

/-- Relabeling the forty-eight original draws does not couple the remainder
permutation to any event seed. No later callback resamples this product. -/
theorem nativeSeedLaw_independent :
    nativeSeedLaw = bindPairLaw remainderOrderLaw
      (fun _ => independentProduct (fun _ : Fin 3 => timingCoin)) := by
  have swapped := bindPairLaw_const_map_swap timingBitsLaw
    (PMF.uniformOfFintype (Fin 6))
  have mapped := congrArg (fun law : PMF (Fin 6 × TimingBits) =>
    law.map fun draw => (callbackPermutation draw.1, timingGood draw.2)) swapped
  simp only [PMF.map_comp, Function.comp_def] at mapped
  change nativeSeedLaw = _ at mapped
  rw [← timingBitsLaw_function]
  rw [mapped]
  simp only [bindPairLaw, remainderOrderLaw, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]

theorem nativeSeedLaw_map_coordinates :
    nativeSeedLaw.map Prod.snd = independentProduct (fun _ : Fin 3 => timingCoin) := by
  rw [nativeSeedLaw_independent, bindPairLaw_map_snd, PMF.bind_const]

theorem nativeSeedLaw_map_coordinate (owner : Fin 3) :
    nativeSeedLaw.map (fun seed => seed.2 owner) = timingCoin := by
  have mapped := congrArg (fun law : PMF (Fin 3 → Bool) =>
    law.map fun bits => bits owner) nativeSeedLaw_map_coordinates
  simpa only [PMF.map_comp, Function.comp_def, independentProduct_map_eval] using mapped

end Vegas.Examples.CommitSeedBroadcast
