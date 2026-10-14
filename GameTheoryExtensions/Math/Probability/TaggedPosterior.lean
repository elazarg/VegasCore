/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ConditionalObservation

/-! # Conditioning a law with its deterministic observation attached

Retaining the sampled value beside a deterministic observation does not change
its posterior, including at observations outside the support.
-/

noncomputable section

namespace GameTheory.Math.Probability

theorem fiberPosterior_tag {Seed Output : Type} (law : PMF Seed) (choose : Seed → Output)
    (output : Output) :
    (fiberPosterior (law.map fun seed => (choose seed, seed)) Prod.fst output).map Prod.snd =
      fiberPosterior law choose output := by
  classical
  by_cases present : output ∈ (law.map choose).support
  · have transfer := fiberPosterior_bind_of_observation law
      (fun seed => PMF.pure (choose seed, seed)) choose Prod.fst
      (fun seed _ result supported => by
        cases (PMF.mem_support_pure_iff _ _).mp supported
        rfl) output present
    change fiberPosterior (law.map fun seed => (choose seed, seed)) Prod.fst output = _ at transfer
    rw [transfer, PMF.map_bind]
    simpa only [PMF.pure_map] using PMF.bind_pure (fiberPosterior law choose output)
  · have notPresent : output ∉
        ((law.map fun seed => (choose seed, seed)).map Prod.fst).support := by
      simpa only [PMF.map_comp, Function.comp_def] using present
    rw [fiberPosterior_of_not_mem_support _ _ notPresent,
      fiberPosterior_of_not_mem_support _ _ present, PMF.map_comp]
    change law.map id = law
    exact PMF.map_id _

end GameTheory.Math.Probability
