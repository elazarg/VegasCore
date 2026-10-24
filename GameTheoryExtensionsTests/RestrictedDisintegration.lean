/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.RestrictedDisintegration

/-! # Conditioning two independent bits

Retaining the first bit leaves the original law of the second bit as the
mixture coefficient. Selecting the second bit as well multiplies their two
masses. At an impossible first-bit observation the total posterior instead
retains the original law; the positive-restriction theorem does not apply.
-/

noncomputable section

namespace GameTheoryExtensionsTests.RestrictedDisintegration

open GameTheory.Math.Probability

/-- The same factored atoms determine a retained-bit posterior and the mass
of its refinement, for arbitrary independent bit distributions. -/
theorem independent_bits_restrictions (first second : PMF Bool)
    (firstPossible : true ∈ first.support) (secondPossible : true ∈ second.support) :
    let joint := bindPairLaw first (fun _ => second)
    fiberPosterior joint Prod.fst true = second.map (fun bit => (true, bit)) ∧
      (joint.map (fun bits => bits.1 && bits.2)) true = first true * second true := by
  classical
  intro joint
  have positive : true ∈ (second.map id).support := by
    simpa only [PMF.map_id] using secondPossible
  obtain ⟨_, _, _, _, posterior, mass, _⟩ :=
    fiberPosteriors_of_factored_restriction joint second Prod.snd Prod.fst id
      (fun bit => PMF.pure (true, bit)) (first true)
      ((PMF.mem_support_iff _ _).mp firstPossible) positive (by
        intro label point
        rcases point with ⟨bit, read⟩
        cases bit <;> cases label <;> cases read <;>
          simp [joint, bindPairLaw_apply, PMF.pure_apply])
  constructor
  · exact posterior.trans (PMF.bind_pure_comp (fun bit => (true, bit)) second)
  · simpa only [PMF.map_id, id_eq] using mass

/-- An observation outside the support uses the original total-posterior
fallback, rather than an arbitrarily selected law on the empty fiber. -/
theorem absent_first_bit (second : PMF Bool) :
    fiberPosterior (bindPairLaw (PMF.pure false) (fun _ => second)) Prod.fst true =
      bindPairLaw (PMF.pure false) (fun _ => second) := by
  apply fiberPosterior_of_not_mem_support
  simp [bindPairLaw_map_fst]

/-- A zero restricted mass identifies the event probability even though it
does not identify a posterior: every candidate conditional has the same atoms. -/
theorem absent_restriction_mass (conditional : PMF Bool) :
    ((PMF.pure false).map id) true = 0 := by
  apply observation_mass_of_scaled_restriction (PMF.pure false) conditional id 0
  intro bit
  cases bit <;> simp [PMF.pure_apply]

end GameTheoryExtensionsTests.RestrictedDisintegration
