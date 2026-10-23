/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ConditionalObservation

/-! # Original hierarchical draws conditioned on a common observation -/

noncomputable section

namespace GameTheory.Math.Probability

/-- The observed marginal times the conditional second-coordinate atom is
the original joint atom, including at observations of zero mass. -/
theorem mul_fiberPosterior_map_snd_apply {Output Memory : Type}
    (joint : PMF (Output × Memory)) (output : Output) (memory : Memory) :
    (joint.map Prod.fst) output *
        ((fiberPosterior joint Prod.fst output).map Prod.snd) memory = joint (output, memory) := by
  by_cases present : output ∈ (joint.map Prod.fst).support
  · rw [fiberPosterior_map_snd_apply joint output present memory]
    have positive := (PMF.mem_support_iff _ _).mp present
    calc
      _ = joint (output, memory) *
          ((joint.map Prod.fst) output * ((joint.map Prod.fst) output)⁻¹) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel positive (PMF.apply_ne_top _ _), mul_one]
  · have zero := (PMF.apply_eq_zero_iff _ _).mpr present
    have jointZero : joint (output, memory) = 0 := by
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro member
      exact present ((PMF.mem_support_map_iff _ _ _).mpr ⟨(output, memory), member, rfl⟩)
    rw [zero, zero_mul, jointZero]

/-- The mass of an accumulated observation is its previous mass times the
conditional atom of the newly read coordinate. -/
theorem observation_fiber_mass {A B : Type} (law : PMF A)
    (old next : A → Bool) (field : A → B) (value : B)
    (present : true ∈ (law.map old).support)
    (same : ∀ point ∈ law.support,
      next point = true ↔ old point = true ∧ field point = value) :
    (law.map next) true = (law.map old) true *
      ((fiberPosterior law old true).map field) value := by
  classical
  let read := fun point => (old point, field point)
  let joint := law.map read
  have posterior : (fiberPosterior law old true).map read =
      fiberPosterior joint Prod.fst true := by
    exact map_fiberPosterior_readout law read Prod.fst true present
  have conditional : ((fiberPosterior joint Prod.fst true).map Prod.snd) =
      (fiberPosterior law old true).map field := by
    rw [← posterior, PMF.map_comp]
    rfl
  have marginal : joint.map Prod.fst = law.map old := by
    simp only [joint, PMF.map_comp, read, Function.comp_def]
  have atom : joint (true, value) = (law.map next) true := by
    rw [PMF.map_apply, PMF.map_apply]
    apply tsum_congr
    intro point
    by_cases supported : point ∈ law.support
    · have fiber := same point supported
      simp only [read, Prod.mk.injEq]
      have predicates : (true = old point ∧ value = field point) =
          (true = next point) := by
        apply propext
        simpa only [eq_comm] using fiber.symm
      by_cases condition : true = next point
      · rw [ite_eq_left (Eq.mpr predicates condition), ite_eq_left condition]
      · rw [ite_eq_right (fun original => condition (Eq.mp predicates original)),
          ite_eq_right condition]
    · have zero := (PMF.apply_eq_zero_iff law point).mpr supported
      simp only [zero, ite_self]
  have balance := mul_fiberPosterior_map_snd_apply joint true value
  rw [marginal, conditional, atom] at balance
  exact balance.symm

end GameTheory.Math.Probability
