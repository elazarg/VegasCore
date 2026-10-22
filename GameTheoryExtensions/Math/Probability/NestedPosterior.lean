/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Support
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

/-- Conditioning an original tagged hierarchical draw first updates its outer
index, then its original inner law at that index. Inner zero-mass observations
remain harmless because their outer posterior mass is zero. -/
theorem fiberPosterior_hierarchical_pair {Outer Inner Output : Type}
    (prior : PMF Outer) (kernel : Outer → PMF (Output × Inner)) (output : Output)
    (present : output ∈ (prior.bind fun index => (kernel index).map Prod.fst).support) :
    let joint := (bindPairLaw prior kernel).map fun pair => (pair.2.1, (pair.1, pair.2.2))
    let outer := prior.bind fun index =>
      ((kernel index).map Prod.fst).map fun value => (value, index)
    (fiberPosterior joint Prod.fst output).map Prod.snd =
      ((fiberPosterior outer Prod.fst output).map Prod.snd).bind fun index =>
        ((fiberPosterior (kernel index) Prod.fst output).map Prod.snd).map (Prod.mk index) := by
  classical
  dsimp only
  let joint := (bindPairLaw prior kernel).map fun pair => (pair.2.1, (pair.1, pair.2.2))
  let outer := prior.bind fun index => ((kernel index).map Prod.fst).map fun value => (value, index)
  have jointMarginal : joint.map Prod.fst = prior.bind fun index =>
      (kernel index).map Prod.fst := by
    simp only [joint, bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have outerMarginal : outer.map Prod.fst = prior.bind fun index =>
      (kernel index).map Prod.fst := by
    simp only [outer, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have jointPresent : output ∈ (joint.map Prod.fst).support := by
    rw [jointMarginal]
    exact present
  have outerPresent : output ∈ (outer.map Prod.fst).support := by
    rw [outerMarginal]
    exact present
  have jointAt (index : Outer) (inner : Inner) :
      joint (output, (index, inner)) = prior index * kernel index (output, inner) := by
    have injective : Function.Injective
        (fun pair : Outer × (Output × Inner) => (pair.2.1, (pair.1, pair.2.2))) := by
      rintro ⟨first, ⟨value, memory⟩⟩ ⟨second, ⟨other, next⟩⟩ same
      obtain ⟨rfl, equal⟩ := Prod.mk.inj same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      rfl
    change (PMF.map _ (bindPairLaw prior kernel))
      ((fun pair : Outer × (Output × Inner) => (pair.2.1, (pair.1, pair.2.2)))
        (index, (output, inner))) = _
    rw [pmf_map_apply_of_injective _ injective, bindPairLaw_apply]
  have outerAt (index : Outer) :
      outer (output, index) = prior index * (kernel index).map Prod.fst output :=
    bind_map_tag_apply prior (fun index => (kernel index).map Prod.fst) output index
  change (fiberPosterior joint Prod.fst output).map Prod.snd =
    bindPairLaw ((fiberPosterior outer Prod.fst output).map Prod.snd)
      (fun index => (fiberPosterior (kernel index) Prod.fst output).map Prod.snd)
  ext ⟨index, inner⟩
  rw [fiberPosterior_map_snd_apply joint output jointPresent (index, inner), bindPairLaw_apply,
    fiberPosterior_map_snd_apply outer output outerPresent index, jointAt, outerAt,
    jointMarginal, outerMarginal]
  rw [← mul_fiberPosterior_map_snd_apply (kernel index) output inner]
  ac_rfl

end GameTheory.Math.Probability
