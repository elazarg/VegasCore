/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Regularity

/-! # Restoring the probability displaced by a regular proposal

Regularity permits an exact law factorization: the selection lottery is fixed,
and silence replaces only its fresh branch by a lottery over displaced old
choices. This is the distributional interface needed for continuation proofs.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {α : Type*}

private theorem option_ext (first second : PMF (Option α))
    (same : ∀ value, (first (some value)).toReal = (second (some value)).toReal) :
    first = second := by
  classical
  have sameMass (value : α) : first (some value) = second (some value) :=
    (ENNReal.toReal_eq_toReal_iff' (first.apply_ne_top _) (second.apply_ne_top _)).mp (same value)
  ext value
  cases value with
  | some value => exact sameMass value
  | none =>
      have total (law : PMF (Option α)) :
          law none + ∑' value, (if value = none then 0 else law value) = 1 := by
        convert (ENNReal.tsum_eq_add_tsum_ite (f := ⇑law) none).symm.trans law.tsum_coe using 4
        congr 1
      have tails : (fun value => if value = none then 0 else first value) =
          (fun value => if value = none then 0 else second value) := by
        funext value
        cases value <;> simp [sameMass]
      have finite : ∑' value, (if value = none then 0 else second value) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (total second ▸ le_add_self)
      have equal := (total first).trans (total second).symm
      rw [tails] at equal
      exact (ENNReal.add_left_inj finite).mp equal

private def keepProbability (before : PMF α) (after : PMF (Option α)) (value : α) : ℝ :=
  if 0 < (before value).toReal then (after (some value)).toReal / (before value).toReal else 0

private theorem keepProbability_bounds (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) (value : α) :
    0 ≤ keepProbability before after value ∧ keepProbability before after value ≤ 1 := by
  classical
  have bound := regular (some value) (by simp)
  rw [pmf_map_apply_of_injective _ (Option.some_injective α)] at bound
  unfold keepProbability
  split
  · rename_i positive
    exact ⟨div_nonneg ENNReal.toReal_nonneg positive.le, (div_le_one positive).mpr bound⟩
  · exact ⟨le_rfl, zero_le_one⟩

private theorem keepProbability_mass (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) (value : α) :
    (before value).toReal * keepProbability before after value = (after (some value)).toReal := by
  classical
  have bound := regular (some value) (by simp)
  rw [pmf_map_apply_of_injective _ (Option.some_injective α)] at bound
  unfold keepProbability
  split
  · rename_i positive
    field_simp
  · have zero : (before value).toReal = 0 := le_antisymm (by linarith) ENNReal.toReal_nonneg
    have other : (after (some value)).toReal = 0 :=
      le_antisymm (by simpa [zero] using bound) ENNReal.toReal_nonneg
    simp [other]

private def regularCoupling (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) : PMF (Option α × α) :=
  before.bind fun value => mix (keepProbability before after value)
    (keepProbability_bounds before after regular value).1
    (keepProbability_bounds before after regular value).2
    (PMF.pure (some value, value)) (PMF.pure (none, value))

private theorem regularCoupling_snd (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) :
    (regularCoupling before after regular).map Prod.snd = before := by
  simp only [regularCoupling, map_bind, mix_map, PMF.pure_map, mix_self, bind_pure]

private theorem regularCoupling_fst (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) :
    (regularCoupling before after regular).map Prod.fst = after := by
  classical
  apply option_ext
  intro value
  simp only [regularCoupling, map_bind, mix_map, PMF.pure_map, toReal_bind_apply,
    mix_apply_toReal, pure_apply, Option.some.injEq, reduceCtorEq, ↓reduceIte,
    ENNReal.toReal_zero, mul_zero, add_zero]
  have indicator : (fun candidate => keepProbability before after candidate *
      (if value = candidate then (1 : ENNReal) else 0).toReal) =
        fun candidate => if value = candidate then keepProbability before after value else 0 := by
    funext candidate
    by_cases same : value = candidate <;> simp [same]
  rw [indicator, expect_ite_eq]
  exact keepProbability_mass before after regular value

private theorem regularCoupling_supported (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) (pair : Option α × α)
    (member : pair ∈ (regularCoupling before after regular).support) :
    pair.1 = none ∨ pair.1 = some pair.2 := by
  classical
  obtain ⟨value, _, selected⟩ := Set.mem_iUnion₂.mp (support_bind .. ▸ member)
  by_contra incompatible
  have first : pair ≠ (some value, value) := by
    rintro rfl
    exact incompatible (Or.inr rfl)
  have second : pair ≠ (none, value) := by
    rintro rfl
    exact incompatible (Or.inl rfl)
  rw [← pmf_toReal_pos_iff, mix_apply_toReal, pure_apply, pure_apply, ite_eq_right first,
    ite_eq_right second, ENNReal.toReal_zero, mul_zero, mul_zero, add_zero] at selected
  exact (lt_irrefl _) selected

/-- The post-insertion lottery can simulate silence by restoring only the
fresh branch. The restoring law is independent of utilities and subsequent
continuation kernels. Zero probability of selecting fresh is included. -/
theorem regular_option_restore (before : PMF α) (after : PMF (Option α))
    (regular : (before.map some).RegularAt after none) :
    ∃ displaced : PMF α,
      before = after.bind (fun selected => selected.elim displaced pure) := by
  classical
  let coupled := regularCoupling before after regular
  let displaced := (fiberPosterior coupled Prod.fst none).map Prod.snd
  refine ⟨displaced, ?_⟩
  calc
    before = coupled.map Prod.snd := (regularCoupling_snd before after regular).symm
    _ = (coupled.map Prod.fst).bind (fun selected =>
        (fiberPosterior coupled Prod.fst selected).map Prod.snd) := by
      conv_lhs => rw [← fiberPosterior_reconstruct coupled Prod.fst]
      rw [map_bind]
    _ = after.bind (fun selected => selected.elim displaced pure) := by
      rw [regularCoupling_fst]
      apply bind_congr_on_support _
      intro selected supported
      cases selected with
      | none => rfl
      | some value =>
          have mapped : some value ∈ (coupled.map Prod.fst).support := by
            rwa [regularCoupling_fst]
          obtain ⟨pair, member, observed⟩ := support_map .. ▸ mapped
          have meets : ∃ pair ∈ Prod.fst ⁻¹' {some value}, pair ∈ coupled.support :=
            ⟨pair, observed, member⟩
          rw [fiberPosterior_eq_filter _ _ meets]
          calc
            _ = (coupled.filter (Prod.fst ⁻¹' {some value}) meets).map (fun _ => value) := by
              apply map_congr_on_support _
              intro pair member
              have both := (PMF.mem_support_filter_iff meets).mp member
              have observed : pair.1 = some value := both.1
              rcases regularCoupling_supported before after regular pair both.2 with
                absent | present
              · rw [observed] at absent
                cases absent
              · exact Option.some.inj (present.symm.trans observed)
            _ = PMF.pure value := PMF.map_const _ _

end PMF
