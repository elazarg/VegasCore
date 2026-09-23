/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Regularity

/-! # Restoring the probability displaced by a regular proposal

Regularity permits an exact law factorization: the selection lottery is fixed,
and silence replaces only its fresh branch by a lottery over displaced old
choices. This is the distributional interface needed for continuation proofs.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α : Type*}

private theorem option_ext (first second : FinDist (Option α))
    (same : ∀ value, first.prob (some value) = second.prob (some value)) : first = second := by
  classical
  apply ext_of_prob
  intro value
  cases value with
  | some value => exact same value
  | none =>
      have total (law : FinDist (Option α)) : law.prob none +
          ∑' value, (if value = none then 0 else law.prob value) = 1 := by
        have sums : Summable law.prob := by simpa using law.summable_prob_mul (fun _ => 1)
        exact (sums.tsum_eq_add_tsum_ite none).symm.trans law.tsum_prob
      have left := total first
      have right := total second
      have tails : (fun value => if value = none then 0 else first.prob value) =
          (fun value => if value = none then 0 else second.prob value) := by
        funext value
        cases value <;> simp [same]
      rw [tails] at left
      linarith

private def keepProbability (before : FinDist α) (after : FinDist (Option α)) (value : α) : ℝ :=
  if 0 < before.prob value then after.prob (some value) / before.prob value else 0

private theorem keepProbability_bounds (before : FinDist α) (after : FinDist (Option α))
    (regular : (before.map some).RegularAt after none) (value : α) :
    0 ≤ keepProbability before after value ∧ keepProbability before after value ≤ 1 := by
  classical
  have bound := regular (some value) (by simp)
  rw [prob_map_of_injective some (Option.some_injective α)] at bound
  unfold keepProbability
  split
  · rename_i positive
    exact ⟨div_nonneg (after.prob_nonneg _) positive.le, (div_le_one positive).mpr bound⟩
  · exact ⟨le_rfl, zero_le_one⟩

private theorem keepProbability_mass (before : FinDist α) (after : FinDist (Option α))
    (regular : (before.map some).RegularAt after none) (value : α) :
    before.prob value * keepProbability before after value = after.prob (some value) := by
  classical
  have bound := regular (some value) (by simp)
  rw [prob_map_of_injective some (Option.some_injective α)] at bound
  unfold keepProbability
  split
  · rename_i positive
    field_simp
  · have zero : before.prob value = 0 := le_antisymm (by linarith) (before.prob_nonneg _)
    have other : after.prob (some value) = 0 :=
      le_antisymm (by simpa [zero] using bound) (after.prob_nonneg _)
    simp [other]

private def regularCoupling (before : FinDist α) (after : FinDist (Option α))
    (regular : (before.map some).RegularAt after none) : FinDist (Option α × α) :=
  before.bind fun value => mix (keepProbability before after value)
    (keepProbability_bounds before after regular value).1
    (keepProbability_bounds before after regular value).2
    (pure (some value, value)) (pure (none, value))

private theorem regularCoupling_snd (before : FinDist α) (after : FinDist (Option α))
    (regular : (before.map some).RegularAt after none) :
    (regularCoupling before after regular).map Prod.snd = before := by
  simp only [regularCoupling, map_bind, map_mix, map_pure, mix_self, bind_pure]

private theorem regularCoupling_fst (before : FinDist α) (after : FinDist (Option α))
    (regular : (before.map some).RegularAt after none) :
    (regularCoupling before after regular).map Prod.fst = after := by
  classical
  apply option_ext
  intro value
  simp only [regularCoupling, map_bind, map_mix, map_pure, prob_bind, prob_mix,
    prob_pure_eq_ite, Option.some.injEq, reduceCtorEq, ↓reduceIte, mul_zero, add_zero]
  have indicator : (fun candidate => keepProbability before after candidate *
      if value = candidate then 1 else 0) =
        fun candidate => if value = candidate then keepProbability before after value else 0 := by
    funext candidate
    by_cases same : value = candidate <;> simp [same]
  rw [indicator, expect_ite_eq]
  exact keepProbability_mass before after regular value

private theorem regularCoupling_supported (before : FinDist α) (after : FinDist (Option α))
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
  rw [← prob_pos_iff, prob_mix, prob_pure_of_ne first, prob_pure_of_ne second,
    mul_zero, mul_zero, add_zero] at selected
  exact (lt_irrefl _) selected

/-- The post-insertion lottery can simulate silence by restoring only the
fresh branch. The restoring law is independent of utilities and subsequent
continuation kernels. Zero probability of selecting fresh is included. -/
theorem regular_option_restore (before : FinDist α) (after : FinDist (Option α))
    (regular : (before.map some).RegularAt after none) :
    ∃ displaced : FinDist α,
      before = after.bind (fun selected => selected.elim displaced pure) := by
  classical
  let coupled := regularCoupling before after regular
  let displaced := (coupled.condOnFibre Prod.fst none).map Prod.snd
  refine ⟨displaced, ?_⟩
  calc
    before = coupled.map Prod.snd := (regularCoupling_snd before after regular).symm
    _ = (coupled.map Prod.fst).bind (fun selected =>
        (coupled.condOnFibre Prod.fst selected).map Prod.snd) := by
      conv_lhs => rw [coupled.eq_bind_condOnFibre Prod.fst]
      rw [map_bind]
    _ = after.bind (fun selected => selected.elim displaced pure) := by
      rw [regularCoupling_fst]
      apply bind_congr
      intro selected supported
      cases selected with
      | none => rfl
      | some value =>
          have mapped : some value ∈ (coupled.map Prod.fst).support := by
            rwa [regularCoupling_fst]
          obtain ⟨pair, member, observed⟩ := support_map .. ▸ mapped
          have meets : ∃ pair ∈ Prod.fst ⁻¹' {some value}, pair ∈ coupled.support :=
            ⟨pair, observed, member⟩
          rw [condOnFibre, dite_eq_left meets]
          calc
            _ = (coupled.condOn (Prod.fst ⁻¹' {some value}) meets).map (fun _ => value) := by
              apply map_congr_of_eq_on_support
              intro pair member
              have both := support_condOn coupled _ meets member
              have observed : pair.1 = some value := both.1
              rcases regularCoupling_supported before after regular pair both.2 with
                absent | present
              · rw [observed] at absent
                cases absent
              · exact Option.some.inj (present.symm.trans observed)
            _ = pure value := map_const _ _

end GameTheory.Math.Probability.FinDist
