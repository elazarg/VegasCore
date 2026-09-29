/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Regularity

/-! # Positive weighted choice on finite sets

The weights are explicit mathematical inputs. Their relation to transaction
fees, propagation, or miner preferences is outside this probability model.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

variable {α : Type*}

def totalWeight (members : Finset α) (weight : α → ℝ) : ℝ := ∑ value ∈ members, weight value

theorem totalWeight_pos (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) :
    0 < totalWeight members weight :=
  Finset.sum_pos (fun value _ => positive value) nonempty

def weightedSet (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) : PMF α := by
  let total := totalWeight members weight
  have totalPositive : 0 < total := totalWeight_pos members nonempty weight positive
  let law : PMF {value // value ∈ members} := ofFintype
    (fun value => ENNReal.ofReal (weight value / total)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (f := fun value : {value // value ∈ members} => weight value / total) fun value _ =>
          div_nonneg (positive value).le totalPositive.le]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      have sum : (∑ value : {value // value ∈ members}, weight value) = total := by
        simp [total, totalWeight, Finset.sum_attach]
      rw [sum, mul_inv_cancel₀ (ne_of_gt totalPositive), ENNReal.ofReal_one])
  exact law.map Subtype.val

theorem prob_weightedSet [DecidableEq α]
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) (value : α) :
    ((weightedSet members nonempty weight positive) value).toReal =
      if value ∈ members then weight value / totalWeight members weight else 0 := by
  by_cases member : value ∈ members
  · change (((ofFintype _ _).map Subtype.val) (Subtype.val ⟨value, member⟩)).toReal = _
    rw [pmf_map_apply_of_injective _ Subtype.val_injective, ofFintype_apply,
      ENNReal.toReal_ofReal (div_nonneg (positive value).le
        (totalWeight_pos members nonempty weight positive).le)]
    simp only [member, ↓reduceIte, totalWeight]
  · rw [ite_eq_right member]
    have absent : value ∉ (weightedSet members nonempty weight positive).support := by
      rw [weightedSet, support_map]
      rintro ⟨old, _, same⟩
      exact member (same ▸ old.property)
    rw [(apply_eq_zero_iff _ _).mpr absent, ENNReal.toReal_zero]

theorem mem_support_weightedSet
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) (value : α) :
    value ∈ (weightedSet members nonempty weight positive).support ↔ value ∈ members := by
  classical
  rw [← pmf_toReal_pos_iff, prob_weightedSet]
  by_cases member : value ∈ members
  · simp only [member, ↓reduceIte, iff_true]
    exact div_pos (positive value) (totalWeight_pos members nonempty weight positive)
  · simp [member]

theorem weightedSet_one (members : Finset α) (nonempty : members.Nonempty) :
    weightedSet members nonempty (fun _ => 1) (fun _ => by norm_num) =
      PMF.uniformOfFinset members nonempty := by
  classical
  apply pmf_ext_toReal
  intro value
  by_cases member : value ∈ members <;>
    simp [prob_weightedSet, uniformOfFinset_apply, totalWeight, one_div, member]

/-- A fresh candidate scales all retained weights by the same factor. -/
theorem weightedSet_insert [DecidableEq α]
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value)
    (fresh : α) (absent : fresh ∉ members) :
    weightedSet (insert fresh members) (Finset.insert_nonempty fresh members) weight positive =
      mix (weight fresh / (weight fresh + totalWeight members weight))
        (div_nonneg (positive fresh).le
          (add_pos (positive fresh) (totalWeight_pos members nonempty weight positive)).le)
        ((div_le_one (add_pos (positive fresh)
          (totalWeight_pos members nonempty weight positive))).mpr
            (le_add_of_nonneg_right (totalWeight_pos members nonempty weight positive).le))
        (PMF.pure fresh) (weightedSet members nonempty weight positive) := by
  have totalPositive := totalWeight_pos members nonempty weight positive
  have newPositive := add_pos (positive fresh) totalPositive
  have total : totalWeight (insert fresh members) weight =
      weight fresh + totalWeight members weight := by
    simp only [totalWeight, Finset.sum_insert absent]
  apply pmf_ext_toReal
  intro value
  by_cases same : value = fresh
  · subst value
    simp only [prob_weightedSet, Finset.mem_insert_self, ↓reduceIte, total,
      mix_apply_toReal, pure_apply, absent, ENNReal.toReal_one, mul_one, mul_zero, add_zero]
  · by_cases member : value ∈ members
    · simp only [prob_weightedSet, Finset.mem_insert, same, member, or_true, ↓reduceIte,
        total, mix_apply_toReal, pure_apply, ENNReal.toReal_zero, mul_zero, zero_add]
      field_simp
      ring
    · simp only [prob_weightedSet, Finset.mem_insert, same, member, or_self, ↓reduceIte,
        mix_apply_toReal, pure_apply, ENNReal.toReal_zero, mul_zero, add_zero]

theorem weightedSet_regular_insert [DecidableEq α]
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value)
    (fresh : α) (absent : fresh ∉ members) :
    (weightedSet members nonempty weight positive).RegularAt
      (weightedSet (insert fresh members) (Finset.insert_nonempty fresh members) weight positive)
      fresh := by
  rw [weightedSet_insert members nonempty weight positive fresh absent]
  apply regularAt_mix

end PMF
