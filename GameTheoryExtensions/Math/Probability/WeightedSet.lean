/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Regularity

/-! # Positive weighted choice on finite sets

The weights are explicit mathematical inputs. Their relation to transaction
fees, propagation, or miner preferences is outside this probability model.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α : Type*}

def totalWeight (members : Finset α) (weight : α → ℝ) : ℝ := ∑ value ∈ members, weight value

theorem totalWeight_pos (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) :
    0 < totalWeight members weight :=
  Finset.sum_pos (fun value _ => positive value) nonempty

def weightedSet (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) : FinDist α := by
  let total := totalWeight members weight
  have totalPositive : 0 < total := totalWeight_pos members nonempty weight positive
  let law : FinDist {value // value ∈ members} := ofWeights
    (fun value => weight value / total)
    (fun value => div_nonneg (positive value).le totalPositive.le) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      have sum : (∑ value : {value // value ∈ members}, weight value) = total := by
        simp [total, totalWeight, Finset.sum_attach]
      rw [sum, mul_inv_cancel₀ (ne_of_gt totalPositive)])
  exact law.map Subtype.val

theorem prob_weightedSet [DecidableEq α]
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) (value : α) :
    (weightedSet members nonempty weight positive).prob value =
      if value ∈ members then weight value / totalWeight members weight else 0 := by
  by_cases member : value ∈ members
  · change ((ofWeights _ _ _).map Subtype.val).prob (Subtype.val ⟨value, member⟩) = _
    rw [prob_map_of_injective Subtype.val Subtype.val_injective, prob_ofWeights]
    simp only [member, ↓reduceIte]
  · rw [weightedSet, prob_map]
    have absent : (fun old : {value // value ∈ members} =>
        if value = old.val then (1 : ℝ) else 0) = fun _ => 0 := by
      funext old
      apply ite_eq_right
      intro same
      exact member (same ▸ old.property)
    rw [absent, expect_const, ite_eq_right member]

theorem mem_support_weightedSet
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value) (value : α) :
    value ∈ (weightedSet members nonempty weight positive).support ↔ value ∈ members := by
  classical
  rw [← prob_pos_iff, prob_weightedSet]
  by_cases member : value ∈ members
  · simp only [member, ↓reduceIte, iff_true]
    exact div_pos (positive value) (totalWeight_pos members nonempty weight positive)
  · simp [member]

theorem weightedSet_one (members : Finset α) (nonempty : members.Nonempty) :
    weightedSet members nonempty (fun _ => 1) (fun _ => by norm_num) =
      uniformSet members nonempty := by
  classical
  apply ext_of_prob
  intro value
  simp [prob_weightedSet, prob_uniformSet, totalWeight, one_div]

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
        (pure fresh) (weightedSet members nonempty weight positive) := by
  have totalPositive := totalWeight_pos members nonempty weight positive
  have newPositive := add_pos (positive fresh) totalPositive
  have total : totalWeight (insert fresh members) weight =
      weight fresh + totalWeight members weight := by
    simp only [totalWeight, Finset.sum_insert absent]
  apply ext_of_prob
  intro value
  by_cases same : value = fresh
  · subst value
    simp only [prob_weightedSet, Finset.mem_insert_self, ↓reduceIte, total,
      prob_mix, prob_pure_self, absent, mul_one, mul_zero, add_zero]
  · by_cases member : value ∈ members
    · simp only [prob_weightedSet, Finset.mem_insert, same, member, or_true, ↓reduceIte,
        total, prob_mix, prob_pure_of_ne same, mul_zero, zero_add]
      field_simp
      ring
    · simp only [prob_weightedSet, Finset.mem_insert, same, member, or_self, ↓reduceIte,
        prob_mix, prob_pure_of_ne same, mul_zero, add_zero]

theorem weightedSet_regular_insert [DecidableEq α]
    (members : Finset α) (nonempty : members.Nonempty)
    (weight : α → ℝ) (positive : ∀ value, 0 < weight value)
    (fresh : α) (absent : fresh ∉ members) :
    (weightedSet members nonempty weight positive).RegularAt
      (weightedSet (insert fresh members) (Finset.insert_nonempty fresh members) weight positive)
      fresh := by
  rw [weightedSet_insert members nonempty weight positive fresh absent]
  apply regularAt_mix

end GameTheory.Math.Probability.FinDist
