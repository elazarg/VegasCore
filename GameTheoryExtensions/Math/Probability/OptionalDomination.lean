/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Dominated optional readouts and integrable payoff comparisons

A dominated present part can be completed by a residual law. This actual law
identity supplies conditional integrability and a payoff comparison without a
finite carrier, an attained minimum, or a declared payoff floor.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

/-- **Residual of a dominated law.** If a law on `Option γ` puts at most `ν c` on
each `some c`, then `ν` is that law with its `none` branch replaced by some
residual law on `γ`. -/
theorem exists_residual_of_le {γ : Type*} (π : PMF (Option γ)) (ν : PMF γ)
    (dominated : ∀ c, π (some c) ≤ ν c) :
    ∃ residual : PMF γ, π.bind (fun outcome => outcome.elim residual PMF.pure) = ν := by
  classical
  have optionSum (f : Option γ → ENNReal) : ∑' outcome, f outcome = f none + ∑' c, f (some c) := by
    rw [ENNReal.tsum_eq_add_tsum_ite none]
    congr 1
    symm
    convert Function.Injective.tsum_eq (Option.some_injective γ) (f := fun outcome =>
      if outcome = none then (0 : ENNReal) else f outcome) ?_ using 1
    · simp
    · exact tsum_congr fun outcome => by split_ifs <;> rfl
    · intro outcome member
      cases outcome with
      | none => simp at member
      | some c => exact ⟨c, rfl⟩
  have split : π none + ∑' c, π (some c) = 1 := by
    rw [← optionSum (fun outcome => π outcome)]
    exact π.tsum_coe
  have someFinite : ∑' c, π (some c) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (split ▸ le_add_self)
  have gap : ∑' c, (ν c - π (some c)) = π none := by
    have whole : ∑' c, (ν c - π (some c)) + ∑' c, π (some c) = 1 := by
      rw [← ENNReal.tsum_add]
      simp only [tsub_add_cancel_of_le (dominated _)]
      exact ν.tsum_coe
    rw [← ENNReal.add_sub_cancel_right someFinite (a := ∑' c, (ν c - π (some c))), whole,
      ← split, ENNReal.add_sub_cancel_right someFinite]
  have apply (residual : PMF γ) (c : γ) :
      (π.bind fun outcome => outcome.elim residual PMF.pure) c =
        π none * residual c + π (some c) := by
    rw [PMF.bind_apply, optionSum]
    congr 1
    rw [tsum_eq_single c fun other different => by
      simp [PMF.pure_apply, Ne.symm different]]
    simp [PMF.pure_apply]
  by_cases empty : π none = 0
  · refine ⟨ν, PMF.ext fun c => ?_⟩
    rw [apply, empty, zero_mul, zero_add]
    have zero : ν c - π (some c) = 0 :=
      ENNReal.tsum_eq_zero.mp (gap.trans empty) c
    exact le_antisymm (dominated c) (tsub_eq_zero_iff_le.mp zero)
  · have finite : π none ≠ ⊤ := PMF.apply_ne_top π none
    refine ⟨PMF.normalize (fun c => ν c - π (some c)) (gap ▸ empty) (gap ▸ finite),
      PMF.ext fun c => ?_⟩
    rw [apply, PMF.normalize_apply, gap, mul_comm, mul_assoc, ENNReal.inv_mul_cancel empty finite,
      mul_one, tsub_add_cancel_of_le (dominated c)]

end PMF

namespace GameTheory.Math.Probability

/-- Reading an embedding backwards retains exactly its original atom, with
all points outside the image sent to none. No ambient finiteness is needed. -/
theorem map_partialInv_apply {Source Target : Type*} (law : PMF Target)
    (embedding : Source ↪ Target) (outcome : Source) :
    (law.map (Function.partialInv embedding)) (some outcome) = law (embedding outcome) := by
  classical
  have condition (point : Target) :
      some outcome = Function.partialInv embedding point ↔ point = embedding outcome := by
    constructor
    · intro same
      exact ((embedding.injective.isPartialInv outcome point).mp same.symm).symm
    · intro same
      subst point
      exact (Function.partialInv_left embedding.injective outcome).symm
  rw [PMF.map_apply]
  simp only [condition]
  simp

/-- A failed partial-inverse readout means precisely that the point is outside
the embedding image; this supplies the protocol's debt-classification premise. -/
theorem partialInv_eq_none_iff {Source Target : Type*} (embedding : Source ↪ Target)
    (point : Target) :
    Function.partialInv embedding point = none ↔ point ∉ Set.range embedding := by
  constructor
  · rintro absent ⟨outcome, rfl⟩
    rw [Function.partialInv_left embedding.injective] at absent
    cases absent
  · intro outside
    cases reading : Function.partialInv embedding point with
    | none => rfl
    | some outcome =>
        exact (outside ⟨outcome,
          (embedding.injective.isPartialInv outcome point).mp reading⟩).elim

/-- An integrable comparison through a partially defined readout. Successful
readouts are atomwise dominated by the reference. Every failed supported point
is worse than every supported reference outcome. No floor or minimum is needed. -/
theorem expect_le_of_dominated_readout {Source Target : Type*}
    (law : PMF Source) (reference : PMF Target) (decode : Source → Option Target)
    (dominated : ∀ outcome, (law.map decode) (some outcome) ≤ reference outcome)
    (value : Source → ℝ) (better : Target → ℝ)
    (valueIntegrable : PayoffIntegrable law value)
    (betterIntegrable : PayoffIntegrable reference better)
    (successful : ∀ point ∈ law.support, ∀ outcome,
      decode point = some outcome → value point ≤ better outcome)
    (failed : ∀ point ∈ law.support, decode point = none →
      ∀ outcome ∈ reference.support, value point ≤ better outcome) :
    expect law value ≤ expect reference better := by
  obtain ⟨residual, rebuilt⟩ := PMF.exists_residual_of_le (law.map decode) reference dominated
  let kernel : Source → PMF Target := fun point => (decode point).elim residual PMF.pure
  have kernelLaw : law.bind kernel = reference := by
    simpa only [PMF.bind_map, Function.comp_def] using rebuilt
  have integrable : PayoffIntegrable (law.bind kernel) better := by
    simpa only [kernelLaw] using betterIntegrable
  have ordered (point : Source) (supported : point ∈ law.support) :
      value point ≤ expect (kernel point) better := by
    cases reading : decode point with
    | some outcome =>
        simpa only [kernel, reading, Option.elim_some, expect_pure] using
          successful point supported outcome reading
    | none =>
        have conditional := payoffIntegrable_bind_conditional_on_support law kernel better
          integrable point supported
        have bound : expect (kernel point) (fun _ => value point) ≤
            expect (kernel point) better := by
          refine expect_mono (fun outcome member => ?_)
            (payoffIntegrable_constant _ _) conditional
          apply failed point supported reading outcome
          rw [← kernelLaw, PMF.mem_support_bind_iff]
          exact ⟨point, supported, member⟩
        simpa only [expect_constant] using bound
  calc
    expect law value ≤ expect law (fun point => expect (kernel point) better) :=
      expect_mono ordered valueIntegrable
        (payoffIntegrable_bind_conditionalExpectation law kernel better integrable)
    _ = expect reference better := by
      rw [← expect_bind_tower law kernel better integrable, kernelLaw]

end GameTheory.Math.Probability
