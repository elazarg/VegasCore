module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Core.Approximate

@[expose] public section

/-! # Nash preservation under support-local utility comparison

A payoff change preserves the prescribed equilibrium when it leaves honest
payoffs unchanged and never increases a deviating player's payoff on that
deviation's support. Only the new deviation payoffs need a separate expectation
existence premise; the original equilibrium and honest-support equality supply
all remaining expectation facts.
-/

noncomputable section

namespace GameTheory

open Math.Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι] {form : GameForm.{uι, us, uo} ι}
variable {upper lower : form.sig.Outcome → ι → ℝ} {ε : ℝ} {profile : Profile form.sig}

/-- Lowering deviation payoffs while fixing honest payoffs preserves the same
approximate Nash equilibrium. All comparisons are local to the relevant supports. -/
theorem IsεNash.of_utility_le_on_support
    (equilibrium : IsεNash form upper ε profile)
    (honest : ∀ who outcome, outcome ∈ (form.play profile).support →
      lower outcome who = upper outcome who)
    (deviating : ∀ who replacement outcome,
      outcome ∈ (form.play (Profile.update profile who replacement)).support →
        lower outcome who ≤ upper outcome who)
    (expectation : ∀ who replacement, UtilityHasExpectation lower who
      (form.play (Profile.update profile who replacement))) :
    IsεNash form lower ε profile := by
  rw [isεNash_iff] at equilibrium ⊢
  intro who replacement
  obtain ⟨base, _alternative, bound⟩ := equilibrium who replacement
  have same : extendedExpectedUtility lower who (form.play profile) =
      extendedExpectedUtility upper who (form.play profile) :=
    extendedExpect_congr_on_support (honest who)
  refine ⟨(hasExpectation_congr_on_support (honest who)).mpr base,
    expectation who replacement, ?_⟩
  calc
    extendedExpectedUtility lower who (form.play (Profile.update profile who replacement)) ≤
        extendedExpectedUtility upper who (form.play (Profile.update profile who replacement)) :=
      extendedExpect_mono (deviating who replacement)
    _ ≤ extendedExpectedUtility upper who (form.play profile) + ε := bound
    _ = extendedExpectedUtility lower who (form.play profile) + ε := by rw [same]

end GameTheory
