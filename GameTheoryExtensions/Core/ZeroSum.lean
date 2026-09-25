/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.ZeroSum

/-! # Zero-sum equilibrium values for arbitrary strategy carriers

The strategies may themselves be behavioral policies. An existing two-player
zero-sum Nash equilibrium fixes the expected utility of every coarse correlated
equilibrium, including equilibria using strategies outside a compiler image.
This concerns expected utilities; neither terminal laws nor sequential
rationality follow from value equality.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}

private theorem cross_update (first second : Profile F.sig) :
    Profile.update first 1 (second 1) = Profile.update second 0 (first 0) := by
  funext who
  fin_cases who <;> simp

/-- A Nash strategy protects its equilibrium payoff against every opponent
strategy in a two-player zero-sum game. -/
theorem IsNash.zeroSum_security
    {profile : Profile F.sig} (nash : IsNash F (euPreference utility) profile)
    (zeroSum : IsZeroSum utility) (other : Profile F.sig) :
    expectedUtility utility 0 (F.play profile) ≤
      expectedUtility utility 0 (F.play (Profile.update other 0 (profile 0))) ∧
    expectedUtility utility 0 (F.play (Profile.update other 1 (profile 1))) ≤
      expectedUtility utility 0 (F.play profile) := by
  have first := (isNash_iff _).mp nash 0 (other 0)
  have second := (isNash_iff _).mp nash 1 (other 1)
  simp only [euPreference_apply] at first second
  rw [zeroSum.expectedUtility_one, zeroSum.expectedUtility_one] at second
  rw [cross_update profile other] at second
  rw [← cross_update other profile] at first
  exact ⟨neg_le_neg_iff.mp second, first⟩

/-- Coarse correlation cannot change the expected equilibrium payoff of a
two-player zero-sum game that has a Nash equilibrium in this strategy carrier. -/
theorem IsCoarseCorrelatedEq.expectedUtility_eq_of_zeroSum
    {law : FinDist (Profile F.sig)} {profile : Profile F.sig}
    (correlated : IsCoarseCorrelatedEq F (euPreference utility) law)
    (nash : IsNash F (euPreference utility) profile) (zeroSum : IsZeroSum utility)
    (who : Fin 2) :
    expectedUtility utility who (F.outcomeLaw law) =
      expectedUtility utility who (F.play profile) := by
  have first := (isCoarseCorrelatedEq_iff _).mp correlated 0 (profile 0)
  have second := (isCoarseCorrelatedEq_iff _).mp correlated 1 (profile 1)
  simp only [euPreference_apply] at first second
  rw [zeroSum.expectedUtility_one, zeroSum.expectedUtility_one] at second
  have lower : expectedUtility utility 0 (F.play profile) ≤
      expectedUtility utility 0 (F.outcomeLaw law) := by
    apply le_trans _ first
    rw [expectedUtility_bind]
    calc
      _ = law.expect (fun _ => expectedUtility utility 0 (F.play profile)) :=
        (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono fun other _ =>
        (nash.zeroSum_security zeroSum other).1
  have upper : expectedUtility utility 0 (F.outcomeLaw law) ≤
      expectedUtility utility 0 (F.play profile) := by
    apply le_trans (neg_le_neg_iff.mp second)
    rw [expectedUtility_bind]
    exact FinDist.expect_le_of_forall _ _ _ fun other _ =>
      (nash.zeroSum_security zeroSum other).2
  have same := le_antisymm upper lower
  fin_cases who
  · exact same
  · change expectedUtility utility 1 (F.outcomeLaw law) =
      expectedUtility utility 1 (F.play profile)
    rw [zeroSum.expectedUtility_one, zeroSum.expectedUtility_one, same]

/-- This applies directly to behavioral-policy game forms, without adding a
second layer of mixed strategies. -/
theorem IsNash.expectedUtility_eq_of_zeroSum
    {first second : Profile F.sig}
    (firstNash : IsNash F (euPreference utility) first)
    (secondNash : IsNash F (euPreference utility) second)
    (zeroSum : IsZeroSum utility) (who : Fin 2) :
    expectedUtility utility who (F.play first) =
      expectedUtility utility who (F.play second) := by
  have equality := (isNash_iff_isCoarseCorrelatedEq_pure first).mp firstNash
    |>.expectedUtility_eq_of_zeroSum secondNash zeroSum who
  simpa [GameForm.outcomeLaw] using equality

end GameTheory
