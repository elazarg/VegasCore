/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.ZeroSum

/-! # Zero-sum values against a considered deviation class

`GameTheory.IsCoarseCorrelatedEq.expectedUtility_eq_of_zeroSum` fixes the value
of every coarse correlated equilibrium from a Nash profile. Its security step
only deviates to strategies that the correlation device actually recommends.
So a profile that is Nash only against a class of considered deviations still
fixes the value of every coarse correlated equilibrium whose recommendations
lie in that class.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
  {profile : Profile F.sig} {Considered : (who : Fin 2) → F.sig.Strategy who → Prop}

/-- A profile that no considered unilateral deviation improves on secures its
value against every opponent strategy that is considered. -/
theorem zeroSum_security_of_considered (hzero : IsZeroSum utility)
    (hnash : ∀ who replacement, Considered who replacement →
      euPreference utility who (F.play profile) (F.play (Profile.update profile who replacement)))
    (other : Profile F.sig) (other₀ : Considered 0 (other 0)) (other₁ : Considered 1 (other 1)) :
    expectedUtility utility 0 (F.play profile) ≤
        expectedUtility utility 0 (F.play (Profile.update other 0 (profile 0))) ∧
      expectedUtility utility 0 (F.play (Profile.update other 1 (profile 1))) ≤
        expectedUtility utility 0 (F.play profile) := by
  constructor
  · obtain ⟨_, _, hle⟩ := hnash 1 (other 1) other₁
    have hlaw := congrArg F.play (update_one_eq_update_zero profile other)
    rw [hzero.expectedUtility_one _, hzero.expectedUtility_one _] at hle
    have hrow := expectedUtility_congr_law utility 0 hlaw
    linarith
  · obtain ⟨_, _, hle⟩ := hnash 0 (other 0) other₀
    have hlaw := congrArg F.play (update_one_eq_update_zero other profile)
    rw [expectedUtility_congr_law utility 0 hlaw]
    exact hle

/-- **Coarse correlation over considered recommendations cannot change a
zero-sum value.** If no considered unilateral deviation improves on a profile,
every coarse correlated equilibrium that recommends only considered strategies
gives each player exactly that profile's payoff. -/
theorem IsCoarseCorrelatedEq.expectedUtility_eq_of_zeroSum_considered
    (hzero : IsZeroSum utility) {law : PMF (Profile F.sig)}
    (hcce : IsCoarseCorrelatedEq F (euPreference utility) law)
    (hnash : ∀ who replacement, Considered who replacement →
      euPreference utility who (F.play profile) (F.play (Profile.update profile who replacement)))
    (recommended : ∀ other ∈ law.support, ∀ who, Considered who (other who)) (who : Fin 2) :
    expectedUtility utility who (F.outcomeLaw law) =
      expectedUtility utility who (F.play profile) := by
  have hvalue := payoffIntegrable_constant law (expectedUtility utility 0 (F.play profile))
  have security (other : Profile F.sig) (hother : other ∈ law.support) :=
    zeroSum_security_of_considered hzero hnash other (recommended other hother 0)
      (recommended other hother 1)
  have lower : expectedUtility utility 0 (F.play profile) ≤
      expectedUtility utility 0 (F.outcomeLaw law) := by
    obtain ⟨_, hbind, hle⟩ := (isCoarseCorrelatedEq_iff law).1 hcce 0 (profile 0)
    rw [expectedUtility_bind utility 0 law _ hbind] at hle
    rw [← expect_constant law (expectedUtility utility 0 (F.play profile))]
    exact (expect_mono (fun other hother => (security other hother).1)
      hvalue (payoffIntegrable_bind_conditionalExpectation law _ _ hbind)).trans hle
  have upper : expectedUtility utility 0 (F.outcomeLaw law) ≤
      expectedUtility utility 0 (F.play profile) := by
    obtain ⟨_, hbind, hle⟩ := (isCoarseCorrelatedEq_iff law).1 hcce 1 (profile 1)
    have hbindZero := hzero.utilityIntegrable_zero_of_one _ hbind
    rw [hzero.expectedUtility_one _, hzero.expectedUtility_one _, neg_le_neg_iff,
      expectedUtility_bind utility 0 law _ hbindZero] at hle
    rw [← expect_constant law (expectedUtility utility 0 (F.play profile))]
    exact hle.trans (expect_mono (fun other hother => (security other hother).2)
      (payoffIntegrable_bind_conditionalExpectation law _ _ hbindZero) hvalue)
  have hsame := le_antisymm upper lower
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · exact hsame
  · rw [hzero.expectedUtility_one, hzero.expectedUtility_one, hsame]

end GameTheory
