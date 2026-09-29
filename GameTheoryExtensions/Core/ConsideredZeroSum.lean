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
    euPreference utility 0 (F.play (Profile.update other 0 (profile 0))) (F.play profile) ∧
      euPreference utility 0 (F.play profile)
        (F.play (Profile.update other 1 (profile 1))) := by
  constructor
  · have hle := hnash 1 (other 1) other₁
    rwa [hzero.euPreference_one_iff, update_one_eq_update_zero profile other] at hle
  · have hle := hnash 0 (other 0) other₀
    rwa [← update_one_eq_update_zero other profile] at hle

/-- **Coarse correlation over considered recommendations cannot change a
zero-sum value.** If no considered unilateral deviation improves on a profile,
every coarse correlated equilibrium that recommends only considered strategies
gives each player exactly that profile's extended expected payoff. The payoffs
need not be integrable. -/
theorem IsCoarseCorrelatedEq.extendedExpectedUtility_eq_of_zeroSum_considered
    (hzero : IsZeroSum utility) {law : PMF (Profile F.sig)}
    (hcce : IsCoarseCorrelatedEq F (euPreference utility) law)
    (hnash : ∀ who replacement, Considered who replacement →
      euPreference utility who (F.play profile) (F.play (Profile.update profile who replacement)))
    (recommended : ∀ other ∈ law.support, ∀ who, Considered who (other who)) (who : Fin 2) :
    extendedExpectedUtility utility who (F.outcomeLaw law) =
      extendedExpectedUtility utility who (F.play profile) := by
  have security (other : Profile F.sig) (hother : other ∈ law.support) :=
    zeroSum_security_of_considered hzero hnash other (recommended other hother 0)
      (recommended other hother 1)
  have lower : euPreference utility 0 (F.outcomeLaw law) (F.play profile) := by
    have hdev := (isCoarseCorrelatedEq_iff law).1 hcce 0 (profile 0)
    exact euPreference_transitive utility 0 _ _ _
      hdev (euPreference_bind_left law _ (fun other hother => (security other hother).1)
        hdev.2.1)
  have upper : euPreference utility 0 (F.play profile) (F.outcomeLaw law) := by
    have hdev := (isCoarseCorrelatedEq_iff law).1 hcce 1 (profile 1)
    rw [hzero.euPreference_one_iff] at hdev
    exact euPreference_transitive utility 0 _ _ _
      (euPreference_bind law _ (fun other hother => (security other hother).2) hdev.1) hdev
  have hsame := le_antisymm upper.2.2 lower.2.2
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · exact hsame
  · rw [hzero.extendedExpectedUtility_one lower.1,
      hzero.extendedExpectedUtility_one upper.1, hsame]

end GameTheory
