/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Nash
import GameTheoryExtensions.Math.Probability.Tremble

/-! # Simultaneous best responses with fixed agents and mandatory trembles

Some finite agents have prescribed mixed laws. Each remaining agent reserves
the same positive weight for a reference law and chooses its residual law.
A finite Nash equilibrium of the induced game supplies simultaneous optimal
residual responses. Thus continuation agents can be completed jointly, rather
than assuming that independently selected best responses are compatible.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : GameForm ι}

/-- Fixed agents retain their law; free agents add an independent tremble. -/
def pinnedTremble (free : Finset ι) (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    Profile F.sig.mixed := fun who =>
  if who ∈ free then mix epsilon nonnegative small (reference who) (residual who)
  else pinned who

private def responseKernel (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (who : ι) (action : F.sig.Strategy who) : PMF (F.sig.Strategy who) :=
  if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure action)
  else pinned who

private def responseGame (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) : GameForm ι where
  sig := F.sig
  play profile := F.mixed.play
    (fun who => responseKernel free pinned reference epsilon nonnegative small who (profile who))

omit [Fintype ι] in
private theorem response_kernel_law (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) (who : ι) :
    (residual who).bind (responseKernel free pinned reference epsilon nonnegative small who) =
      pinnedTremble free pinned reference residual epsilon nonnegative small who := by
  change (residual who).bind (fun action =>
    if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure action)
    else pinned who) = _
  by_cases active : who ∈ free
  · simp only [pinnedTremble, active, ↓reduceIte]
    apply pmf_ext_toReal
    intro action
    simp only [toReal_bind_apply, mix_apply_toReal, FinDist.expect_add,
      expect_constant, FinDist.expect_smul]
    rw [← toReal_bind_apply, PMF.bind_pure]
  · simp only [pinnedTremble, active, ↓reduceIte, PMF.bind_const]

private theorem response_game_law (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    (responseGame free pinned reference epsilon nonnegative small).mixed.play residual =
      F.mixed.play (pinnedTremble free pinned reference residual epsilon nonnegative small) := by
  change ((independentProduct residual).bind fun profile =>
    (independentProduct fun who =>
      responseKernel free pinned reference epsilon nonnegative small who (profile who)).bind
        F.play) = _
  rw [← PMF.bind_bind, FinDist.pi_bind]
  simp only [response_kernel_law]

omit [Fintype ι] in
private theorem pinned_tremble_update (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (who : ι) (active : who ∈ free) (alternative : PMF (F.sig.Strategy who)) :
    pinnedTremble free pinned reference (Profile.update residual who alternative)
        epsilon nonnegative small =
      Profile.update (pinnedTremble free pinned reference residual epsilon nonnegative small)
        who (mix epsilon nonnegative small (reference who) alternative) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [pinnedTremble, active, ↓reduceIte, Profile.update_same]
  · simp only [pinnedTremble, Profile.update_of_ne _ _ same]

private theorem expected_mixed_update_mix (utility : F.sig.Outcome → ι → ℝ)
    (profile : Profile F.sig.mixed) (who : ι)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (first second : PMF (F.sig.Strategy who)) :
    expectedUtility utility who (F.mixed.play
      (Profile.update profile who (mix epsilon nonnegative small first second))) =
      epsilon * expectedUtility utility who (F.mixed.play (Profile.update profile who first)) +
        (1 - epsilon) *
          expectedUtility utility who (F.mixed.play (Profile.update profile who second)) := by
  rw [F.mixed_play_update profile who (mix epsilon nonnegative small first second),
    F.mixed_play_update profile who first, F.mixed_play_update profile who second]
  simp only [expectedUtility_bind, FinDist.expect_mix]

/-- Finite Nash existence jointly selects the residual responses of all free
agents. Their optimality compares every mixed deviation against the same
perturbed opponents. The played profile includes the compulsory trembles, so
the theorem does not call that fully mixed profile an unconstrained equilibrium. -/
theorem exists_pinned_tremble_bestResponses [∀ who, Finite (F.sig.Strategy who)]
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) (free : Finset ι)
    (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon < 1) :
    ∃ residual : Profile F.sig.mixed, ∀ who ∈ free,
      ∀ alternative : PMF (F.sig.Strategy who),
        expectedUtility utility who (F.mixed.play
          (Profile.update
            (pinnedTremble free pinned reference residual epsilon nonnegative small.le)
            who alternative)) ≤
        expectedUtility utility who (F.mixed.play
          (Profile.update
            (pinnedTremble free pinned reference residual epsilon nonnegative small.le)
            who (residual who))) := by
  let _ (who : ι) : Fintype (F.sig.Strategy who) := Fintype.ofFinite _
  let _ (who : ι) : Fintype
      ((responseGame free pinned reference epsilon nonnegative small.le).sig.Strategy who) :=
    inferInstanceAs (Fintype (F.sig.Strategy who))
  let _ (who : ι) : Nonempty
      ((responseGame free pinned reference epsilon nonnegative small.le).sig.Strategy who) :=
    inferInstanceAs (Nonempty (F.sig.Strategy who))
  obtain ⟨residual, optimal⟩ := exists_isNash_mixed
    (F := responseGame free pinned reference epsilon nonnegative small.le) utility
  refine ⟨residual, fun who active alternative => ?_⟩
  have comparison := (isNash_iff
    (F := (responseGame free pinned reference epsilon nonnegative small.le).mixed)
    (weaklyPrefers := euPreference utility) residual).mp optimal who alternative
  change expectedUtility utility who
    ((responseGame free pinned reference epsilon nonnegative small.le).mixed.play
      (Profile.update residual who alternative)) ≤
    expectedUtility utility who
      ((responseGame free pinned reference epsilon nonnegative small.le).mixed.play residual)
    at comparison
  rw [response_game_law, response_game_law,
    pinned_tremble_update free pinned reference residual epsilon nonnegative small.le
      who active alternative] at comparison
  have self : pinnedTremble free pinned reference residual epsilon nonnegative small.le =
      Profile.update (pinnedTremble free pinned reference residual epsilon nonnegative small.le)
        who (mix epsilon nonnegative small.le (reference who) (residual who)) := by
    conv_lhs => rw [← Profile.update_eq_self residual who]
    exact pinned_tremble_update free pinned reference residual epsilon nonnegative small.le
      who active (residual who)
  nth_rw 2 [self] at comparison
  rw [expected_mixed_update_mix, expected_mixed_update_mix] at comparison
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr small)).mp (by linarith)

omit [Fintype ι] in
theorem pinnedTremble_fullSupport (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon ≤ 1)
    (pinnedFull : ∀ who, who ∉ free → FullSupport (pinned who))
    (referenceFull : ∀ who, who ∈ free → FullSupport (reference who)) :
    ∀ who,
      FullSupport (pinnedTremble free pinned reference residual epsilon positive.le small who) :=
    by
  intro who action
  by_cases active : who ∈ free
  · simp only [pinnedTremble, active, ↓reduceIte]
    exact mem_support_mix_left _ _ _ positive (referenceFull who active action)
  · simpa only [pinnedTremble, active, ↓reduceIte] using pinnedFull who active action

end GameTheory
