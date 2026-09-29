/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Approximate

/-! # Choosing among retained proposals and one fresh proposal

At a fixed prefix, inclusion uses the fresh proposal with a fixed probability
and otherwise selects from an unchanged law of retained proposals. Silence
leaves the retained law unchanged. Under this contract, an optimal source
choice stays optimal against all randomized optional submissions.

The continuation kernel may include disclosure and subsequent play. Its law
must be fixed across the compared submissions; this module does not prove
that a reactive implementation, or a later information set, satisfies that
premise. In particular, this is a local incentive result, not native SPE.
-/

noncomputable section

namespace GameTheory.PendingChoice

open Math.Probability

universe u v

variable {Action : Type u} {Outcome : Type v}

/-- The weight and retained law are fixed before choosing a response. -/
def includeLaw (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : PMF Action) : Option Action → PMF Action
  | none => retained
  | some action => mix weight nonnegative atMostOne (PMF.pure action) retained

def responseLaw (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : PMF Action) (response : PMF (Option Action)) : PMF Action :=
  response.bind (includeLaw weight nonnegative atMostOne retained)

/-- Sampling a source action and submitting it has the expected mixture law. -/
theorem submitted_law (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained prescribed : PMF Action) :
    responseLaw weight nonnegative atMostOne retained (prescribed.map some) =
      mix weight nonnegative atMostOne prescribed retained := by
  apply pmf_ext_toReal
  intro action
  simp only [responseLaw, toReal_bind_apply, expect_map, includeLaw,
    mix_apply_toReal, FinDist.expect_add, FinDist.expect_smul,
    expect_constant, FinDist.expect_prob_pure]

/-- A continuation-optimal source lottery remains optimal after unresolved
inclusion. The deviation may randomize over silence and arbitrary proposals.
No ranking of the retained proposals is required from the source strategy. -/
theorem optimal_response (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained prescribed : PMF Action) (continuation : Action → PMF Outcome)
    (utility : Outcome → ℝ)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (alternative : PMF (Option Action)) :
    expect ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
      utility ≤
    expect ((responseLaw weight nonnegative atMostOne retained (prescribed.map some)).bind
      continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [FinDist.expect_bind] using optimal action
  have oldBound : expect retained value ≤ expect prescribed value :=
    FinDist.expect_le_of_forall _ _ _ (fun action _ => best action)
  rw [submitted_law]
  simp only [FinDist.expect_bind, FinDist.expect_mix, responseLaw]
  change expect alternative (fun response =>
      expect (includeLaw weight nonnegative atMostOne retained response) value) ≤
    weight * expect prescribed value + (1 - weight) * expect retained value
  apply FinDist.expect_le_of_forall
  intro response _
  cases response with
  | none =>
      change expect retained value ≤ _
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr oldBound)]
  | some action =>
      simp only [includeLaw, FinDist.expect_mix, expect_pure]
      exact add_le_add (mul_le_mul_of_nonneg_left (best action) nonnegative) le_rfl

/-- Reusing any supported choice of an optimal lottery is also optimal. The
recovery policy need not resample the lottery or rank its supported actions. -/
theorem optimal_response_of_support (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (retained prescribed recovered : PMF Action)
    (continuation : Action → PMF Outcome) (utility : Outcome → ℝ)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (supported : recovered.support ⊆ prescribed.support)
    (alternative : PMF (Option Action)) :
    expect ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
      utility ≤
    expect ((responseLaw weight nonnegative atMostOne retained (recovered.map some)).bind
      continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [FinDist.expect_bind] using optimal action
  have equal (action : Action) (member : action ∈ prescribed.support) :
      value action = expect prescribed value :=
    prescribed.eq_of_expect_eq_of_le value _ (fun action _ => best action) rfl member
  have sameValue : expect recovered value = expect prescribed value := by
    calc
      expect recovered value = expect recovered (fun _ => expect prescribed value) :=
        expect_congr_on_support fun action member => equal action (supported member)
      _ = _ := expect_constant ..
  apply optimal_response weight nonnegative atMostOne retained recovered continuation utility
    ?_ alternative
  intro action
  simpa only [FinDist.expect_bind, ← sameValue] using best action

/-- The source and native continuation games share the same downstream law. -/
def sourceGame (continuation : Action → PMF Outcome) : GameForm Unit where
  sig := { Strategy := fun _ => PMF Action, Outcome := Outcome }
  play profile := (profile ()).bind continuation

def responseGame (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : PMF Action) (continuation : Action → PMF Outcome) : GameForm Unit where
  sig := { Strategy := fun _ => PMF (Option Action), Outcome := Outcome }
  play profile := (responseLaw weight nonnegative atMostOne retained (profile ())).bind continuation

theorem nash_preserved (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : PMF Action) (continuation : Action → PMF Outcome)
    (utility : Outcome → Unit → ℝ) (prescribed : PMF Action)
    (optimal : IsNash (sourceGame continuation) (euPreference utility) (fun _ => prescribed)) :
    IsNash (responseGame weight nonnegative atMostOne retained continuation)
      (euPreference utility) (fun _ => prescribed.map some) := by
  rw [isNash_iff] at optimal ⊢
  intro who alternative
  cases who
  apply optimal_response weight nonnegative atMostOne retained prescribed continuation
    (utility · ()) ?_ alternative
  intro action
  have bound := optimal () (PMF.pure action)
  simpa only [euPreference, expectedUtility, sourceGame, Profile.update_same,
    PMF.pure_bind] using bound

end GameTheory.PendingChoice
