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
    (retained : FinDist Action) : Option Action → FinDist Action
  | none => retained
  | some action => FinDist.mix weight nonnegative atMostOne (FinDist.pure action) retained

def responseLaw (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : FinDist Action) (response : FinDist (Option Action)) : FinDist Action :=
  response.bind (includeLaw weight nonnegative atMostOne retained)

/-- Sampling a source action and submitting it has the expected mixture law. -/
theorem submitted_law (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained prescribed : FinDist Action) :
    responseLaw weight nonnegative atMostOne retained (prescribed.map some) =
      FinDist.mix weight nonnegative atMostOne prescribed retained := by
  apply FinDist.ext_of_prob
  intro action
  simp only [responseLaw, FinDist.prob_bind, FinDist.expect_map, includeLaw,
    FinDist.prob_mix, FinDist.expect_add, FinDist.expect_smul,
    FinDist.expect_const, FinDist.expect_prob_pure]

/-- A continuation-optimal source lottery remains optimal after unresolved
inclusion. The deviation may randomize over silence and arbitrary proposals.
No ranking of the retained proposals is required from the source strategy. -/
theorem optimal_response (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained prescribed : FinDist Action) (continuation : Action → FinDist Outcome)
    (utility : Outcome → ℝ)
    (optimal : ∀ action, (continuation action).expect utility ≤
      (prescribed.bind continuation).expect utility)
    (alternative : FinDist (Option Action)) :
    ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation).expect
      utility ≤
    ((responseLaw weight nonnegative atMostOne retained (prescribed.map some)).bind
      continuation).expect utility := by
  let value := fun action => (continuation action).expect utility
  have best (action : Action) : value action ≤ prescribed.expect value := by
    simpa only [FinDist.expect_bind] using optimal action
  have oldBound : retained.expect value ≤ prescribed.expect value :=
    FinDist.expect_le_of_forall _ _ _ (fun action _ => best action)
  rw [submitted_law]
  simp only [FinDist.expect_bind, FinDist.expect_mix, responseLaw]
  change alternative.expect (fun response =>
      (includeLaw weight nonnegative atMostOne retained response).expect value) ≤
    weight * prescribed.expect value + (1 - weight) * retained.expect value
  apply FinDist.expect_le_of_forall
  intro response _
  cases response with
  | none =>
      change retained.expect value ≤ _
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr oldBound)]
  | some action =>
      simp only [includeLaw, FinDist.expect_mix, FinDist.expect_pure]
      exact add_le_add (mul_le_mul_of_nonneg_left (best action) nonnegative) le_rfl

/-- Reusing any supported choice of an optimal lottery is also optimal. The
recovery policy need not resample the lottery or rank its supported actions. -/
theorem optimal_response_of_support (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (retained prescribed recovered : FinDist Action)
    (continuation : Action → FinDist Outcome) (utility : Outcome → ℝ)
    (optimal : ∀ action, (continuation action).expect utility ≤
      (prescribed.bind continuation).expect utility)
    (supported : recovered.support ⊆ prescribed.support)
    (alternative : FinDist (Option Action)) :
    ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation).expect
      utility ≤
    ((responseLaw weight nonnegative atMostOne retained (recovered.map some)).bind
      continuation).expect utility := by
  let value := fun action => (continuation action).expect utility
  have best (action : Action) : value action ≤ prescribed.expect value := by
    simpa only [FinDist.expect_bind] using optimal action
  have equal (action : Action) (member : action ∈ prescribed.support) :
      value action = prescribed.expect value :=
    prescribed.eq_of_expect_eq_of_le value _ (fun action _ => best action) rfl member
  have sameValue : recovered.expect value = prescribed.expect value := by
    calc
      recovered.expect value = recovered.expect (fun _ => prescribed.expect value) :=
        FinDist.expect_congr fun action member => equal action (supported member)
      _ = _ := FinDist.expect_const ..
  apply optimal_response weight nonnegative atMostOne retained recovered continuation utility
    ?_ alternative
  intro action
  simpa only [FinDist.expect_bind, ← sameValue] using best action

/-- The source and native continuation games share the same downstream law. -/
def sourceGame (continuation : Action → FinDist Outcome) : GameForm Unit where
  sig := { Strategy := fun _ => FinDist Action, Outcome := Outcome }
  play profile := (profile ()).bind continuation

def responseGame (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : FinDist Action) (continuation : Action → FinDist Outcome) : GameForm Unit where
  sig := { Strategy := fun _ => FinDist (Option Action), Outcome := Outcome }
  play profile := (responseLaw weight nonnegative atMostOne retained (profile ())).bind continuation

theorem nash_preserved (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : FinDist Action) (continuation : Action → FinDist Outcome)
    (utility : Outcome → Unit → ℝ) (prescribed : FinDist Action)
    (optimal : IsNash (sourceGame continuation) (euPreference utility) (fun _ => prescribed)) :
    IsNash (responseGame weight nonnegative atMostOne retained continuation)
      (euPreference utility) (fun _ => prescribed.map some) := by
  rw [isNash_iff] at optimal ⊢
  intro who alternative
  cases who
  apply optimal_response weight nonnegative atMostOne retained prescribed continuation
    (utility · ()) ?_ alternative
  intro action
  have bound := optimal () (FinDist.pure action)
  simpa only [euPreference, expectedUtility, sourceGame, Profile.update_same,
    FinDist.pure_bind] using bound

end GameTheory.PendingChoice
