/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Approximate
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

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
  classical
  apply pmf_ext_toReal
  intro action
  rw [responseLaw, PMF.bind_map, toReal_bind_apply, mix_apply_toReal]
  simp only [Function.comp_apply, includeLaw, mix_apply_toReal, toReal_pure_apply]
  have point : PayoffIntegrable prescribed fun choice =>
      weight * (if action = choice then (1 : ℝ) else 0) :=
    payoffIntegrable_of_bounded _ _ (C := |weight|) fun choice => by
      split_ifs <;> simp
  rw [expect_add point (payoffIntegrable_constant _ _), expect_const_mul, expect_ite_eq,
    expect_constant, mul_one]

/-- A continuation-optimal source lottery remains optimal after unresolved
inclusion. The deviation may randomize over silence and arbitrary proposals.
No ranking of the retained proposals is required from the source strategy.
The compared laws must have finite expected utility. -/
theorem optimal_response (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained prescribed : PMF Action) (continuation : Action → PMF Outcome)
    (utility : Outcome → ℝ)
    (actionIntegrable : ∀ action, PayoffIntegrable (continuation action) utility)
    (prescribedIntegrable : PayoffIntegrable (prescribed.bind continuation) utility)
    (retainedIntegrable : PayoffIntegrable (retained.bind continuation) utility)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (alternative : PMF (Option Action))
    (alternativeIntegrable : PayoffIntegrable
      ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
        utility) :
    expect ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
      utility ≤
    expect ((responseLaw weight nonnegative atMostOne retained (prescribed.map some)).bind
      continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have prescribedValue := expect_bind_tower _ _ _ prescribedIntegrable
  have retainedValue := expect_bind_tower _ _ _ retainedIntegrable
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [prescribedValue] using optimal action
  have oldBound : expect retained value ≤ expect prescribed value :=
    expect_le_const _ _ (payoffIntegrable_bind_conditionalExpectation _ _ _ retainedIntegrable)
      _ fun action _ => best action
  rw [submitted_law, mix_bind, expect_mix _ _ _ _ _ _ prescribedIntegrable retainedIntegrable,
    prescribedValue, retainedValue]
  rw [responseLaw, PMF.bind_bind] at alternativeIntegrable ⊢
  rw [expect_bind_tower _ _ _ alternativeIntegrable]
  apply expect_le_const _ _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ alternativeIntegrable)
  intro response _
  cases response with
  | none =>
      change expect (retained.bind continuation) utility ≤ _
      rw [retainedValue]
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr oldBound)]
  | some action =>
      change expect ((mix weight nonnegative atMostOne (PMF.pure action) retained).bind
        continuation) utility ≤ _
      rw [mix_bind, PMF.pure_bind, expect_mix _ _ _ _ _ _ (actionIntegrable action)
        retainedIntegrable, retainedValue]
      exact add_le_add (mul_le_mul_of_nonneg_left (best action) nonnegative) le_rfl

/-- Reusing any supported choice of an optimal lottery is also optimal. The
recovery policy need not resample the lottery or rank its supported actions. -/
theorem optimal_response_of_support (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (retained prescribed recovered : PMF Action)
    (continuation : Action → PMF Outcome) (utility : Outcome → ℝ)
    (actionIntegrable : ∀ action, PayoffIntegrable (continuation action) utility)
    (prescribedIntegrable : PayoffIntegrable (prescribed.bind continuation) utility)
    (recoveredIntegrable : PayoffIntegrable (recovered.bind continuation) utility)
    (retainedIntegrable : PayoffIntegrable (retained.bind continuation) utility)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (supported : recovered.support ⊆ prescribed.support)
    (alternative : PMF (Option Action))
    (alternativeIntegrable : PayoffIntegrable
      ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
        utility) :
    expect ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
      utility ≤
    expect ((responseLaw weight nonnegative atMostOne retained (recovered.map some)).bind
      continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have prescribedValue := expect_bind_tower _ _ _ prescribedIntegrable
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [prescribedValue] using optimal action
  have equal := expect_eq_const_of_le_on_support prescribed value _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ prescribedIntegrable)
    (fun action _ => best action) rfl
  have sameValue : expect recovered value = expect prescribed value := by
    calc
      expect recovered value = expect recovered (fun _ => expect prescribed value) :=
        expect_congr_on_support fun action member => equal action (supported member)
      _ = _ := expect_constant ..
  apply optimal_response weight nonnegative atMostOne retained recovered continuation utility
    actionIntegrable recoveredIntegrable retainedIntegrable ?_ alternative alternativeIntegrable
  intro action
  rw [expect_bind_tower _ _ _ recoveredIntegrable]
  simpa only [← sameValue] using best action

/-- The source and native continuation games share the same downstream law. -/
def sourceGame (continuation : Action → PMF Outcome) : GameForm Unit where
  sig := { Strategy := fun _ => PMF Action, Outcome := Outcome }
  play profile := (profile ()).bind continuation

def responseGame (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : PMF Action) (continuation : Action → PMF Outcome) : GameForm Unit where
  sig := { Strategy := fun _ => PMF (Option Action), Outcome := Outcome }
  play profile := (responseLaw weight nonnegative atMostOne retained (profile ())).bind continuation

/-- Nash equilibrium of the source choice carries over to the response game
whenever every response deviation has a finite expected utility. Every
finitely supported instance satisfies that premise. -/
theorem nash_preserved (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (retained : PMF Action) (continuation : Action → PMF Outcome)
    (utility : Outcome → Unit → ℝ) (prescribed : PMF Action)
    (optimal : IsNash (sourceGame continuation) (euPreference utility) (fun _ => prescribed))
    (integrable : ∀ alternative : PMF (Option Action), PayoffIntegrable
      ((responseLaw weight nonnegative atMostOne retained alternative).bind continuation)
        (utility · ())) :
    IsNash (responseGame weight nonnegative atMostOne retained continuation)
      (euPreference utility) (fun _ => prescribed.map some) := by
  rw [isNash_iff] at optimal ⊢
  intro who alternative
  cases who
  have pure (action : Action) := optimal () (PMF.pure action)
  simp only [euPreference_apply, sourceGame, Profile.update_same, PMF.pure_bind] at pure
  have base := optimal () prescribed
  simp only [euPreference_apply, sourceGame, Profile.update_same] at base
  have retainedIntegrable := integrable (PMF.pure none)
  rw [responseLaw, PMF.pure_bind] at retainedIntegrable
  refine ⟨integrable _, integrable _, ?_⟩
  exact optimal_response weight nonnegative atMostOne retained prescribed continuation
    (utility · ()) (fun action => (pure action).2.1) base.1
    retainedIntegrable (fun action => (pure action).2.2) alternative (integrable _)

end GameTheory.PendingChoice
