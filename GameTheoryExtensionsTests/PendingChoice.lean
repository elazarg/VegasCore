/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.PendingChoice
import GameTheory.Tests.ContinuationMenus

/-! # Inclusion can preserve or destroy a common optimal response

These are continuation games, not canonical native subgame witnesses. The
positive case allows arbitrary retained proposals and inclusion weights. The
negative case isolates weighting repeated copies of an envelope: a stateless
weighted selector can then reward replay more than a fresh optimal proposal.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PendingChoice

open GameTheory GameTheory.Math.Probability
open GameTheory.Tests.ContinuationMenus

deriving instance Fintype for Outcome

theorem same_submission_optimal (retained : PMF Outcome)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    IsNash (PendingChoice.responseGame weight nonnegative atMostOne retained PMF.pure)
        (euPreference utilityB) (fun _ => PMF.pure (some .a)) ∧
      IsNash (PendingChoice.responseGame weight nonnegative atMostOne retained PMF.pure)
        (euPreference utilityC) (fun _ => PMF.pure (some .a)) := by
  have sourceOptimal (utility : Outcome → Unit → ℝ)
      (best : ∀ outcome, utility outcome () ≤ utility .a ()) :
      IsNash (PendingChoice.sourceGame PMF.pure) (euPreference utility)
        (fun _ => PMF.pure Outcome.a) := by
    rw [isNash_iff]
    intro who alternative
    cases who
    rw [euPreference_apply]
    refine ⟨payoffIntegrable_of_finite (α := Outcome) _ _,
      payoffIntegrable_of_finite (α := Outcome) _ _, ?_⟩
    change expect (alternative.bind PMF.pure) (utility · ()) ≤
      expect ((PMF.pure Outcome.a).bind PMF.pure) (utility · ())
    rw [PMF.bind_pure, PMF.pure_bind, expect_pure]
    exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ (fun outcome _ => best outcome)
  constructor
  · simpa only [PMF.pure_map] using
      PendingChoice.nash_preserved weight nonnegative atMostOne retained PMF.pure
        utilityB (PMF.pure Outcome.a)
        (sourceOptimal utilityB (by intro outcome; cases outcome <;> norm_num [utilityB]))
        (fun _ => payoffIntegrable_of_finite _ _)
  · simpa only [PMF.pure_map] using
      PendingChoice.nash_preserved weight nonnegative atMostOne retained PMF.pure
        utilityC (PMF.pure Outcome.a)
        (sourceOptimal utilityC (by intro outcome; cases outcome <;> norm_num [utilityC]))
        (fun _ => payoffIntegrable_of_finite _ _)

inductive Response where
  | fresh (outcome : Outcome)
  | replay (first : Bool)
  | silent
  deriving Fintype

def retained : PMF Outcome :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure .b) (PMF.pure .c)

/-- Two old envelopes have weight five each; the next fresh envelope has
weight one. Replaying an old envelope adds another copy of weight five.
Selection uses only the resulting multiset, with no observation records. -/
def weightedCopies : Response → PMF Outcome
  | .fresh outcome =>
      mix (1 / 11) (by norm_num) (by norm_num) (PMF.pure outcome) retained
  | .replay first => mix (2 / 3) (by norm_num) (by norm_num)
      (PMF.pure (if first then .b else .c)) (PMF.pure (if first then .c else .b))
  | .silent => retained

def replayGame : GameForm Unit where
  sig := { Strategy := fun _ => PMF Response, Outcome := Outcome }
  play profile := (profile ()).bind weightedCopies

theorem weightedCopies_sum (response : Response) :
    expect (weightedCopies response) (utilityB · ()) +
      expect (weightedCopies response) (utilityC · ()) ≤ 36 / 11 := by
  cases response with
  | fresh outcome =>
      cases outcome <;> norm_num [weightedCopies, retained, expect_mix_of_finite,
        expect_pure, utilityB, utilityC]
  | replay first =>
      cases first <;> norm_num [weightedCopies, expect_mix_of_finite,
        expect_pure, utilityB, utilityC]
  | silent =>
      norm_num [weightedCopies, retained, expect_mix_of_finite,
        expect_pure, utilityB, utilityC]

/-- Statelessness alone does not ensure a utility-independent optimal
response. Counting duplicate envelopes can change old candidates' odds. -/
theorem no_common_weighted_replay_response :
    ¬ ∃ profile : Profile replayGame.sig,
      IsNash replayGame (euPreference utilityB) profile ∧
        IsNash replayGame (euPreference utilityC) profile := by
  rintro ⟨profile, bestB, bestC⟩
  rw [isNash_iff] at bestB bestC
  have first := (bestB () (PMF.pure (.replay true))).2.2
  have second := (bestC () (PMF.pure (.replay false))).2.2
  change (expect ((PMF.pure (Response.replay true)).bind weightedCopies) (utilityB · ())) ≤
    expect ((profile ()).bind weightedCopies) (utilityB · ()) at first
  change (expect ((PMF.pure (Response.replay false)).bind weightedCopies) (utilityC · ())) ≤
    expect ((profile ()).bind weightedCopies) (utilityC · ()) at second
  have total :
      expect ((profile ()).bind weightedCopies) (utilityB · ()) +
        expect ((profile ()).bind weightedCopies) (utilityC · ()) ≤ 36 / 11 := by
    rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
      expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
      ← expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      (fun response _ => weightedCopies_sum response)
  norm_num [PMF.pure_bind, weightedCopies, expect_mix_of_finite,
    expect_pure, utilityB, utilityC] at first second
  change (5 / 3 : ℝ) ≤ expect ((profile ()).bind weightedCopies) (utilityB · ()) at first
  change (5 / 3 : ℝ) ≤ expect ((profile ()).bind weightedCopies) (utilityC · ()) at second
  linarith

end GameTheoryExtensionsTests.PendingChoice
