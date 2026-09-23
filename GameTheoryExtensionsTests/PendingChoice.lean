/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.PendingChoice
import GameTheoryExtensionsTests.ContinuationMenus

/-! # Inclusion can preserve or destroy a common optimal response

These are continuation games, not canonical native subgame witnesses. The
positive case allows arbitrary retained proposals and inclusion weights. The
negative case isolates weighting repeated copies of an envelope: a stateless
weighted selector can then reward replay more than a fresh optimal proposal.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PendingChoice

open GameTheory GameTheory.Math.Probability
open ContinuationMenus

theorem same_submission_optimal (retained : FinDist Outcome)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    IsNash (PendingChoice.responseGame weight nonnegative atMostOne retained FinDist.pure)
        (euPreference utilityB) (fun _ => FinDist.pure (some .a)) ∧
      IsNash (PendingChoice.responseGame weight nonnegative atMostOne retained FinDist.pure)
        (euPreference utilityC) (fun _ => FinDist.pure (some .a)) := by
  have sourceOptimal (utility : Outcome → Unit → ℝ)
      (best : ∀ outcome, utility outcome () ≤ utility .a ()) :
      IsNash (PendingChoice.sourceGame FinDist.pure) (euPreference utility)
        (fun _ => FinDist.pure Outcome.a) := by
    rw [isNash_iff]
    intro who alternative
    cases who
    change (alternative.bind FinDist.pure).expect (utility · ()) ≤
      ((FinDist.pure Outcome.a).bind FinDist.pure).expect (utility · ())
    rw [FinDist.bind_pure, FinDist.pure_bind, FinDist.expect_pure]
    exact FinDist.expect_le_of_forall _ _ _ (fun outcome _ => best outcome)
  constructor
  · simpa only [FinDist.map_pure] using
      PendingChoice.nash_preserved weight nonnegative atMostOne retained FinDist.pure
        utilityB (FinDist.pure Outcome.a)
        (sourceOptimal utilityB (by intro outcome; cases outcome <;> norm_num [utilityB]))
  · simpa only [FinDist.map_pure] using
      PendingChoice.nash_preserved weight nonnegative atMostOne retained FinDist.pure
        utilityC (FinDist.pure Outcome.a)
        (sourceOptimal utilityC (by intro outcome; cases outcome <;> norm_num [utilityC]))

inductive Response where
  | fresh (outcome : Outcome)
  | replay (first : Bool)
  | silent

def retained : FinDist Outcome :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure .b) (FinDist.pure .c)

/-- Two old envelopes have weight five each; the next fresh envelope has
weight one. Replaying an old envelope adds another copy of weight five.
Selection uses only the resulting multiset, with no observation records. -/
def weightedCopies : Response → FinDist Outcome
  | .fresh outcome =>
      FinDist.mix (1 / 11) (by norm_num) (by norm_num) (FinDist.pure outcome) retained
  | .replay first => FinDist.mix (2 / 3) (by norm_num) (by norm_num)
      (FinDist.pure (if first then .b else .c)) (FinDist.pure (if first then .c else .b))
  | .silent => retained

def replayGame : GameForm Unit where
  sig := { Strategy := fun _ => FinDist Response, Outcome := Outcome }
  play profile := (profile ()).bind weightedCopies

theorem weightedCopies_sum (response : Response) :
    (weightedCopies response).expect (utilityB · ()) +
      (weightedCopies response).expect (utilityC · ()) ≤ 36 / 11 := by
  cases response with
  | fresh outcome =>
      cases outcome <;> norm_num [weightedCopies, retained, FinDist.expect_mix,
        FinDist.expect_pure, utilityB, utilityC]
  | replay first =>
      cases first <;> norm_num [weightedCopies, FinDist.expect_mix,
        FinDist.expect_pure, utilityB, utilityC]
  | silent =>
      norm_num [weightedCopies, retained, FinDist.expect_mix,
        FinDist.expect_pure, utilityB, utilityC]

/-- Statelessness alone does not ensure a utility-independent optimal
response. Counting duplicate envelopes can change old candidates' odds. -/
theorem no_common_weighted_replay_response :
    ¬ ∃ profile : Profile replayGame.sig,
      IsNash replayGame (euPreference utilityB) profile ∧
        IsNash replayGame (euPreference utilityC) profile := by
  rintro ⟨profile, bestB, bestC⟩
  rw [isNash_iff] at bestB bestC
  have first := bestB () (FinDist.pure (.replay true))
  have second := bestC () (FinDist.pure (.replay false))
  change (((FinDist.pure (Response.replay true)).bind weightedCopies).expect (utilityB · ())) ≤
    ((profile ()).bind weightedCopies).expect (utilityB · ()) at first
  change (((FinDist.pure (Response.replay false)).bind weightedCopies).expect (utilityC · ())) ≤
    ((profile ()).bind weightedCopies).expect (utilityC · ()) at second
  have total :
      ((profile ()).bind weightedCopies).expect (utilityB · ()) +
        ((profile ()).bind weightedCopies).expect (utilityC · ()) ≤ 36 / 11 := by
    rw [FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_add]
    exact FinDist.expect_le_of_forall _ _ _ (fun response _ => weightedCopies_sum response)
  norm_num [FinDist.pure_bind, weightedCopies, FinDist.expect_mix,
    FinDist.expect_pure, utilityB, utilityC] at first second
  change (5 / 3 : ℝ) ≤ ((profile ()).bind weightedCopies).expect (utilityB · ()) at first
  change (5 / 3 : ℝ) ≤ ((profile ()).bind weightedCopies).expect (utilityC · ()) at second
  linarith

end GameTheoryExtensionsTests.PendingChoice
