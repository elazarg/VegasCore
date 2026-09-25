/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MatrixGame

/-! # Communication can make a nonstrategic payoff strategic

Alice and Bob initially choose Boolean actions independently. Alice is paid
one exactly when Bob chooses `true`; Bob is paid zero. Neither player's own
action affects that player's utility, so the source payoff is entirely
nonstrategic.

Now Alice's Boolean is a message observed by Bob before his choice. Bob's pure
strategy becomes a response function. The terminal outcome and payoff rule
are unchanged, and constant responses embed every source profile exactly.
Against Bob's identity response, Alice nevertheless gains by changing only
her message. Decomposing payoffs into incentive components therefore depends
on the strategy space and its unilateral deviations, not just terminal payoffs.

This is a component counterexample, not an equilibrium impossibility: every
embedded source profile remains Nash because a constant response ignores
Alice's message and Bob remains indifferent.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ComponentCommunication

open GameTheory GameTheory.Math.Probability

abbrev source := MatrixGame.form Bool Bool

/-- The normal form of one message followed by a contingent reply. -/
def communicated : GameForm (Fin 2) where
  sig :=
    { Strategy := MatrixGame.Action Bool (Bool → Bool)
      Outcome := Bool × Bool }
  play profile := FinDist.pure (profile 0, profile 1 (profile 0))

def payout (outcome : Bool × Bool) (who : Fin 2) : ℝ :=
  if who = 0 ∧ outcome.2 = true then 1 else 0

/-- The defining incentive property of a nonstrategic payoff game. -/
def OwnUtilityIndependent (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) : Prop :=
  ∀ (profile : Profile form.sig) (who : Fin 2)
    (replacement : form.sig.Strategy who),
    expectedUtility utility who (form.play (profile.update who replacement)) =
      expectedUtility utility who (form.play profile)

theorem source_nonstrategic : OwnUtilityIndependent source payout := by
  intro profile who replacement
  fin_cases who <;>
    simp [expectedUtility, source, MatrixGame.form, payout]

/-- Alice keeps her action; Bob ignores the message. -/
def embed (profile : Profile source.sig) : Profile communicated.sig :=
  Fin.cons (profile 0)
    (Fin.cons (fun _ => profile 1) fun impossible : Fin 0 => impossible.elim0)

theorem embed_outcome (profile : Profile source.sig) :
    communicated.play (embed profile) = source.play profile := rfl

theorem source_nash (profile : Profile source.sig) :
    IsNash source (euPreference payout) profile := by
  rw [isNash_iff]
  intro who replacement
  exact le_of_eq (source_nonstrategic profile who replacement)

theorem embed_nash (profile : Profile source.sig) :
    IsNash communicated (euPreference payout) (embed profile) := by
  rw [isNash_iff]
  intro who replacement
  fin_cases who <;>
    simp [euPreference, expectedUtility, communicated, embed, payout]

def responsive (message : Bool) : Profile communicated.sig :=
  Fin.cons message
    (Fin.cons (fun observed => observed) fun impossible : Fin 0 => impossible.elim0)

theorem change_message :
    (responsive false).update 0 true = responsive true := by
  funext who
  fin_cases who <;> rfl

theorem message_strictly_profitable :
    expectedUtility payout 0 (communicated.play (responsive false)) <
      expectedUtility payout 0
        (communicated.play ((responsive false).update 0 true)) := by
  rw [change_message]
  change expectedUtility payout 0 (FinDist.pure (false, false)) <
    expectedUtility payout 0 (FinDist.pure (true, true))
  norm_num [payout]

theorem communicated_not_nonstrategic :
    ¬ OwnUtilityIndependent communicated payout := by
  intro independent
  have equality := independent (responsive false) 0 true
  exact (ne_of_gt message_strictly_profitable) equality

end GameTheoryExtensionsTests.ComponentCommunication
