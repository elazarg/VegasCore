/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Equilibrium
import GameTheory.Core.Utility
import Interaction.BoundPublication

/-! # Matching pennies with informed disclosure failure

Failure is a terminal outcome outside the ordinary Boolean play values. The
second player fixes its bit before observing the first opening, but its
disclosure plan may depend on that opening. This is a small terminal-settlement
game, not a generic semantics of player withdrawal.
-/

noncomputable section

namespace VegasTests.FailureGame

open GameTheory GameTheory.Math.Probability

inductive Player where
  | first
  | second
  deriving DecidableEq, Fintype

/-- The committed bit is fixed independently of the later disclosure plan. -/
structure SecondPolicy where
  bit : Bool
  disclose : Option Bool → Bool
  deriving Fintype

inductive Outcome where
  | played (first second : Bool)
  | failed (who : Player)
  deriving DecidableEq

def PurePolicy : Player → Type
  | .first => Option Bool
  | .second => SecondPolicy

/-- Strategies are arbitrary finite randomized policies. In particular, the
second marginal may randomize jointly over its fixed bit and complete informed
disclosure plan. -/
def signature : GameSignature Player where
  Strategy who := FinDist (PurePolicy who)
  Outcome := Outcome

def terminal : Option Bool → SecondPolicy → Outcome
  | none, _ => .failed .first
  | some first, second =>
      if second.disclose (some first) then .played first second.bit
      else .failed .second

/-- Execute both immutable bindings before either publication. The second
disclosure plan observes the actual first publication, never an unbound value.
This example stops at the first failed publication. -/
def execute (first : Option Bool) (second : SecondPolicy) : Outcome :=
  let protocol : Interaction.GuardedPublication (fun _ : Player => Bool) := ⟨[]⟩
  let initial := Interaction.BoundPublicationState.empty (Value := fun _ : Player => Bool)
  let firstBinding := match first with
    | none => Interaction.Binding.unopenable
    | some bit => Interaction.Binding.value bit
  let committed := (initial.bind .first firstBinding).bind .second (.value second.bit)
  let firstOpening := committed.reveal protocol .first true
  match firstOpening.publications .first with
  | .value firstBit =>
      let finalState := firstOpening.reveal protocol .second (second.disclose (some firstBit))
      match finalState.publications .second with
      | .value secondBit => .played firstBit secondBit
      | .pending | .failed => .failed .second
  | .pending | .failed => .failed .first

/-- The game outcome is exactly the result of the new binding/publication
operations, for every pure fixed-bit and contingent-disclosure policy. -/
theorem execute_eq_terminal : ∀ first second, execute first second = terminal first second := by
  decide

abbrev form : GameForm Player where
  sig := signature
  play profile := (profile .first).bind fun first =>
    (profile .second).map (terminal first)

/-- Ordinary play is matching pennies: the first player wants equality. The
failing player receives `-2`, strictly below either ordinary payoff `-1` or
`1`; the other player receives `2`. -/
def utility : Outcome → Player → ℝ
  | .played first second, .first => if first = second then 1 else -1
  | .played first second, .second => if first = second then -1 else 1
  | .failed failed, who => if failed = who then -2 else 2

def fairBool : FinDist Bool :=
  FinDist.mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def honestFirst : FinDist (Option Bool) := fairBool.map some

def alwaysDisclose (bit : Bool) : SecondPolicy :=
  ⟨bit, fun _ => true⟩

def honestSecond : FinDist SecondPolicy := fairBool.map alwaysDisclose

def honest : Profile signature
  | .first => honestFirst
  | .second => honestSecond

/-- Once the second player's bit is fixed, opening strictly beats informed
failure even on the losing branch. -/
theorem second_opening_strictly_beats_failure (first fixed : Bool) :
    utility (.failed .second) .second <
      utility (.played first fixed) .second := by
  by_cases h : first = fixed
  · simp [utility, h]
  · simp [utility, h]
    norm_num

private theorem fairBool_expect (f : Bool → ℝ) :
    fairBool.expect f = (f false + f true) / 2 := by
  rw [fairBool, FinDist.expect_mix]
  simp
  ring

theorem honest_expectedUtility_zero (who : Player) :
    expectedUtility utility who (form.play honest) = 0 := by
  cases who <;>
    simp only [honest, honestFirst, honestSecond, expectedUtility_bind,
      FinDist.expect_map]
  all_goals
    rw [fairBool_expect]
    simp only [expectedUtility, alwaysDisclose, terminal, utility,
      FinDist.expect_map]
    rw [fairBool_expect, fairBool_expect]
    norm_num

private theorem first_deviation_le (replacement : FinDist (Option Bool)) :
    expectedUtility utility .first
      (form.play (Profile.update honest .first replacement)) ≤ 0 := by
  simp only [form, Profile.update_same, expectedUtility_bind]
  rw [show Profile.update honest .first replacement .second = honestSecond by rfl]
  apply FinDist.expect_le_of_forall
  intro action _haction
  simp only [honestSecond, expectedUtility, FinDist.expect_map]
  rw [fairBool_expect]
  cases action with
  | none => norm_num [terminal, utility]
  | some action => cases action <;> norm_num [alwaysDisclose, terminal, utility]

private theorem second_pure_le (policy : SecondPolicy) :
    expectedUtility utility .second
      ((honestFirst.bind fun first => FinDist.pure (terminal first policy))) ≤ 0 := by
  simp only [expectedUtility_bind, expectedUtility_pure]
  rw [show honestFirst = fairBool.map some from rfl,
    FinDist.expect_map, fairBool_expect]
  rcases policy with ⟨bit, disclose⟩
  cases bit
  all_goals
    by_cases hfalse : disclose (some false) <;>
      by_cases htrue : disclose (some true) <;>
      norm_num [terminal, utility, hfalse, htrue]

private theorem second_deviation_le (replacement : FinDist SecondPolicy) :
    expectedUtility utility .second
      (form.play (Profile.update honest .second replacement)) ≤ 0 := by
  change ((honestFirst.bind fun first => replacement.map (terminal first)).expect
    fun outcome => utility outcome .second) ≤ 0
  rw [FinDist.expect_bind]
  simp_rw [FinDist.expect_map]
  rw [FinDist.expect_comm]
  apply FinDist.expect_le_of_forall
  intro policy _hpolicy
  have hpolicy := second_pure_le policy
  rw [expectedUtility_bind] at hpolicy
  simpa only [expectedUtility_pure] using hpolicy

/-- Fair committed bits with unconditional honest disclosure are Nash against
all randomized first-player failures and all randomized informed second-player
disclosure policies. -/
theorem honest_isNash : IsNash form (euPreference utility) honest := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply, honest_expectedUtility_zero]
  cases who
  · exact first_deviation_le replacement
  · exact second_deviation_le replacement

end VegasTests.FailureGame
