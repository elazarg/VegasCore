/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Source.ValueBinding
import GameTheory.Core.Response

/-! # Conditional withholding refutes dominant truthful bidding

Two bidders commit before either bid is revealed. Alice reveals first. The
second-price settlement ignores withheld bids and charges each withholding
bidder a forfeiture to an external seller. Bob can condition his disclosure on
Alice's public report. This source-level counterexample uses value-only
commitments and utilities of public results, for every forfeiture amount.
-/

noncomputable section

namespace Vegas.Examples.CommitRevealAuction

open SourceProgram GameTheory GameTheory.Math.Probability

inductive Player where
  | alice
  | bob
  deriving DecidableEq

private def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .int where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

/-- Both bids are bound before Alice and then Bob choose whether to disclose. -/
def program : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 .alice (by decide) (acceptGuard .alice 0) <|
  .commit 1 .bob (by decide) (acceptGuard .bob 1) <|
  .reveal 2 .alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 .bob 1 (by decide) (.there .here) (by decide) <|
  .ret []

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := FinDist.pure (Env.empty (CellVal simpleExpr))
  obligations := ∅
  program := program
  accounts := rfl

/-- Alice binds the supplied report and always discloses it. -/
def alicePolicy (report : Int) : BehavioralPolicy Player.alice program :=
  (fun _ _ => FinDist.pure (.success report),
    ((fun h => nomatch h),
      (fun _ _ => FinDist.pure true, ((fun h => nomatch h), PUnit.unit))))

/-- Bob binds 4 and discloses precisely when Alice's public report is 5. -/
def bobPolicy : BehavioralPolicy Player.bob program :=
  ((fun h => nomatch h),
    (fun _ _ => FinDist.pure (.success 4),
      ((fun h => nomatch h),
        (fun _ view => FinDist.pure (match view.1.cells.get .here with
          | .failure => false
          | .success bid => decide (bid = (5 : Int))),
          PUnit.unit))))

def aliceStrategy (report : Int) : ValueBindingPolicy Player.alice program :=
  ⟨alicePolicy report, by simp [ValueBinding, program, alicePolicy]⟩

def bobStrategy : ValueBindingPolicy Player.bob program :=
  ⟨bobPolicy, by simp [ValueBinding, program, bobPolicy]⟩

def profile (report : Int) : Profile setup.valueBindingGame.sig := fun
  | .alice => aliceStrategy report
  | .bob => bobStrategy

def result (alice bob : PublicationResult Int) : PublicOutcome program :=
  Env.cons bob (Env.cons alice (Env.empty simpleExpr.Val))

/-- Net utility for a second-price sale, breaking ties toward Alice. A bidder
who withholds pays the forfeiture to the seller, with no transfer to the other
bidder. Values are exogenous analysis parameters, not chosen reports. -/
def utility (values : Player → ℝ) (forfeiture : ℝ)
    (outcome : PublicOutcome program) : Player → ℝ
  | .alice => match (outcome.get (.there .here) : PublicationResult Int) with
    | .failure => -forfeiture
    | .success a => match (outcome.get .here : PublicationResult Int) with
      | .failure => values .alice
      | .success b => if b ≤ a then values .alice - b else 0
  | .bob => match (outcome.get .here : PublicationResult Int) with
    | .failure => -forfeiture
    | .success b => match (outcome.get (.there .here) : PublicationResult Int) with
      | .failure => values .bob
      | .success a => if a < b then values .bob - a else 0

theorem play_truthful :
    setup.valueBindingGame.play (profile 5) = FinDist.pure (result (.success 5) (.success 4)) := by
  simp only [Setup.valueBindingGame, Setup.publicRun, Setup.run, setup, valueBindingProfile,
    profile, aliceStrategy, bobStrategy, alicePolicy, bobPolicy, SourceProgram.run,
    program, runWith, commitKernel, revealKernel, afterCommit, afterReveal,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

theorem play_misreport :
    setup.valueBindingGame.play (profile 6) = FinDist.pure (result (.success 6) .failure) := by
  simp only [Setup.valueBindingGame, Setup.publicRun, Setup.run, setup, valueBindingProfile,
    profile, aliceStrategy, bobStrategy, alicePolicy, bobPolicy, SourceProgram.run,
    program, runWith, commitKernel, revealKernel, afterCommit, afterReveal,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

theorem update_profile (before after : Int) :
    Profile.update (profile before) .alice (aliceStrategy after) = profile after := by
  funext who
  cases who <;> simp [profile, Profile.update]

/-- The witness keeps the same opponent policy and improves utility from 1 to 5. -/
theorem profitable_misreport (values : Player → ℝ) (forfeiture : ℝ)
    (valuation : values .alice = 5) :
    expectedUtility (utility values forfeiture) Player.alice
        (setup.valueBindingGame.play (profile 5)) <
      expectedUtility (utility values forfeiture) Player.alice
        (setup.valueBindingGame.play (profile 6)) := by
  rw [play_truthful, play_misreport, expectedUtility_pure, expectedUtility_pure]
  norm_num [utility, result, Env.get, Env.cons, valuation]

/-- Truthful binding and disclosure is not dominant, for any withholding penalty. -/
theorem truthful_not_dominant (values : Player → ℝ) (forfeiture : ℝ)
    (valuation : values .alice = 5) :
    ¬ IsDominant setup.valueBindingGame (euPreference (utility values forfeiture))
      Player.alice (aliceStrategy 5) := by
  intro dominant
  have bound := dominant (aliceStrategy 6) (profile 5)
  rw [euPreference_apply, update_profile, update_profile] at bound
  exact (not_le_of_gt (profitable_misreport values forfeiture valuation)) bound

universe uStrategy uOutcome

/-- Every translation preserving Alice's utility at source profiles preserves
this failure of dominance. This quantifies over translations and target games,
but does not forbid changing the source settlement or disclosure order. -/
theorem translated_truthful_not_dominant
    (values : Player → ℝ) (forfeiture : ℝ) (valuation : values .alice = 5)
    (target : GameForm.{0, uStrategy, uOutcome} Player)
    (compile : (who : Player) → setup.valueBindingGame.sig.Strategy who →
      target.sig.Strategy who)
    (targetUtility : target.sig.Outcome → Player → ℝ)
    (preserves : ∀ players : Profile setup.valueBindingGame.sig,
      expectedUtility targetUtility Player.alice (target.play (Profile.map compile players)) =
        expectedUtility (utility values forfeiture) Player.alice
          (setup.valueBindingGame.play players)) :
    ¬ IsDominant target (euPreference targetUtility) Player.alice
      (compile Player.alice (aliceStrategy 5)) := by
  intro dominant
  have bound := dominant (compile Player.alice (aliceStrategy 6))
    (Profile.map compile (profile 5))
  rw [euPreference_apply, ← Profile.map_update, ← Profile.map_update,
    preserves, preserves, update_profile, update_profile] at bound
  exact (not_le_of_gt (profitable_misreport values forfeiture valuation)) bound

end Vegas.Examples.CommitRevealAuction
