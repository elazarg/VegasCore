/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionReservations
import Vegas.Game.SealedPayoutBounds
import VegasTests.SealedPublicSettlement

/-! # Source-defined sealed payout bounds

The one-player source pays `7` after either nonempty Boolean commitment and
`-3` after the explicit `none` choice.  Its quit bound is proved from the
written small-step semantics and then transported to the actual pending-message
round game with deadline-relative service.
-/

noncomputable section

namespace VegasTests.SealedPayout

open Vegas Vegas.EventGraph Vegas.ToEventGraph Vegas.SealedCompilation
open Interaction Interaction.MessageApplication Interaction.SealedResolution
open GameTheory GameTheory.Math.Probability
open SealedPublicSettlement

private def valuation (payout : Payout SealedPublicSettlement.Player)
    (who : SealedPublicSettlement.Player) : ℝ := payout who

private def bound (_ : SealedPublicSettlement.Player) : ℝ := -3

private theorem terminal_public_eq_commit
    (final : VEnv simpleExpr (sourceTerminalCtx core))
    (hstar : SmallStep.Star
      ⟨source.core.Γ, source.core.env, source.core.prog⟩
      ⟨sourceTerminalCtx core, final, .ret (sourceTerminalPayoffs core)⟩) :
    final.get (.here : VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) =
      final.get (.there .here :
        VHasVar (sourceTerminalCtx core) 0 (.sealed 0 (.option .bool))) := by
  cases hstar with
  | tail hprefix hlast =>
      cases hlast with
      | sample =>
          cases hprefix with
          | tail hzero hstep =>
              cases hstep
              cases hzero with
              | tail _ himpossible => cases himpossible
      | reveal =>
          cases hprefix with
          | tail hzero hstep =>
              cases hstep
              cases hzero with
              | refl => rfl
              | tail _ himpossible => cases himpossible

private theorem source_utility_eq (final : VEnv simpleExpr (sourceTerminalCtx core)) :
    sourcePayoutUtility (source := source) valuation final 0 =
      if (final.get (.here :
        VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool)))).isSome
      then 7 else -3 := by
  change valuation (evalPayoffs (sourceTerminalPayoffs core) final) 0 = _
  let disclosed : Value := final.get (.here :
    VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool)))
  let secret : Value := final.get (.there .here :
    VHasVar (sourceTerminalCtx core) 0 (.sealed 0 (.option .bool)))
  have hfinal : final =
      VEnv.cons (x := 1)
        (τ := (⟨BaseTy.option BaseTy.bool, Visibility.pub⟩ :
          BindTy SealedPublicSettlement.Player simpleExpr)) disclosed
        (VEnv.cons (x := 0)
          (τ := (⟨BaseTy.option BaseTy.bool, Visibility.sealed 0⟩ :
            BindTy SealedPublicSettlement.Player simpleExpr)) secret
          (VEnv.empty simpleExpr)) := by
    funext name binding position
    cases position with
    | here => rfl
    | there position =>
        cases position with
        | here => rfl
        | there position => cases position
  rw [hfinal]
  unfold valuation
  rw [show sourceTerminalPayoffs core = [(0, payoff)] from rfl]
  cases disclosed with
  | none =>
      change (evalExpr payoff (Env.cons none (Env.empty Val)) : ℝ) = -3
      rw [payoff_depends_on_public_value.1]
      norm_num
  | some value =>
      change (evalExpr payoff (Env.cons (some value) (Env.empty Val)) : ℝ) = 7
      cases value <;> rfl

/-- The actual source has a nonconstant payout and its explicit `none` choice
is exactly the global lower settlement bound. -/
theorem concrete_quit_payout_bound :
    core.QuitPayoutBound (ty := .option .bool) source.core.env
      (none : Value) valuation bound := by
  constructor
  · intro final _hstar who
    have hwho : who = 0 := Subsingleton.elim _ _
    subst who
    change bound 0 ≤ sourcePayoutUtility (source := source) valuation final 0
    rw [source_utility_eq]
    cases final.get (.here :
      VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) <;> norm_num [bound]
  · intro final hstar who hchooses
    have hwho : who = 0 := Subsingleton.elim _ _
    subst who
    have hcommit :
        final.get (.there .here :
          VHasVar (sourceTerminalCtx core) 0 (.sealed 0 (.option .bool))) = none := by
      rcases hchooses with ⟨Δ, name, guard, site, hvalue⟩
      unfold core at site
      cases site with
      | here => exact hvalue
      | commit site =>
          cases site with
          | reveal site => cases site
    have hpublic := terminal_public_eq_commit final hstar
    rw [hcommit] at hpublic
    have hnone : final.get (.here :
        VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) = none := hpublic
    change sourcePayoutUtility (source := source) valuation final 0 ≤ bound 0
    rw [source_utility_eq, hnone]
    norm_num [bound]

private abbrev runtime := supported.resolvingRuntime none 8
private abbrev app := runtime.messageApplication

private def model (base : app.WirePolicy) : RoundModel compilation none 8 where
  principals := [0]
  serviceSlots := 2
  total := 18
  wire := app.reserveInclusion (periodicFinalReservation 2 2) base
  budget := by decide

private def timely (base : app.WirePolicy) : (model base).Timely where
  reserved := periodicFinalReservation 2 2
  service := app.reserveInclusion_service _ base
  period := 2
  positive := by decide
  capacity := fun block => periodicFinalReservation_capacity [0] 2 2 block
    (by decide) (by decide)
  roster := by
    intro who
    fin_cases who
    simp [model]
  windowBound := by decide
  wholePeriods := ⟨9, rfl⟩

def alwaysTrueProfile : SourceBehavioralProfile core := by
  intro who Δ name ty guard site visible
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at site
  cases site with
  | here => exact FinDist.pure ⟨some true, rfl⟩
  | commit site =>
      cases site with
      | reveal site => cases site

private def trueTerminal : VEnv simpleExpr (sourceTerminalCtx core) :=
  (VEnv.empty simpleExpr).cons (some true) |>.cons (some true)

private theorem alwaysTrue_source_law :
    denoteSource core alwaysTrueProfile source.core.env = FinDist.pure trueTerminal := by
  simp only [source, core, denoteSource, alwaysTrueProfile, VegasCore.commit.noConfusion,
    VegasCore.noConfusion, id_eq, FinDist.pure_bind]
  rfl

private theorem source_payout_le_seven
    (law : FinDist (VEnv simpleExpr (sourceTerminalCtx core)))
    (who : SealedPublicSettlement.Player) :
    law.expect (fun outcome =>
      sourcePayoutUtility (source := source) valuation outcome who) ≤ 7 := by
  apply FinDist.expect_le_of_forall
  intro outcome _
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  rw [source_utility_eq]
  cases outcome.get (.here :
    VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) <;> norm_num

theorem alwaysTrue_source_isNash :
    IsNash (sourceGameForm core source.core.env)
      (euPreference (sourcePayoutUtility (source := source) valuation))
      alwaysTrueProfile := by
  rw [GameTheory.isNash_iff_isεNash_zero, GameTheory.isεNash_iff]
  intro who replacement
  have hdeviation := source_payout_le_seven
    ((sourceGameForm core source.core.env).play
      (Profile.update alwaysTrueProfile who replacement)) who
  calc
    expectedUtility (sourcePayoutUtility (source := source) valuation) who
        ((sourceGameForm core source.core.env).play
          (Profile.update alwaysTrueProfile who replacement)) ≤ 7 := hdeviation
    _ = expectedUtility (sourcePayoutUtility (source := source) valuation) who
        ((sourceGameForm core source.core.env).play alwaysTrueProfile) + 0 := by
      have hwho : who = 0 := Subsingleton.elim _ _
      subst who
      rw [sourceGameForm_play, alwaysTrue_source_law]
      rw [expectedUtility, FinDist.expect_pure, source_utility_eq]
      norm_num [trueTerminal]

/-- The source payout theorem gives same-error equilibrium correspondence for
the actual round driver under any adaptive unreserved wire policy. -/
theorem concrete_isεNash_iff (base : app.WirePolicy) (ε : ℝ)
    (profile : SourceBehavioralProfile core) :
    IsεNash (model base).game
        (nativePayoutUtility (model base) valuation bound) ε
        (fun who => compilation.compileResolvingPolicy none 8 who (profile who)) ↔
      IsεNash (sourceGameForm core source.core.env)
        (sourcePayoutUtility (source := source) valuation) ε profile :=
  (model base).isεNash_iff_of_sourcePayoutBound (timely base) valuation bound bound
    concrete_quit_payout_bound ε profile

/-- The always-`some true` source equilibrium compiles to an equilibrium of the
actual pending-message game, whose utility is the publicly reconstructed
programmed payout. -/
theorem compiled_alwaysTrue_isNash (base : app.WirePolicy) :
    IsNash (model base).game
      (euPreference (nativePayoutUtility (model base) valuation bound))
      (fun who => compilation.compileResolvingPolicy none 8 who
        (alwaysTrueProfile who)) := by
  rw [GameTheory.isNash_iff_isεNash_zero]
  exact (concrete_isεNash_iff base 0 alwaysTrueProfile).2
    ((GameTheory.isNash_iff_isεNash_zero
      (sourceGameForm core source.core.env)
      (sourcePayoutUtility (source := source) valuation)).mp alwaysTrue_source_isNash)

end VegasTests.SealedPayout

/-- info: 'VegasTests.SealedPayout.compiled_alwaysTrue_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPayout.compiled_alwaysTrue_isNash
