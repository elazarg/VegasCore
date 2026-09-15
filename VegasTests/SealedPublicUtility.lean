/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionReservations
import Vegas.Game.SourcePublicCandidate

/-! # Candidate utilities beyond programmed payouts

This one-player source has no payout expressions.  Its public reveal still
supports a nonconstant utility: a disclosed non-null option is worth one and
the disclosed null is worth zero.  Prefix-relative quitting dominance applies
directly to that public interpretation and bounds every native replacement,
although no valuation of the empty programmed payout can express the utility.
-/

noncomputable section

namespace VegasTests.SealedPublicUtility

open Vegas Vegas.EventGraph Vegas.ToEventGraph Vegas.SealedCompilation
open Interaction Interaction.MessageApplication Interaction.SealedResolution
open GameTheory GameTheory.Math.Probability

abbrev Player := Fin 1
abbrev Value := Option Bool

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (b := .option .bool)
    (Expr.nullableCommitGuard (Expr.constBool true))
    (.reveal 1 0 0 .here (.ret []))

def source : WFProgram Player simpleExpr where
  core := {
    Γ := []
    prog := core
    env := VEnv.empty simpleExpr
    wctx := by simp
    fresh := by simp [core, FreshBindings, Fresh] }
  accounted := CommitmentAccounting.ofRevealComplete core
    (by simp [core, FreshBindings, Fresh]) [] (by simp) (by decide)
  legal := by
    unfold core
    constructor
    · intro env
      exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
    · trivial

abbrev graph := (compile source.core).graph

private def node (index : Fin 2) : Fin graph.nodeCount := index

theorem supported : SealedFragment graph (.option .bool) where
  graphWF := (compile source.core).graphWF
  rowType node := by fin_cases node <;> rfl
  noSamples node dist := by fin_cases node <;> intro h <;> cases h
  commitType node who guard hsem := by
    fin_cases node
    · cases hsem
      rfl
    · cases hsem
  commitGuard node who guard hsem value env := by
    fin_cases node
    · cases hsem
      cases value
      all_goals rfl
    · cases hsem
  revealSource node sourceField hsem := by
    fin_cases node
    · cases hsem
    · cases hsem; exact ⟨node 0, 0, _, rfl, rfl⟩

theorem compilation : SealedCompilation source (.option .bool) := ⟨supported⟩

/-- The public outcome, rather than the empty payout list, carries utility. -/
def interpretation
    (outcome : Env simpleExpr.Val
      (erasePubVCtx (sourceTerminalCtx core))) (_who : Player) : ℝ :=
  if (outcome.get .here : Value).isSome then 1 else 0

private def fixedProfile (value : Value) : SourceBehavioralProfile core := by
  intro who Δ name ty guard site visible
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at site
  cases site with
  | here => exact FinDist.pure ⟨value, by cases value <;> rfl⟩
  | commit site =>
      cases site with
      | reveal site => cases site

def profile : SourceBehavioralProfile core := fixedProfile (some true)

private def terminalEnv (value : Value) :
    VEnv simpleExpr (sourceTerminalCtx core) :=
  (VEnv.empty simpleExpr).cons value |>.cons value

private theorem fixed_source_law (value : Value) :
    denoteSource core (fixedProfile value) source.core.env =
      FinDist.pure (terminalEnv value) := by
  simp only [source, core, denoteSource, fixedProfile,
    VegasCore.commit.noConfusion, VegasCore.noConfusion, id_eq, FinDist.pure_bind]
  rfl

private theorem no_step_ret {Γ : VCtx Player simpleExpr} (env : VEnv simpleExpr Γ)
    (payoffs : List (Player × Expr (erasePubVCtx Γ) .int))
    (next : SourceConfig Player simpleExpr) :
    ¬ SmallStep ⟨Γ, env, .ret payoffs⟩ next := by
  intro hstep
  cases hstep

private theorem terminal_public_eq_commit
    (final : VEnv simpleExpr (sourceTerminalCtx core))
    (hstar : SmallStep.Star
      ⟨source.core.Γ, source.core.env, source.core.prog⟩
      ⟨sourceTerminalCtx core, final, .ret (sourceTerminalPayoffs core)⟩) :
    final.get (.here : VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) =
      final.get (.there .here :
        VHasVar (sourceTerminalCtx core) 0 (.sealed 0 (.option .bool))) := by
  rcases SmallStep.Star.eq_or_head hstar with heq | ⟨afterCommit, hcommit, hrest⟩
  · have hctx := congrArg SourceConfig.ctx heq
    have hlength := congrArg List.length hctx
    change 0 = 2 at hlength
    omega
  · cases hcommit with
    | commit =>
        rcases SmallStep.Star.eq_or_head hrest with heq | ⟨afterReveal, hreveal, hrest⟩
        · have hctx := congrArg SourceConfig.ctx heq
          have hlength := congrArg List.length hctx
          change 1 = 2 at hlength
          omega
        · cases hreveal with
          | reveal =>
              rcases SmallStep.Star.eq_or_head hrest with heq | ⟨_, himpossible, _⟩
              · cases heq
                rfl
              · exact (no_step_ret _ _ _ himpossible).elim

private theorem source_utility_eq
    (final : VEnv simpleExpr (sourceTerminalCtx core)) (who : Player) :
    interpretation final.erasePubEnv who =
      if (final.get (.here :
        VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) : Value).isSome
      then 1 else 0 := by
  rfl

/-- Quitting is worth zero, while every continued public outcome is worth
either zero or one. -/
theorem quit_prefix_dominance :
    core.QuitPrefixDominanceAgainst (ty := .option .bool)
      source.core.env (none : Value)
      (fun final who => interpretation final.erasePubEnv who) profile := by
  intro who Δ name guard site alternative quitting continued
    hquitting hquit hcontinued hprefix
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at site
  cases site with
  | here =>
      have hsecret : quitting.get (.there .here :
          VHasVar (sourceTerminalCtx core) 0 (.sealed 0 (.option .bool))) = none := by
        exact hquit
      have hpublic := terminal_public_eq_commit quitting hquitting
      rw [hsecret] at hpublic
      change interpretation quitting.erasePubEnv 0 ≤
        interpretation continued.erasePubEnv 0
      rw [source_utility_eq quitting, source_utility_eq continued, hpublic]
      cases continued.get (.here :
        VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) <;> norm_num
  | commit site =>
      cases site with
      | reveal site => cases site

/-- Both null and non-null public outcomes are reachable, but their empty
programmed payouts are identical, so this utility has no payout valuation. -/
theorem public_utility_not_payout_factor :
    ¬ ∃ valuation : Payout Player → Player → ℝ,
      ∀ (sourceProfile : SourceBehavioralProfile core)
        (final : VEnv simpleExpr (sourceTerminalCtx core)),
        final ∈ (denoteSource core sourceProfile source.core.env).support →
        interpretation final.erasePubEnv 0 =
          valuation (evalPayoffs (sourceTerminalPayoffs core) final) 0 := by
  rintro ⟨valuation, hvaluation⟩
  have hnone := hvaluation (fixedProfile none) (terminalEnv none) (by
    rw [fixed_source_law]
    exact FinDist.mem_support_pure.mpr rfl)
  have hsome := hvaluation (fixedProfile (some true)) (terminalEnv (some true)) (by
    rw [fixed_source_law]
    exact FinDist.mem_support_pure.mpr rfl)
  have heq := hnone.trans hsome.symm
  change (0 : ℝ) = 1 at heq
  norm_num at heq

private abbrev runtime := supported.resolvingRuntime none 8
private abbrev app := runtime.candidateApplication

private def model (base : app.WirePolicy) : supported.CandidateRoundModel none 8 where
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
  roster := by intro who; fin_cases who; simp [model]
  windowBound := by decide
  wholePeriods := ⟨9, rfl⟩

private theorem source_equilibrium :
    IsεNash (sourceGameForm core source.core.env)
      (fun final who => interpretation final.erasePubEnv who) 0 profile := by
  rw [GameTheory.isεNash_iff]
  intro who replacement
  have hhonest : expectedUtility
      (fun final who => interpretation final.erasePubEnv who) who
      ((sourceGameForm core source.core.env).play profile) = 1 := by
    rw [sourceGameForm_play]
    change (denoteSource core (fixedProfile (some true)) source.core.env).expect _ = 1
    rw [fixed_source_law, FinDist.expect_pure]
    rfl
  rw [hhonest, add_zero]
  apply FinDist.expect_le_of_forall
  intro final _
  change (if (final.get (.here :
    VHasVar (sourceTerminalCtx core) 1 (.pub (.option .bool))) : Value).isSome
    then (1 : ℝ) else 0) ≤ 1
  split <;> norm_num

/-- A source equilibrium for non-monetary participation utility is preserved
in the actual candidate game, for every adaptive unreserved wire policy. -/
theorem compiled_public_equilibrium (base : app.WirePolicy) :
    IsNash (model base).game
      (euPreference (fun next who =>
        (compilation.publicSourceOutcome? next.native.application.visible.events).elim
          (0 : ℝ) (fun outcome => interpretation outcome who)))
      (fun who => compilation.compileCandidatePolicy none 8 who (profile who)) := by
  rw [GameTheory.isNash_iff_isεNash_zero]
  exact (compilation.candidate_public_approximate_nash_iff none 8
    (model base) (timely base) interpretation (fun _ => 0) profile
    quit_prefix_dominance 0).2 source_equilibrium

/-- Every observation-local native replacement is bounded by a legal source
alternative for the non-payout public utility. -/
theorem arbitrary_native_deviation_bound (base : app.WirePolicy) (who : Player)
    (replacement : (model base).game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy core who,
      ((model base).game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy none 8 player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicSourceOutcome?
            next.native.application.visible.events).elim
            (0 : ℝ) (fun outcome => interpretation outcome who)) ≤
      ((sourceGameForm core source.core.env).play
        (Profile.update profile who alternative)).expect
          (fun final => interpretation final.erasePubEnv who) := by
  exact compilation.candidate_public_deviation_bound none 8
    (model base) (timely base) interpretation (fun _ => 0) profile
    quit_prefix_dominance who replacement

end VegasTests.SealedPublicUtility

/-- info: 'VegasTests.SealedPublicUtility.quit_prefix_dominance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPublicUtility.quit_prefix_dominance

/-- info: 'VegasTests.SealedPublicUtility.public_utility_not_payout_factor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPublicUtility.public_utility_not_payout_factor

/-- info: 'VegasTests.SealedPublicUtility.arbitrary_native_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPublicUtility.arbitrary_native_deviation_bound

/-- info: 'VegasTests.SealedPublicUtility.compiled_public_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPublicUtility.compiled_public_equilibrium
