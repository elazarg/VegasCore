/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionReservations
import Vegas.Game.SourceCandidate

/-! # Profile-relative source settlement bounds

This two-player source separates the global quitting cap from the source floor
needed at a fixed profile. Player zero receives `-1` after choosing `none`;
otherwise it receives `1` when player one's public choice is `some true`, and
`-2` for every other player-one choice. Player one receives `0`.

At the always-`some true` profile every unilateral source deviation stays above
the quitting bound of its deviator. There is nevertheless no uniform source
floor compatible with the quitting cap, because player one can choose `none`
while player zero chooses a non-quitting value.
-/

noncomputable section

namespace VegasTests.SealedProfilePayout

open Vegas Vegas.EventGraph Vegas.ToEventGraph Vegas.SealedCompilation
open Interaction Interaction.MessageApplication Interaction.SealedResolution
open GameTheory GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev Value := Option Bool

def payout0 : Expr [(3, .option .bool), (1, .option .bool)] .int :=
  .ite (.isSome (.var 1 (.there .here)))
    (.ite (.eq (.var 3 .here) (.some (.constBool true)))
      (.constInt 1) (.constInt (-2)))
    (.constInt (-1))

def payout1 : Expr [(3, .option .bool), (1, .option .bool)] .int :=
  .constInt 0

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (b := .option .bool)
    (Expr.nullableCommitGuard (Expr.constBool true))
    (.reveal 1 0 0 .here
      (.commit 2 1 (b := .option .bool)
        (Expr.nullableCommitGuard (Expr.constBool true))
        (.reveal 3 1 2 .here (.ret [(0, payout0), (1, payout1)]))))

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
    · constructor
      · intro env
        exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
      · trivial

abbrev graph := (compile source.core).graph

def node (index : Fin 4) : Fin graph.nodeCount := index

theorem supported : SealedFragment graph (.option .bool) where
  graphWF := (compile source.core).graphWF
  rowType node := by fin_cases node <;> rfl
  noSamples node dist := by fin_cases node <;> intro h <;> cases h
  commitType node who guard hsem := by fin_cases node <;> cases hsem <;> rfl
  commitGuard node who guard hsem value env := by
    fin_cases node <;> cases hsem <;> cases value <;> rfl
  revealSource node sourceField hsem := by
    fin_cases node
    · cases hsem
    · cases hsem; exact ⟨node 0, 0, _, rfl, rfl⟩
    · cases hsem
    · cases hsem; exact ⟨node 2, 1, _, rfl, rfl⟩

theorem compilation : SealedCompilation source (.option .bool) := ⟨supported⟩

def firstSite : SourceDecisionSite (L := simpleExpr) 0 core []
    0 (.option .bool) (Expr.nullableCommitGuard (Expr.constBool true)) :=
  .here _ _

def secondSite : SourceDecisionSite (L := simpleExpr) 1 core
    [(1, .pub (.option .bool)), (0, .sealed 0 (.option .bool))]
    2 (.option .bool) (Expr.nullableCommitGuard (Expr.constBool true)) :=
  .commit (.reveal (.here _ _))

private def valuation (payout : Payout Player) (who : Player) : ℝ := payout who

private def bound : Player → ℝ
  | 0 => -1
  | 1 => 0

private def terminalEnv (left right : Value) :
    VEnv simpleExpr (sourceTerminalCtx core) :=
  VEnv.cons (x := 3) (τ := (⟨.option .bool, .pub⟩ : BindTy Player simpleExpr)) right
    (VEnv.cons (x := 2) (τ := (⟨.option .bool, .sealed 1⟩ : BindTy Player simpleExpr)) right
      (VEnv.cons (x := 1) (τ := (⟨.option .bool, .pub⟩ : BindTy Player simpleExpr)) left
        (VEnv.cons (x := 0) (τ := (⟨.option .bool, .sealed 0⟩ : BindTy Player simpleExpr)) left
          (VEnv.empty simpleExpr))))

private def leftPublic (final : VEnv simpleExpr (sourceTerminalCtx core)) : Value :=
  final.get (.there (.there .here))

private def rightPublic (final : VEnv simpleExpr (sourceTerminalCtx core)) : Value :=
  final.get .here

private def sourceUtility (final : VEnv simpleExpr (sourceTerminalCtx core))
    (who : Player) : ℝ :=
  valuation (evalPayoffs (sourceTerminalPayoffs core) final) who

private theorem source_utility_eq (final : VEnv simpleExpr (sourceTerminalCtx core)) :
    sourceUtility final 0 = (
        if (leftPublic final).isSome then
          if rightPublic final = some true then 1 else -2
        else -1) ∧
      sourceUtility final 1 = 0 := by
  have herase : VEnv.erasePubEnv final =
      Env.cons (rightPublic final) (Env.cons (leftPublic final) (Env.empty simpleExpr.Val)) := by
    funext name ty position
    cases position with
    | here => rfl
    | there position =>
        cases position with
        | here => rfl
        | there position => cases position
  change valuation (evalPayoffs [(0, payout0), (1, payout1)] final) 0 = _ ∧
    valuation (evalPayoffs [(0, payout0), (1, payout1)] final) 1 = 0
  simp only [evalPayoffs]
  rw [herase]
  simp [valuation, payout0, payout1, mkPayout, payoffAt, evalExpr, simpleExpr]

private theorem terminal_utility (left right : Value) :
    sourceUtility (terminalEnv left right) 0 =
        (if left.isSome then if right = some true then 1 else -2 else -1) ∧
      sourceUtility (terminalEnv left right) 1 = 0 := by
  simpa [leftPublic, rightPublic, terminalEnv] using source_utility_eq (terminalEnv left right)

private theorem no_step_ret {Γ : VCtx Player simpleExpr} (env : VEnv simpleExpr Γ)
    (payoffs : List (Player × Expr (erasePubVCtx Γ) .int)) (next : SourceConfig Player simpleExpr) :
    ¬ SmallStep ⟨Γ, env, .ret payoffs⟩ next := by
  intro hstep
  cases hstep

private theorem terminal_reveals_choices
    (final : VEnv simpleExpr (sourceTerminalCtx core))
    (hstar : SmallStep.Star
      ⟨source.core.Γ, source.core.env, source.core.prog⟩
      ⟨sourceTerminalCtx core, final, .ret (sourceTerminalPayoffs core)⟩) :
    final.get (.there (.there .here)) =
        final.get (.there (.there (.there .here))) ∧
      final.get .here = final.get (.there .here) := by
  rcases SmallStep.Star.eq_or_head hstar with heq | ⟨afterFirst, hfirst, hrest⟩
  · have hctx := congrArg SourceConfig.ctx heq
    have hterminalLength : (sourceTerminalCtx core).length = 4 := rfl
    have hlength := congrArg List.length hctx
    rw [hterminalLength] at hlength
    change 0 = 4 at hlength
    omega
  · cases hfirst with
    | commit =>
        rcases SmallStep.Star.eq_or_head hrest with heq | ⟨afterSecond, hsecond, hrest⟩
        · have hctx := congrArg SourceConfig.ctx heq
          have hterminalLength : (sourceTerminalCtx core).length = 4 := rfl
          have hlength := congrArg List.length hctx
          rw [hterminalLength] at hlength
          change 1 = 4 at hlength
          omega
        · cases hsecond with
          | reveal =>
              rcases SmallStep.Star.eq_or_head hrest with heq | ⟨afterThird, hthird, hrest⟩
              · have hctx := congrArg SourceConfig.ctx heq
                have hterminalLength : (sourceTerminalCtx core).length = 4 := rfl
                have hlength := congrArg List.length hctx
                rw [hterminalLength] at hlength
                change 2 = 4 at hlength
                omega
              · cases hthird with
                | commit =>
                    rcases SmallStep.Star.eq_or_head hrest with heq | ⟨afterFourth, hfourth, hrest⟩
                    · have hctx := congrArg SourceConfig.ctx heq
                      have hterminalLength : (sourceTerminalCtx core).length = 4 := rfl
                      have hlength := congrArg List.length hctx
                      rw [hterminalLength] at hlength
                      change 3 = 4 at hlength
                      omega
                    · cases hfourth with
                      | reveal =>
                          rcases SmallStep.Star.eq_or_head hrest with heq | ⟨_, himpossible, _⟩
                          · cases heq
                            exact ⟨rfl, rfl⟩
                          · exact (no_step_ret _ _ _ himpossible).elim

private theorem chooses_zero_value (final : VEnv simpleExpr (sourceTerminalCtx core))
    (value : Value) (hchooses : core.Chooses (ty := .option .bool) 0 value final) :
    final.get (.there (.there (.there .here))) = value := by
  rcases hchooses with ⟨Δ, name, guard, site, hvalue⟩
  unfold core at site
  cases site with
  | here => exact hvalue
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | commit site =>
              cases site with
              | reveal site => cases site

private theorem terminal_chooses_zero (left right : Value) :
    core.Chooses (ty := .option .bool) 0 left (terminalEnv left right) := by
  refine ⟨[], 0, _, firstSite, ?_⟩
  rfl

private def fixedZeroPolicy (left : Value) : SourceBehavioralPolicy core 0 := by
  intro Δ name ty guard site visible
  unfold core at site
  cases site with
  | here => exact FinDist.pure ⟨left, by cases left <;> rfl⟩
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | commit site =>
              cases site with
              | reveal site => cases site

private def fixedOnePolicy (right : Value) : SourceBehavioralPolicy core 1 := by
  intro Δ name ty guard site visible
  unfold core at site
  cases site with
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | here => exact FinDist.pure ⟨right, by cases right <;> rfl⟩
          | commit site =>
              cases site with
              | reveal site => cases site

private def fixedProfile (left right : Value) : SourceBehavioralProfile core :=
  fun who =>
    @Fin.cases 1 (fun player : Fin 2 => SourceBehavioralPolicy core player)
      (fixedZeroPolicy left)
      (fun tail =>
        @Fin.cases 0 (fun player : Fin 1 => SourceBehavioralPolicy core player.succ)
          (fixedOnePolicy right) (fun impossible => Fin.elim0 impossible) tail)
      who

@[simp] private theorem fixedProfile_zero_apply (left right : Value)
    {Δ name ty guard} (site : SourceDecisionSite 0 core Δ name ty guard)
    (visible : Env simpleExpr.Val (eraseVCtx (viewVCtx 0 Δ))) :
    fixedProfile left right 0 site visible = fixedZeroPolicy left site visible := by
  change (@Fin.cases 1 (fun player : Fin 2 => SourceBehavioralPolicy core player)
    (fixedZeroPolicy left)
    (fun tail => @Fin.cases 0 (fun player : Fin 1 => SourceBehavioralPolicy core player.succ)
      (fixedOnePolicy right) (fun impossible => Fin.elim0 impossible) tail) 0) site visible = _
  rw [Fin.cases_zero]

@[simp] private theorem fixedProfile_one_apply (left right : Value)
    {Δ name ty guard} (site : SourceDecisionSite 1 core Δ name ty guard)
    (visible : Env simpleExpr.Val (eraseVCtx (viewVCtx 1 Δ))) :
    fixedProfile left right 1 site visible = fixedOnePolicy right site visible := by
  change (@Fin.cases 1 (fun player : Fin 2 => SourceBehavioralPolicy core player)
    (fixedZeroPolicy left)
    (fun tail => @Fin.cases 0 (fun player : Fin 1 => SourceBehavioralPolicy core player.succ)
      (fixedOnePolicy right) (fun impossible => Fin.elim0 impossible) tail)
    (0 : Fin 1).succ) site visible = _
  rw [Fin.cases_succ, Fin.cases_zero]

def profile : SourceBehavioralProfile core :=
  fixedProfile (some true) (some true)

private theorem fixed_source_law (left right : Value) :
    denoteSource core (fixedProfile left right) source.core.env =
      FinDist.pure (terminalEnv left right) := by
  simp [source, core, denoteSource, fixedZeroPolicy, fixedOnePolicy,
    SourceBehavioralProfile.afterCommit, SourceBehavioralProfile.afterReveal, terminalEnv]

private theorem profile_source_law :
    denoteSource core profile source.core.env =
      FinDist.pure (terminalEnv (some true) (some true)) := by
  exact fixed_source_law _ _

private theorem fixed_source_star (left right : Value) :
    SmallStep.Star
      ⟨source.core.Γ, source.core.env, source.core.prog⟩
      ⟨sourceTerminalCtx core, terminalEnv left right,
        .ret (sourceTerminalPayoffs core)⟩ := by
  apply denoteSource_support_star core (fixedProfile left right) source.core.env
  rw [fixed_source_law, FinDist.mem_support_pure]

private theorem source_utility_le_one
    (law : FinDist (VEnv simpleExpr (sourceTerminalCtx core))) :
    law.expect (fun final => sourceUtility final 0) ≤ 1 := by
  apply FinDist.expect_le_of_forall
  intro final _
  rw [(source_utility_eq final).1]
  cases leftPublic final with
  | none => norm_num
  | some value =>
      cases rightPublic final with
      | none =>
          rw [if_neg (show (none : Value) ≠ some true by decide)]
          norm_num
      | some right => cases right <;> norm_num

theorem profile_isNash :
    IsNash (sourceGameForm core source.core.env)
      (euPreference sourceUtility) profile := by
  rw [GameTheory.isNash_iff_isεNash_zero, GameTheory.isεNash_iff]
  intro who alternative
  have hcases : who = 0 ∨ who = 1 := by fin_cases who <;> simp
  rcases hcases with hwho | hwho
  · subst who
    calc
      expectedUtility sourceUtility 0
          ((sourceGameForm core source.core.env).play
            (Profile.update profile 0 alternative)) ≤ 1 := source_utility_le_one _
      _ = expectedUtility sourceUtility 0
          ((sourceGameForm core source.core.env).play profile) + 0 := by
        rw [sourceGameForm_play, profile_source_law]
        rw [expectedUtility, FinDist.expect_pure, (terminal_utility _ _).1]
        norm_num
  · subst who
    calc
      expectedUtility sourceUtility 1
          ((sourceGameForm core source.core.env).play
            (Profile.update profile 1 alternative)) = 0 := by
        rw [expectedUtility]
        exact (FinDist.expect_congr (fun final _ => (source_utility_eq final).2)).trans
          (FinDist.expect_const _ _)
      _ = expectedUtility sourceUtility 1
          ((sourceGameForm core source.core.env).play profile) + 0 := by
        rw [sourceGameForm_play, profile_source_law]
        rw [expectedUtility, FinDist.expect_pure, (terminal_utility _ _).2]
        norm_num
      _ ≤ _ := le_rfl

private theorem update_zero_source_law
    (alternative : SourceBehavioralPolicy core 0) :
    denoteSource core (Profile.update (sig := sourceGameSignature core) profile 0 alternative)
      source.core.env =
      (alternative firstSite (Env.empty simpleExpr.Val)).bind fun choice =>
        FinDist.pure (terminalEnv choice.1 (some true)) := by
  simp [source, core, profile, fixedOnePolicy, denoteSource,
    SourceBehavioralProfile.afterCommit, SourceBehavioralProfile.afterReveal, firstSite,
    terminalEnv]
  rfl

/-- Every supported unilateral source deviation against the fixed opponents
stays above that deviator's quitting settlement. -/
theorem source_floor_against_profile :
    core.QuitPayoutBoundAgainst (ty := .option .bool) source.core.env
      (none : Value) valuation bound profile := by
  refine { lower := ?_, quit_upper := ?_ }
  · intro who alternative final hfinal
    have hcases : who = 0 ∨ who = 1 := by fin_cases who <;> simp
    rcases hcases with hwho | hwho
    · subst who
      rw [update_zero_source_law] at hfinal
      rw [FinDist.support_bind] at hfinal
      obtain ⟨choice, _hchoice, hterminal⟩ := Set.mem_iUnion₂.mp hfinal
      rw [FinDist.mem_support_pure] at hterminal
      subst final
      change bound 0 ≤ sourceUtility (terminalEnv choice.1 (some true)) 0
      rw [(terminal_utility choice.1 (some true)).1]
      cases choice.1 <;> norm_num [bound]
    · subst who
      change bound 1 ≤ sourceUtility final 1
      rw [(source_utility_eq final).2]
      rfl
  · intro final hstar who hchooses
    have hcases : who = 0 ∨ who = 1 := by fin_cases who <;> simp
    rcases hcases with hwho | hwho
    · subst who
      have hsecret := chooses_zero_value final none hchooses
      have hpublic := (terminal_reveals_choices final hstar).1
      rw [hsecret] at hpublic
      have hleft : leftPublic final = none := hpublic
      change sourceUtility final 0 ≤ bound 0
      rw [(source_utility_eq final).1, hleft]
      norm_num [bound, leftPublic]
    · subst who
      change sourceUtility final 1 ≤ bound 1
      rw [(source_utility_eq final).2]
      rfl

/-- The quitting half remains global: it covers every legal source settlement,
including settlements generated by arbitrary choices of both players. -/
theorem source_quitting_cap :
    core.QuitPayoutCap (ty := .option .bool) source.core.env (none : Value) valuation bound :=
  source_floor_against_profile.quit_upper

/-- No player-indexed bound can simultaneously be a global source floor and a
global quitting cap for this source. -/
theorem no_uniform_quit_payout_bound :
    ¬ ∃ uniform : Player → ℝ,
      core.QuitPayoutBound (ty := .option .bool) source.core.env
        (none : Value) valuation uniform := by
  rintro ⟨uniform, huniform⟩
  have hlower := huniform.lower (terminalEnv (some true) none)
    (fixed_source_star (some true) none) 0
  have hupper := huniform.quit_upper (terminalEnv none (some true))
    (fixed_source_star none (some true)) 0 (terminal_chooses_zero none (some true))
  change uniform 0 ≤ sourceUtility (terminalEnv (some true) none) 0 at hlower
  change sourceUtility (terminalEnv none (some true)) 0 ≤ uniform 0 at hupper
  rw [(terminal_utility (some true) none).1] at hlower
  rw [(terminal_utility none (some true)).1] at hupper
  simp at hlower hupper
  linarith

private abbrev runtime := supported.resolvingRuntime none 14
private abbrev app := runtime.candidateApplication

private def candidateModel (base : app.WirePolicy) :
    supported.CandidateRoundModel none 14 where
  principals := [0, 1]
  serviceSlots := 4
  total := 60
  wire := app.reserveInclusion (periodicFinalReservation 4 2) base
  budget := by decide

private def candidateTimely (base : app.WirePolicy) :
    (candidateModel base).Timely where
  reserved := periodicFinalReservation 4 2
  service := app.reserveInclusion_service _ base
  period := 2
  positive := by decide
  capacity := fun block => periodicFinalReservation_capacity [0, 1] 4 2 block
    (by decide) (by decide)
  roster := by intro who; fin_cases who <;> simp [candidateModel]
  windowBound := by decide
  wholePeriods := ⟨30, rfl⟩

/-- The profile-relative source theorem applies to the actual candidate-message
round game, with an arbitrary adaptive policy for unreserved wire actions. -/
theorem candidate_profile_isNash (base : app.WirePolicy) :
    IsNash (candidateModel base).game
      (euPreference (fun next who =>
        (compilation.publicPayout? next.native.application.visible.events).elim
          (0 : ℝ) (fun payout => valuation payout who)))
      (fun who => compilation.compileCandidatePolicy none 14 who (profile who)) := by
  rw [GameTheory.isNash_iff_isεNash_zero]
  apply (compilation.candidate_approximate_nash_iff_of_source_floor none 14
    (candidateModel base) (candidateTimely base) valuation (fun _ => 0) bound profile
    source_floor_against_profile 0).2
  change IsεNash (sourceGameForm core source.core.env) sourceUtility 0 profile
  exact (GameTheory.isNash_iff_isεNash_zero
    (sourceGameForm core source.core.env) sourceUtility).mp profile_isNash

/-- Competing and unopenable candidates, malformed messages, withholding, and
all other observation-local native player-zero policies are covered by the
unrestricted replacement below. -/
theorem candidate_arbitrary_zero_deviation_bound (base : app.WirePolicy)
    (replacement : (candidateModel base).game.sig.Strategy 0) :
    ((candidateModel base).game.play (Profile.update
      (fun who => compilation.compileCandidatePolicy none 14 who (profile who))
      0 replacement)).expect (fun next =>
        (compilation.publicPayout? next.native.application.visible.events).elim
          (0 : ℝ) (fun payout => valuation payout 0)) ≤ 1 := by
  obtain ⟨alternative, hdeviation⟩ :=
    compilation.candidate_deviation_bound_of_source_floor none 14
      (candidateModel base) (candidateTimely base) valuation (fun _ => 0) bound profile
      source_floor_against_profile 0 replacement
  exact hdeviation.trans (source_utility_le_one _)

end VegasTests.SealedProfilePayout

/-- info: 'VegasTests.SealedProfilePayout.no_uniform_quit_payout_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedProfilePayout.no_uniform_quit_payout_bound

/-- info: 'VegasTests.SealedProfilePayout.candidate_profile_isNash'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedProfilePayout.candidate_profile_isNash

/-- info: 'VegasTests.SealedProfilePayout.candidate_arbitrary_zero_deviation_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedProfilePayout.candidate_arbitrary_zero_deviation_bound
