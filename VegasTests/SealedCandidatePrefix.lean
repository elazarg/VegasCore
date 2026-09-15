/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionReservations
import Vegas.Game.SourceCandidate

/-! # Prefix-relative candidate deviation regression

Player zero first chooses and reveals a public baseline. Player one's payout is
that baseline and is independent of player one's later choice. Consequently a
null settlement at either decision is no better than a continuation with the
same public source prefix. The source condition is instantiated in the actual
candidate-message round game with arbitrary native unilateral policies.
-/

noncomputable section

namespace VegasTests.SealedCandidatePrefix

open Vegas Vegas.EventGraph Vegas.ToEventGraph Vegas.SealedCompilation
open Interaction Interaction.MessageApplication Interaction.SealedResolution
open GameTheory GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev Value := Option Bool

def payout0 : Expr [(3, .option .bool), (1, .option .bool)] .int :=
  .constInt 0

def payout1 : Expr [(3, .option .bool), (1, .option .bool)] .int :=
  .ite (.eq (.var 1 (.there .here)) (.some (.constBool true)))
    (.constInt 10) (.constInt 0)

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

private def baselineLaw : RationalLaw Value where
  entries := [(some false, 1 / 2), (some true, 1 / 2)]
  normalized := by norm_num

private def baselinePolicy : SourceBehavioralPolicy core 0 := by
  intro Δ name ty guard site visible
  unfold core at site
  cases site with
  | here =>
      exact baselineLaw.denote.map fun value => ⟨value, by cases value <;> rfl⟩
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | commit site =>
              cases site with
              | reveal site => cases site

private def secondPolicy : SourceBehavioralPolicy core 1 := by
  intro Δ name ty guard site visible
  unfold core at site
  cases site with
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | here => exact FinDist.pure ⟨some true, rfl⟩
          | commit site =>
              cases site with
              | reveal site => cases site

def profile : SourceBehavioralProfile core := fun who =>
  @Fin.cases 1 (fun player : Fin 2 => SourceBehavioralPolicy core player)
    baselinePolicy
    (fun tail => @Fin.cases 0 (fun player : Fin 1 => SourceBehavioralPolicy core player.succ)
      secondPolicy (fun impossible => Fin.elim0 impossible) tail)
    who

private def baseline (final : VEnv simpleExpr (sourceTerminalCtx core)) : Value :=
  final.get (.there (.there .here))

private def valuation (result : Payout Player) (who : Player) : ℝ := result who

private def sourceUtility (final : VEnv simpleExpr (sourceTerminalCtx core))
    (who : Player) : ℝ :=
  valuation (evalPayoffs (sourceTerminalPayoffs core) final) who

private theorem source_utility_eq (final : VEnv simpleExpr (sourceTerminalCtx core)) :
    sourceUtility final 0 = 0 ∧
      sourceUtility final 1 = if baseline final = some true then 10 else 0 := by
  have herase : VEnv.erasePubEnv final =
      Env.cons (final.get .here) (Env.cons (baseline final) (Env.empty simpleExpr.Val)) := by
    funext name ty position
    cases position with
    | here => rfl
    | there position =>
        cases position with
        | here => rfl
        | there position => cases position
  change valuation (evalPayoffs [(0, payout0), (1, payout1)] final) 0 = 0 ∧
    valuation (evalPayoffs [(0, payout0), (1, payout1)] final) 1 = _
  simp only [evalPayoffs]
  rw [herase]
  simp [valuation, payout0, payout1, baseline, mkPayout, payoffAt, evalExpr, simpleExpr]

/-- At player one's decision, equal public prefixes fix player zero's revealed
baseline. Player zero's utility is constant, so the same source condition also
holds at the first decision. -/
theorem quit_prefix_dominance :
    core.QuitPayoutPrefixDominanceAgainst (ty := .option .bool) source.core.env
      (none : Value) valuation profile := by
  intro who Δ name guard site alternative quitting continued
    hquitting hquit hcontinued hprefix
  have hcases : who = 0 ∨ who = 1 := by fin_cases who <;> simp
  rcases hcases with hwho | hwho
  · subst who
    change sourceUtility quitting 0 ≤ sourceUtility continued 0
    rw [(source_utility_eq quitting).1, (source_utility_eq continued).1]
  · subst who
    unfold core at site
    cases site with
    | commit site =>
        cases site with
        | reveal site =>
            cases site with
            | here =>
                have hbaseline : baseline quitting = baseline continued := by
                  have heq := congrFun
                    (congrFun (congrFun hprefix 1) (.option .bool)) (.here)
                  exact heq
                change sourceUtility quitting 1 ≤ sourceUtility continued 1
                rw [(source_utility_eq quitting).2, (source_utility_eq continued).2,
                  hbaseline]
            | commit site =>
                cases site with
                | reveal site => cases site

private abbrev runtime := supported.resolvingRuntime none 14
private abbrev app := runtime.candidateApplication

private def model (base : app.WirePolicy) : supported.CandidateRoundModel none 14 where
  principals := [0, 1]
  serviceSlots := 4
  total := 60
  wire := app.reserveInclusion (periodicFinalReservation 4 2) base
  budget := by decide

private def timely (base : app.WirePolicy) : (model base).Timely where
  reserved := periodicFinalReservation 4 2
  service := app.reserveInclusion_service _ base
  period := 2
  positive := by decide
  capacity := fun block => periodicFinalReservation_capacity [0, 1] 4 2 block
    (by decide) (by decide)
  roster := by intro who; fin_cases who <;> simp [model]
  windowBound := by decide
  wholePeriods := ⟨30, rfl⟩

/-- The prefix-relative source condition bounds every observation-local native
unilateral deviation in the actual candidate-message game. The wire's
unreserved actions remain arbitrary. -/
theorem arbitrary_native_deviation_bound (base : app.WirePolicy) (who : Player)
    (replacement : (model base).game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy core who,
      ((model base).game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy none 14 player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicPayout? next.native.application.visible.events).elim
            (0 : ℝ) (fun result => valuation result who)) ≤
      ((sourceGameForm core source.core.env).play
        (Profile.update profile who alternative)).expect (fun final =>
          valuation (evalPayoffs (sourceTerminalPayoffs core) final) who) := by
  exact compilation.candidate_deviation_bound_of_source_quit_prefix none 14
    (model base) (timely base) valuation (fun _ => 0) profile quit_prefix_dominance who replacement

end VegasTests.SealedCandidatePrefix

/-- info: 'VegasTests.SealedCandidatePrefix.quit_prefix_dominance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedCandidatePrefix.quit_prefix_dominance

/-- info: 'VegasTests.SealedCandidatePrefix.arbitrary_native_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedCandidatePrefix.arbitrary_native_deviation_bound
