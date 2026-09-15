/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.SourceQuitPrefix

/-! # A context-relative source quitting example

A public bit is sampled before the only decision.  Both quitting and continuing
receive the baseline selected by that bit.  Thus matching the public source
prefix makes quitting and continuing equal, while no single global value can
both cap the high-baseline quit and floor the low-baseline continuation.
-/

noncomputable section

namespace VegasTests.SourceQuitPrefix

open Vegas GameTheory GameTheory.Math.Probability

abbrev Player := Fin 1

def fairBit : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

def payout : Expr [(0, .bool)] .int :=
  .ite (.var 0 .here) (.constInt 10) (.constInt 0)

def core : VegasCore Player simpleExpr [] :=
  .sample 0 (b := .bool) (.weighted fairBit)
    (.commit 1 0 (b := .bool) (.constBool true) (.ret [(0, payout)]))

def site : SourceDecisionSite (L := simpleExpr) 0 core
    [(0, .pub .bool)] 1 .bool (.constBool true) :=
  .sample (.here _ _)

private def initial : VEnv (Player := Player) simpleExpr [] := VEnv.empty simpleExpr

private def terminalEnv (baseline choice : Bool) :
    VEnv simpleExpr (sourceTerminalCtx core) :=
  VEnv.cons (x := 1) (τ := (⟨.bool, .sealed 0⟩ : BindTy Player simpleExpr)) choice
    (VEnv.cons (x := 0) (τ := (⟨.bool, .pub⟩ : BindTy Player simpleExpr)) baseline
      (VEnv.empty simpleExpr))

private def baseline (final : VEnv simpleExpr (sourceTerminalCtx core)) : Bool :=
  final.get (.there .here)

private def valuation (result : Payout Player) (who : Player) : ℝ := result who

private def utility (final : VEnv simpleExpr (sourceTerminalCtx core))
    (who : Player) : ℝ :=
  valuation (evalPayoffs (sourceTerminalPayoffs core) final) who

private theorem utility_eq (final : VEnv simpleExpr (sourceTerminalCtx core)) :
    utility final 0 = if baseline final then 10 else 0 := by
  have herase : VEnv.erasePubEnv final =
      Env.cons (baseline final) (Env.empty simpleExpr.Val) := by
    funext name ty position
    cases position with
    | here => rfl
    | there position => cases position
  unfold utility
  rw [show sourceTerminalPayoffs core = [(0, payout)] from rfl]
  simp only [evalPayoffs]
  rw [herase]
  simp [valuation, payout, baseline, mkPayout, payoffAt, evalExpr, simpleExpr]

private theorem legal : Legal core := by
  constructor
  · intro _
    exact ⟨false, rfl⟩
  · trivial

def profile : SourceBehavioralProfile core := legalSourceProfile core legal

/-- Matching the exact public source prefix before the decision fixes the
sampled baseline, so the two terminal utilities coincide. -/
theorem quit_prefix_dominance :
    core.QuitPayoutPrefixDominanceAgainst (ty := .bool) initial false valuation profile := by
  intro who Δ name guard decision alternative quitting continued
    hquitting hquit hcontinued hprefix
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at decision
  cases decision with
  | sample decision =>
      cases decision with
      | here =>
          have hbaseline : baseline quitting = baseline continued := by
            have heq := congrFun (congrFun (congrFun hprefix 0) BaseTy.bool) (.here)
            exact heq
          change utility quitting 0 ≤ utility continued 0
          rw [utility_eq, utility_eq, hbaseline]
      | commit decision => cases decision

private def fixedFalse : SourceBehavioralPolicy core 0 := by
  intro Δ name ty guard decision visible
  unfold core at decision
  cases decision with
  | sample decision =>
      cases decision with
      | here => exact FinDist.pure ⟨false, rfl⟩
      | commit decision => cases decision

private theorem fairBit_support (value : Bool) :
    value ∈ fairBit.denote.support := by
  unfold fairBit
  apply FinDist.prob_pos_iff.mp
  rw [RationalLaw.prob_denote]
  apply Finset.sum_pos'
  · intro index _
    split <;> positivity
  · cases value
    · refine ⟨⟨0, by decide⟩, by simp, ?_⟩
      norm_num
    · refine ⟨⟨1, by decide⟩, by simp, ?_⟩
      norm_num

private theorem fixedFalse_support (baseline : Bool) :
    terminalEnv baseline false ∈
      (denoteSource core
        (Profile.update (sig := sourceGameSignature core) profile 0 fixedFalse)
        initial).support := by
  simp only [core, denoteSource, FinDist.support_bind, Set.mem_iUnion]
  refine ⟨baseline, fairBit_support baseline, ?_⟩
  refine ⟨⟨false, rfl⟩, ?_, ?_⟩
  · unfold SourceBehavioralProfile.afterSample
    rw [Profile.update_same]
    simp [fixedFalse]
  · simp [terminalEnv, initial]

private theorem fixedFalse_star (baseline : Bool) :
    SmallStep.Star ⟨[], initial, core⟩
      ⟨sourceTerminalCtx core, terminalEnv baseline false,
        .ret (sourceTerminalPayoffs core)⟩ :=
  denoteSource_support_star core
    (Profile.update (sig := sourceGameSignature core) profile 0 fixedFalse)
    initial _ (fixedFalse_support baseline)

private theorem chooses_false (baseline : Bool) :
    core.Chooses (ty := .bool) 0 false (terminalEnv baseline false) := by
  refine ⟨[(0, .pub .bool)], 1, .constBool true, site, ?_⟩
  rfl

/-- No equal global cap and fixed-opponent floor exists: the legal high-prefix
quit pays ten, while a supported low-prefix continuation pays zero. -/
theorem no_global_equal_cap_floor :
    ¬ ∃ bound : Player → ℝ,
      core.QuitPayoutBoundAgainst (ty := .bool) initial false valuation bound profile := by
  rintro ⟨bound, hbound⟩
  have hupper := hbound.quit_upper (terminalEnv true false)
    (fixedFalse_star true) 0 (chooses_false true)
  have hlower := hbound.lower 0 fixedFalse (terminalEnv false false)
    (fixedFalse_support false)
  change utility (terminalEnv true false) 0 ≤ bound 0 at hupper
  change bound 0 ≤ utility (terminalEnv false false) 0 at hlower
  rw [utility_eq] at hupper hlower
  norm_num [baseline, terminalEnv] at hupper hlower
  linarith

end VegasTests.SourceQuitPrefix

/-- info: 'VegasTests.SourceQuitPrefix.quit_prefix_dominance' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SourceQuitPrefix.quit_prefix_dominance

/-- info: 'VegasTests.SourceQuitPrefix.no_global_equal_cap_floor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SourceQuitPrefix.no_global_equal_cap_floor
