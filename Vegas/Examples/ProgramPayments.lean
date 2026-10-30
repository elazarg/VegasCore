/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.ProgramPaymentNash

/-! # An executable payment reverses a player's strict incentive

A player commits to a Boolean and reveals it. Choosing true has valuation
minus one; the program pays its displayed integer bonus precisely when true is
published. A bonus of two makes true strictly better, while zero makes false
strictly better. Both utility and compiled transfer readout evaluate `ret`.
-/

noncomputable section

namespace Vegas.Examples.ProgramPayments

open SourceProgram GameTheory GameTheory.Math.Probability

inductive Player where
  | alice
  deriving DecidableEq, Fintype

private def acceptGuard : SourceGuard simpleExpr [] Player.alice 0 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

/-- A straight-line commit–reveal program with an executable conditional bonus. -/
def program (bonus : Int) : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 .alice (by decide) acceptGuard <|
  .reveal 1 .alice 0 (by decide) .here (by decide) <|
  .ret [(.alice, .ite (.getResultD (.var 1 .here) (.constBool false))
    (.constInt bonus) (.constInt 0))]

def initial : State (Player := Player) simpleExpr [] := Env.empty (CellVal simpleExpr)

/-- The empty initial state is sampled with probability one. -/
def setup (bonus : Int) : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by simp
  initialLaw := PMF.pure initial
  obligations := ∅
  program := program bonus
  accounts := rfl
  exitTransfers := fun _ => 0

instance (bonus : Int) : (setup bonus).FiniteInitialLaw where
  support_finite := by
    change (PMF.pure initial).support.Finite
    rw [PMF.support_pure]
    exact Set.finite_singleton initial

theorem finiteBindingTypes (bonus : Int) : (program bonus).FiniteBindingTypes := by
  change Finite Bool ∧ True
  exact ⟨inferInstance, trivial⟩

def policy (bonus : Int) (choice : Bool) : BehavioralPolicy Player.alice (program bonus) :=
  (fun _ _ _ => PMF.pure (some (.success choice)),
    (fun _ _ _ => PMF.pure true, PUnit.unit))

def profile (bonus : Int) (choice : Bool) : BehavioralProfile (program bonus)
  | .alice => policy bonus choice

def final (bonus : Int) (choice : Bool) : Config Player simpleExpr (program bonus).terminalCtx :=
  revealSuccessor 1 .here
    (commitSuccessor 0 acceptGuard (Config.initial initial) (some (.success choice))) true

def result (bonus : Int) (choice : Bool) : PublicOutcome (program bonus) :=
  ⟨Env.cons (.success choice) (Env.empty simpleExpr.Val), ⟨[none, none]⟩⟩

/-- The player's valuation charges one unit for publishing true. -/
def valuation (bonus : Int) (outcome : PublicOutcome (program bonus)) (_who : Player) : ℝ :=
  match (outcome.values.get .here : PublicationResult Bool) with
  | .success true => -1
  | _ => 0

/-- The strategic game evaluates the source program's own monetary instructions. -/
def game (bonus : Int) : UtilityGame Player where
  form := (program bonus).gameForm initial
  utility := (program bonus).paymentUtility (valuation bonus)

theorem setup_gameForm (bonus : Int) : (setup bonus).gameForm = (game bonus).form := by
  unfold Setup.gameForm Setup.publicRun Setup.run setup game
  simp only [PMF.pure_bind]
  rfl

/-- Every public outcome, including failed publication, has its utility fixed
by the same conditional payment instruction. -/
theorem utility_eq (bonus : Int) (outcome : PublicOutcome (program bonus)) :
    (game bonus).utility outcome .alice =
      match (outcome.values.get .here : PublicationResult Bool) with
      | .success true => (bonus : ℝ) - 1
      | _ => 0 := by
  have payments : (program bonus).publicPayoffs outcome =
      [(.alice, if (outcome.values.get .here : PublicationResult Bool).getD false
        then bonus else 0)] :=
    rfl
  change valuation bonus outcome .alice +
    (transferAmount ((program bonus).publicPayoffs outcome) .alice : ℝ) = _
  rw [payments]
  cases published : (outcome.values.get .here : PublicationResult Bool) with
  | failure => simp [valuation, published, PublicationResult.getD, transferAmount]
  | success choice =>
      cases choice <;> simp [valuation, published, PublicationResult.getD, transferAmount]
      ring

theorem utility_abs_le (bonus : Int) (outcome : PublicOutcome (program bonus)) :
    |(game bonus).utility outcome .alice| ≤ |(bonus : ℝ) - 1| := by
  rw [utility_eq]
  cases (outcome.values.get .here : PublicationResult Bool) with
  | failure => simp
  | success choice => cases choice <;> simp

/-- The bound quantifies over arbitrary outcome laws, so it also covers all
randomized policies, failed binding attempts, and withheld reveals. -/
theorem expectedUtility_le (bonus : Int) (law : PMF (PublicOutcome (program bonus))) :
    expectedUtility (game bonus).utility .alice law ≤ max ((bonus : ℝ) - 1) 0 := by
  apply expect_le_const law _ (payoffIntegrable_of_bounded law _ (utility_abs_le bonus))
  intro outcome _
  rw [utility_eq]
  cases (outcome.values.get .here : PublicationResult Bool) with
  | failure => exact le_max_right _ _
  | success choice =>
      cases choice
      · exact le_max_right _ _
      · exact le_max_left _ _

theorem hasIntegrableDeviations (bonus : Int) (choice : Bool) :
    (game bonus).form.HasIntegrableDeviations (game bonus).utility (profile bonus choice) := by
  intro who replacement
  cases who
  exact payoffIntegrable_of_bounded _ _ (utility_abs_le bonus)

theorem run_profile (bonus : Int) (choice : Bool) :
    (program bonus).run (profile bonus choice) initial = PMF.pure (final bonus choice) := by
  simp only [SourceProgram.run, program, profile, policy, runFrom, commitKernel, revealKernel,
    afterCommit, Config.initial_defaulted, Finset.notMem_empty, ↓reduceDIte, PMF.pure_bind]
  rw [dite_eq_right (by
    change Player.alice ∉ (∅ : Finset Player)
    exact Finset.notMem_empty _), PMF.pure_bind]
  rfl

theorem play_profile (bonus : Int) (choice : Bool) :
    (game bonus).form.play (profile bonus choice) = PMF.pure (result bonus choice) := by
  change ((program bonus).run (profile bonus choice) initial).map (publicOutcome _) = _
  rw [run_profile, PMF.pure_map]
  rfl

theorem evaluatePayoffs_final (bonus : Int) (choice : Bool) :
    (program bonus).evaluatePayoffs (final bonus choice).state =
      [(.alice, if choice then bonus else 0)] := by
  cases choice <;> rfl

/-- The utility comes from the evaluated instruction, not an independent payoff table. -/
theorem expectedUtility_profile (bonus : Int) (choice : Bool) :
    expectedUtility (game bonus).utility .alice ((game bonus).form.play (profile bonus choice)) =
      if choice then (bonus : ℝ) - 1 else 0 := by
  rw [play_profile, expectedUtility_pure]
  have publicResult : (program bonus).publicOutcome (final bonus choice) =
      result bonus choice := rfl
  have payments := publicPayoffs_publicOutcome (program bonus) (final bonus choice)
  rw [publicResult, evaluatePayoffs_final] at payments
  change valuation bonus (result bonus choice) .alice +
    (transferAmount ((program bonus).publicPayoffs (result bonus choice)) .alice : ℝ) = _
  rw [payments]
  cases choice <;> simp [valuation, result, Env.get, Env.cons, transferAmount]
  ring

theorem update_profile (bonus : Int) (before after : Bool) :
    Profile.update (sig := (game bonus).form.sig) (profile bonus before) Player.alice
        (policy bonus after) = profile bonus after := by
  funext who
  cases who
  simp [Profile.update, profile]

/-- A payment of two makes choosing true a strictly profitable unilateral deviation. -/
theorem bonus_profitable_deviation :
    expectedUtility (game 2).utility .alice ((game 2).form.play (profile 2 false)) <
      expectedUtility (game 2).utility .alice
        ((game 2).form.play (Profile.update (profile 2 false) .alice (policy 2 true))) := by
  rw [update_profile, expectedUtility_profile, expectedUtility_profile]
  norm_num

/-- Changing only the program bonus reverses the strict preference. -/
theorem payment_reverses_incentive :
    expectedUtility (game 2).utility .alice ((game 2).form.play (profile 2 false)) <
        expectedUtility (game 2).utility .alice ((game 2).form.play (profile 2 true)) ∧
      expectedUtility (game 0).utility .alice ((game 0).form.play (profile 0 true)) <
        expectedUtility (game 0).utility .alice ((game 0).form.play (profile 0 false)) := by
  simp only [expectedUtility_profile]
  norm_num

/-- Paying two makes publishing true optimal against every legal whole-policy
deviation, including randomized binding failures and publication withholding. -/
theorem bonus_true_isNash :
    IsNash (game 2).form (euPreference (game 2).utility) (profile 2 true) := by
  rw [(hasIntegrableDeviations 2 true).isNash_iff]
  intro who replacement
  cases who
  rw [expectedUtility_profile]
  simpa using expectedUtility_le 2
    ((game 2).form.play (Profile.update (profile 2 true) .alice replacement))

/-- Without a bonus, publishing false is optimal against the same full policy
space. Failure or withholding may tie it but cannot improve its utility. -/
theorem zero_false_isNash :
    IsNash (game 0).form (euPreference (game 0).utility) (profile 0 false) := by
  rw [(hasIntegrableDeviations 0 false).isNash_iff]
  intro who replacement
  cases who
  rw [expectedUtility_profile]
  simpa using expectedUtility_le 0
    ((game 0).form.play (Profile.update (profile 0 false) .alice replacement))

theorem bonus_false_not_isNash :
    ¬ IsNash (game 2).form (euPreference (game 2).utility) (profile 2 false) := by
  intro equilibrium
  have bound := (hasIntegrableDeviations 2 false).isNash_iff.mp equilibrium
    .alice (policy 2 true)
  exact (not_lt_of_ge bound) bonus_profitable_deviation

theorem zero_true_not_isNash :
    ¬ IsNash (game 0).form (euPreference (game 0).utility) (profile 0 true) := by
  intro equilibrium
  have bound := (hasIntegrableDeviations 0 true).isNash_iff.mp equilibrium
    .alice (policy 0 false)
  rw [update_profile, expectedUtility_profile, expectedUtility_profile] at bound
  norm_num at bound

/-- The ideal compiled game values the decoded publication and the actual
compiled payment instructions under an arbitrary public scheduler. -/
def compiledGame (bonus : Int) (scheduler : (setup bonus).eventGraph.PublicScheduler) :
    UtilityGame Player where
  form := (setup bonus).eventGame scheduler
  utility outcome who := valuation bonus ((setup bonus).eventPublicOutcome outcome) who +
    (transferAmount (terminalPayouts (program bonus) outcome) who : ℝ)

/-- Compilation preserves and reflects full-policy Nash for this concrete
payment game; compiled deviations are not restricted to compiled source policies. -/
theorem compiled_isNash_iff (bonus : Int)
    (scheduler : (setup bonus).eventGraph.PublicScheduler)
    (sourceProfile : BehavioralProfile (program bonus)) :
    IsNash (compiledGame bonus scheduler).form
        (euPreference (compiledGame bonus scheduler).utility)
        (compileEventProfile (program bonus) sourceProfile) ↔
      IsNash (game bonus).form (euPreference (game bonus).utility) sourceProfile := by
  have correspondence := (setup bonus).eventGame_payment_approximate_nash_iff
    (finiteBindingTypes bonus) scheduler (valuation bonus) 0 sourceProfile
  rw [← isNash_iff_isεNash_zero, ← isNash_iff_isεNash_zero] at correspondence
  rw [isNash_iff, isNash_iff] at correspondence ⊢
  simpa only [compiledGame, game, Setup.gameForm, Setup.publicRun, Setup.run, setup,
    SourceProgram.gameForm, PMF.pure_bind] using correspondence

theorem compiled_bonus_true_isNash (scheduler : (setup 2).eventGraph.PublicScheduler) :
    IsNash (compiledGame 2 scheduler).form
      (euPreference (compiledGame 2 scheduler).utility)
      (compileEventProfile (program 2) (profile 2 true)) :=
  (compiled_isNash_iff 2 scheduler _).mpr bonus_true_isNash

theorem compiled_zero_false_isNash (scheduler : (setup 0).eventGraph.PublicScheduler) :
    IsNash (compiledGame 0 scheduler).form
      (euPreference (compiledGame 0 scheduler).utility)
      (compileEventProfile (program 0) (profile 0 false)) :=
  (compiled_isNash_iff 0 scheduler _).mpr zero_false_isNash

theorem compiled_bonus_false_not_isNash (scheduler : (setup 2).eventGraph.PublicScheduler) :
    ¬ IsNash (compiledGame 2 scheduler).form
      (euPreference (compiledGame 2 scheduler).utility)
      (compileEventProfile (program 2) (profile 2 false)) :=
  fun equilibrium => bonus_false_not_isNash ((compiled_isNash_iff 2 scheduler _).mp equilibrium)

theorem compiled_zero_true_not_isNash (scheduler : (setup 0).eventGraph.PublicScheduler) :
    ¬ IsNash (compiledGame 0 scheduler).form
      (euPreference (compiledGame 0 scheduler).utility)
      (compileEventProfile (program 0) (profile 0 true)) :=
  fun equilibrium => zero_true_not_isNash ((compiled_isNash_iff 0 scheduler _).mp equilibrium)

/-- The same program-derived transfer is settled by an arbitrary terminal
audit; expected utility subtracts its actual marginal collection charge. -/
theorem audited_expectedUtility {Observation : Type} (bonus : Int) (choice : Bool)
    (observe : PublicOutcome (program bonus) → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ) :
    expect (Enforcement.TerminalAudit.settlement (program bonus).publicTransfers
        observe audit deposit (result bonus choice))
        (fun receipts => monetaryUtility (valuation bonus) (result bonus choice, receipts) .alice) =
      (if choice then (bonus : ℝ) - 1 else 0) -
        Enforcement.TerminalAudit.charge observe audit (result bonus choice) .alice *
          deposit .alice := by
  have integrated := Enforcement.TerminalAudit.settlement_expect_monetaryUtility
    (valuation bonus) (program bonus).publicTransfers observe audit deposit (result bonus choice)
      Player.alice
  have base := expectedUtility_profile bonus choice
  rw [play_profile, expectedUtility_pure] at base
  change valuation bonus (result bonus choice) .alice +
    (program bonus).publicTransfers (result bonus choice) .alice = _ at base
  simpa only [Enforcement.TerminalAudit.utility, base] using integrated

/-- The actual compiled payment list has the program-selected bonus law. -/
theorem compiled_payout_law (bonus : Int) (choice : Bool) :
    ((toEventGraph (program bonus)).terminalOutcomes
        (toEventGraph (program bonus)).canonicalScheduler
        (compileEventProfile (program bonus) (profile bonus choice)) (encodeInputs initial)).map
        (terminalPayouts (program bonus)) = PMF.pure [(.alice, if choice then bonus else 0)] := by
  rw [Vegas.canonical_payout_law, run_profile, PMF.pure_map, evaluatePayoffs_final]

/-- The compiled monetary receipts agree with the transfer read by strategic utility. -/
theorem compiled_transfer_law (bonus : Int) (choice : Bool) :
    ((toEventGraph (program bonus)).terminalOutcomes
        (toEventGraph (program bonus)).canonicalScheduler
        (compileEventProfile (program bonus) (profile bonus choice)) (encodeInputs initial)).map
        (fun terminal who => (transferAmount (terminalPayouts (program bonus) terminal) who : ℝ)) =
      PMF.pure ((program bonus).publicTransfers (result bonus choice)) := by
  rw [SourceProgram.canonical_transfer_law, run_profile, PMF.pure_map]
  rfl

end Vegas.Examples.ProgramPayments
