/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.ProgramPayoffs

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
  deriving DecidableEq

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

def policy (bonus : Int) (choice : Bool) : BehavioralPolicy Player.alice (program bonus) :=
  (fun _ _ => PMF.pure (.success choice), (fun _ _ => PMF.pure true, PUnit.unit))

def profile (bonus : Int) (choice : Bool) : BehavioralProfile (program bonus)
  | .alice => policy bonus choice

def final (bonus : Int) (choice : Bool) : State simpleExpr (program bonus).terminalCtx :=
  Env.cons (.success choice) (Env.cons (.success choice) (Env.empty (CellVal simpleExpr)))

def result (bonus : Int) (choice : Bool) : PublicOutcome (program bonus) :=
  Env.cons (.success choice) (Env.empty simpleExpr.Val)

/-- The player's valuation charges one unit for publishing true. -/
def valuation (bonus : Int) (outcome : PublicOutcome (program bonus)) (_who : Player) : ℝ :=
  match (outcome.get .here : PublicationResult Bool) with
  | .success true => -1
  | _ => 0

/-- The strategic game evaluates the source program's own monetary instructions. -/
def game (bonus : Int) : UtilityGame Player where
  form := (program bonus).gameForm initial
  utility := (program bonus).paymentUtility (valuation bonus)

theorem run_profile (bonus : Int) (choice : Bool) :
    (program bonus).run (profile bonus choice) initial = PMF.pure (final bonus choice) := by
  simp only [SourceProgram.run, program, profile, policy, runWith, commitKernel, revealKernel,
    afterCommit, PMF.pure_bind]
  rfl

theorem play_profile (bonus : Int) (choice : Bool) :
    (game bonus).form.play (profile bonus choice) = PMF.pure (result bonus choice) := by
  change ((program bonus).run (profile bonus choice) initial).map (publicOutcome _) = _
  rw [run_profile, PMF.pure_map]
  rfl

theorem evaluatePayoffs_final (bonus : Int) (choice : Bool) :
    (program bonus).evaluatePayoffs (final bonus choice) =
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
