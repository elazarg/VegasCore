/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.RevealService
import Vegas.Game.SequentialRuntimePhases
import Vegas.Game.OnePacketPublicInitialSignal
import Vegas.Game.OnePacketSwapFiberSum
import Vegas.Game.ProgramPayoffs

/-! # Two-player Odds–Evens with executable settlement -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol GameTheory.Math.Probability

abbrev Player := Bool
abbrev even : Player := false
abbrev odd : Player := true

def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun cell => nomatch cell

def cash (re ro : PublicationResult Bool) (who : Player) : Int :=
  match re, ro with
  | .failure, .failure => 0
  | .failure, .success _ => if who = odd then 200 else 0
  | .success _, .failure => if who = even then 200 else 0
  | .success e, .success o => if (e = o) = (who = even) then 126 else 74

def cashExpr {Γ : CtxSimple} (who : Player)
    (re ro : Expr Γ (.result .bool)) : Expr Γ .int :=
  .ite (.isFailure re)
    (.ite (.isFailure ro) (.constInt 0) (.constInt (if who = odd then 200 else 0)))
    (.ite (.isFailure ro) (.constInt (if who = even then 200 else 0))
      (.ite (.eq (.eq (.getResultD re (.constBool false))
        (.getResultD ro (.constBool false))) (.constBool (decide (who = even))))
        (.constInt 126) (.constInt 74)))

def program : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 even (by decide) (acceptGuard even 0) <|
  .commit 1 odd (by decide) (acceptGuard odd 1) <|
  .reveal 2 even 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 odd 1 (by decide) (.there .here) (by decide) <|
  .ret [(even, cashExpr even (.var 2 (.there .here)) (.var 3 .here)),
    (odd, cashExpr odd (.var 2 (.there .here)) (.var 3 .here))]

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := PMF.pure (Env.empty (CellVal simpleExpr))
  obligations := ∅
  program := program
  accounts := rfl
  exitTransfers := fun _ => 0

abbrev compiled := graph setup
abbrev plan := sequentialRuntimePhasePlan program

def sourceUtility (result : Unit × PublicOutcome program) (who : Player) : ℝ :=
  cash (result.2.get (.there .here)) (result.2.get .here) who

theorem cash_success (e o : Bool) :
    cash (.success e) (.success o) even = (if e = o then 126 else 74) ∧
      cash (.success e) (.success o) odd = (if e = o then 74 else 126) := by
  cases e <;> cases o <;> decide

theorem cash_failure (bit : Bool) :
    (cash .failure (.success bit) even, cash .failure (.success bit) odd) = (0, 200) ∧
      (cash (.success bit) .failure even, cash (.success bit) .failure odd) = (200, 0) ∧
        (cash .failure .failure even, cash .failure .failure odd) = (0, 0) := by
  cases bit <;> decide

theorem successful_pot (e o : Bool) :
    cash (.success e) (.success o) even + cash (.success e) (.success o) odd = 200 := by
  cases e <;> cases o <;> decide

theorem sourceUtility_bounds (result : Unit × PublicOutcome program) (who : Player) :
    0 ≤ sourceUtility result who ∧ sourceUtility result who ≤ 200 := by
  unfold sourceUtility cash
  split <;> (try split_ifs) <;> norm_num

theorem eval_cashExpr {Γ : CtxSimple} (who : Player)
    (re ro : Expr Γ (.result .bool)) (env : PlainEnv Γ) :
    evalExpr (cashExpr who re ro) env = cash (evalExpr re env) (evalExpr ro env) who := by
  cases who <;> cases he : evalExpr re env <;> cases ho : evalExpr ro env <;>
    simp [cashExpr, cash, evalExpr, he, ho, even, odd,
      PublicationResult.isFailure, PublicationResult.getD]

theorem publicPayoffs_eq (outcome : PublicOutcome program) :
    program.publicPayoffs outcome =
      [(even, cash (outcome.get (.there .here)) (outcome.get .here) even),
        (odd, cash (outcome.get (.there .here)) (outcome.get .here) odd)] := by
  change [(even, evalExpr _ outcome), (odd, evalExpr _ outcome)] = _
  rw [eval_cashExpr, eval_cashExpr]
  rfl

theorem sourceUtility_eq_programTransfer (result : Unit × PublicOutcome program)
    (who : Player) : sourceUtility result who = program.publicTransfers result.2 who := by
  unfold SourceProgram.publicTransfers
  rw [publicPayoffs_eq]
  cases who <;> simp [transferAmount, even, odd, sourceUtility]

instance : setup.FiniteInitialLaw where
  support_finite := by change (PMF.pure _).support.Finite; simp

theorem finiteBindingTypes : program.FiniteBindingTypes :=
  ⟨inferInstance, inferInstance, trivial⟩

instance : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes

theorem wellFormed : setup.WellFormed where
  initialValues := by intro initial _ name actor payload cell; cases cell
  guardsSatisfiable := by
    intro initial _
    exact ⟨⟨false, rfl⟩, fun _ _ => ⟨⟨false, rfl⟩, fun _ _ => trivial⟩⟩

def signal (_state : State simpleExpr setup.context) : Unit := ()

private theorem empty_state_eq (first second : State simpleExpr setup.context) :
    first = second := by
  funext name kind cell
  cases cell

theorem independent : setup.PrivateInputsIndependentGiven signal := by
  intro who first second _
  rw [empty_state_eq (splice who first second) first,
    empty_state_eq (splice who second first) second]

theorem observable : setup.PublicInitialSignal signal := by intro _ _ _; rfl

def bounds : MessageBounds compiled where
  candidateCount := 2
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

theorem outputValues : bounds.CoversOutputValues := by
  intro requested
  fin_cases requested <;>
    intro bit <;> exact Finset.mem_image.mpr ⟨bit, Finset.mem_univ _, rfl⟩

theorem inputValues : bounds.CoversInputValues := by
  intro input
  change Fin 0 at input
  exact Fin.elim0 input

theorem candidateCapacity : ∀ who, bindingEventCount compiled who < bounds.candidateCount := by
  intro who
  cases who <;> decide

end Vegas.Examples.OddsEvens
