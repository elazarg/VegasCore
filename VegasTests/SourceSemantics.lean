/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Source.Semantics
import Vegas.Expr.Simple

/-! Mixed fixtures and execution regressions for the source language.

The program deliberately uses every source constructor and begins with both
public and private initial data. It supplies heterogeneous, guarded, sampled,
and forced-failure programs to compiler and runtime tests.
-/

namespace VegasTests.SourceSemantics

open GameTheory GameTheory.Math.Probability Vegas

noncomputable section

inductive Player where
  | alice
  deriving DecidableEq

private abbrev flag : VarId := 10
private abbrev seed : VarId := 11
private abbrev choice : VarId := 12
private abbrev choiceOut : VarId := 13
private abbrev seedOut : VarId := 14
private abbrev coin : VarId := 15

private abbrev InitialCtx : SourceCtx Player simpleExpr :=
  [(seed, .privateData .alice .bool), (flag, .publicData .bool)]

/-- `choice` is checked against an earlier public flag and Alice's retained
private seed. The guard is checked when the last of its inputs is revealed. -/
private def choiceGuard :
    SourceGuard simpleExpr InitialCtx .alice choice (.option .bool) where
  schema := [(flag, .bool), (seed, .bool)]
  schemaNames := by decide
  subjectFresh := by decide
  code :=
    .ite
      (.var flag (.there .here))
      (.eq (.var choice .here) .none)
      (.eq (.var choice .here) (.some (.var seed (.there (.there .here)))))
  reads := fun h => match h with
    | .here => .publicData (.there .here)
    | .there .here => .privateData .here

private abbrev AfterRevealsPublicCtx : CtxSimple :=
  [(seedOut, .result .bool), (choiceOut, .result (.option .bool)), (flag, .bool)]

private def choiceResult :
    Expr AfterRevealsPublicCtx (.result (.option .bool)) :=
  .var choiceOut (.there .here)

private def fairBool : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

/-- Total dependent chance: failure, successful `none`, and successful
`some b` all select an ordinary Boolean law. -/
private def dependentCoin : DistExpr AfterRevealsPublicCtx .bool :=
  .ite (.isFailure choiceResult)
    (.weighted (.pure false))
    (.ite (.isNone (.getResultD choiceResult .none))
      (.weighted fairBool)
      (.ite (.getD (.getResultD choiceResult .none) (.constBool false))
        (.weighted (.pure true)) (.weighted (.pure false))))

private abbrev TerminalPublicCtx : CtxSimple :=
  [(coin, .bool), (seedOut, .result .bool),
    (choiceOut, .result (.option .bool)), (flag, .bool)]

/-- Failure-sensitive settlement explicitly inspects both publication results.
No failed result is coerced to an ordinary payload or winning comparison. -/
private def payoff : Expr TerminalPublicCtx .int :=
  .ite
    (.isFailure (.var choiceOut (.there (.there .here))))
    (.constInt (-10))
    (.ite
      (.isFailure (.var seedOut (.there .here)))
      (.constInt (-5))
      (.constInt 10))

/-- Reverse disclosure is intentional: `choiceOut` becomes public before the
guard's input `seed`, so the guard is checked later, at the reveal of `seed`. -/
def mixedProgram : SourceProgram Player simpleExpr InitialCtx {seed} :=
  .commit choice .alice (by decide) choiceGuard <|
  .reveal choiceOut .alice choice (by decide) .here (by decide) <|
  .reveal seedOut .alice seed (by decide) (.there (.there .here)) (by decide) <|
  .sample coin (by decide) dependentCoin <|
  .ret [(.alice, payoff)]

private def initialState : State simpleExpr InitialCtx :=
  Env.cons (x := seed) (.success true) <|
    Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private abbrev ChoiceCtx : SourceCtx Player simpleExpr :=
  (choice, .privateData .alice (.option .bool)) :: InitialCtx

private abbrev ChoiceOutCtx : SourceCtx Player simpleExpr :=
  (choiceOut, .publication (.option .bool)) :: ChoiceCtx

private def choiceObligation : SourceProgram.Registry ChoiceCtx :=
  [{ owner := .alice, subject := choice, payload := .option .bool, source := .here,
     guard := choiceGuard.weaken }]

private def afterCommit : Revelations ChoiceCtx :=
  Revelations.weaken (Revelations.initial InitialCtx)

private def choiceRevealed : Revelations ChoiceOutCtx :=
  Revelations.reveal (published := choiceOut) afterCommit .here

/-- Revealing `choice` completes no check: its guard also reads `seed`. -/
example : (choiceObligation.completedBy (published := choiceOut) afterCommit .here).length = 0 := by
  rfl

/-- Revealing `seed` completes the check of the guard on `choice`. -/
example : (choiceObligation.weaken.completedBy (published := seedOut) choiceRevealed
    (.there (.there .here))).length = 1 := by
  rfl

/-- Evaluate the guard on `choice` at the reveal of `seed`. -/
private def acceptsAtSeed (published : PublicationResult (Option Bool))
    (proposal : PublicationResult Bool) : Bool :=
  (choiceObligation.weaken.completedBy (published := seedOut) choiceRevealed
    (.there (.there .here))).all fun obligation =>
      obligation.accepts (choiceRevealed.reveal (published := seedOut) (.there (.there .here)))
        (Env.cons (x := seedOut) (τ := .publication .bool) proposal <|
          Env.cons (x := choiceOut) (τ := .publication (.option .bool)) published <|
          Env.cons (x := choice) (τ := .privateData .alice (.option .bool))
            (PublicationResult.success Option.none) initialState)

example : acceptsAtSeed (.success Option.none) (.success true) = true := by decide
example : acceptsAtSeed (.success (some false)) (.success true) = false := by decide
/-- A failed subject publication or a failed input discharges the guard. -/
example : acceptsAtSeed .failure (.success true) = true := by decide
example : acceptsAtSeed (.success (some false)) .failure = true := by decide

def mixedInitial : SourceProgram.Initial (Player := Player) (L := simpleExpr) where
  context := InitialCtx
  namesNodup := by decide
  state := initialState
  obligations := {seed}
  program := mixedProgram
  accounts := rfl

private abbrev doomed : VarId := 20
private abbrev doomedOut : VarId := 21

private def falseGuard :
    SourceGuard (Player := Player) simpleExpr [] Player.alice doomed .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool false
  reads := fun h => nomatch h

example : ∀ state : State simpleExpr [],
    falseGuard.accepts (.success true) (Revelations.initial []) state = false := by
  intro state
  rfl

/-- A failed subject discharges even constant-false code. -/
example : ∀ state : State simpleExpr [],
    falseGuard.accepts .failure (Revelations.initial []) state = true := by
  intro state
  rfl

/-- Structurally valid despite having no all-ordinary successful opening. -/
def falseGuardProgram : SourceProgram Player simpleExpr [] ∅ :=
  .commit doomed .alice (by decide) falseGuard <|
  .reveal doomedOut .alice doomed (by decide) .here (by decide) <|
  .ret
    [(.alice,
      .ite (.isFailure (.var doomedOut .here))
        (.constInt (-1)) (.constInt 1))]

private def mixedProfile (bound : PublicationResult (Option Bool))
    (discloseChoice : Bool) : mixedProgram.BehavioralProfile :=
  fun
    | .alice =>
      (fun _ _ => FinDist.pure bound,
        (fun _ _ => FinDist.pure discloseChoice,
          (fun _ _ => FinDist.pure true, PUnit.unit)))

private def successfulState (sample : Bool) : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) sample <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.success Option.none) <|
  Env.cons (x := choice) (PublicationResult.success Option.none) <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private def invalidState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.failure) <|
  Env.cons (x := choiceOut) (PublicationResult.success (some false)) <|
  Env.cons (x := choice) (PublicationResult.success (some false)) <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private def unopenableState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.failure) <|
  Env.cons (x := choice) PublicationResult.failure <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private def withheldState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.failure) <|
  Env.cons (x := choice) (PublicationResult.success Option.none) <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

@[simp] private theorem point_law (value : Bool) :
    (RationalLaw.pure value).denote = FinDist.pure value := by
  apply FinDist.ext_of_prob
  intro other
  simp [RationalLaw.prob_denote, RationalLaw.pure, FinDist.prob_pure_eq_ite]

macro "solve_mixed_run" : tactic =>
  `(tactic|
    simp only [SourceProgram.run, mixedProgram, mixedProfile, SourceProgram.runWith,
      SourceProgram.commitKernel, SourceProgram.revealKernel,
      SourceProgram.afterCommit, SourceProgram.afterReveal,
      FinDist.pure_bind, FinDist.map_eq_bind])

private theorem successful_run :
    mixedProgram.run (mixedProfile (.success Option.none) true) initialState =
      fairBool.denote.map successfulState := by
  solve_mixed_run
  rfl

private theorem invalid_run :
    mixedProgram.run (mixedProfile (.success (some false)) true) initialState =
      FinDist.pure invalidState := by
  solve_mixed_run
  change (RationalLaw.pure false).denote.bind _ = _
  rw [point_law, FinDist.pure_bind]
  rfl

private theorem unopenable_run :
    mixedProgram.run (mixedProfile .failure true) initialState =
      FinDist.pure unopenableState := by
  solve_mixed_run
  change (RationalLaw.pure false).denote.bind _ = _
  rw [point_law, FinDist.pure_bind]
  rfl

private theorem withholding_run :
    mixedProgram.run (mixedProfile (.success Option.none) false) initialState =
      FinDist.pure withheldState := by
  solve_mixed_run
  change (RationalLaw.pure false).denote.bind _ = _
  rw [point_law, FinDist.pure_bind]
  rfl

example (value : Bool) :
    ((mixedProgram.run (mixedProfile (.success Option.none) true) initialState).map
      (fun state => state.get .here)).prob value = 1 / 2 := by
  rw [successful_run, FinDist.map_comp]
  change (fairBool.denote.map id).prob value = _
  rw [FinDist.map_id]
  rw [RationalLaw.prob_denote]
  change (∑ index : Fin 2, if value = (fairBool.entries.get index).1 then
    ((fairBool.entries.get index).2 : ℝ) else 0) = _
  rw [Fin.sum_univ_two]
  cases value <;> norm_num [fairBool]

example :
    (mixedProgram.run (mixedProfile (.success Option.none) true) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, 10)] := by
  rw [successful_run, FinDist.map_comp]
  change fairBool.denote.map (fun _ => ([(Player.alice, 10)] : List (Player × Int))) = _
  exact FinDist.map_const _ _

example :
    (mixedProgram.run (mixedProfile (.success (some false)) true) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, -5)] := by
  rw [invalid_run, FinDist.map_pure]
  rfl

example :
    (mixedProgram.run (mixedProfile .failure true) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, -10)] := by
  rw [unopenable_run, FinDist.map_pure]
  rfl

example :
    (mixedProgram.run (mixedProfile (.success Option.none) false) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, -10)] := by
  rw [withholding_run, FinDist.map_pure]
  rfl

private def falseProfile : falseGuardProgram.BehavioralProfile :=
  fun
    | .alice =>
      (fun _ _ => FinDist.pure (.success true),
        (fun _ _ => FinDist.pure true, PUnit.unit))

private def falseGuardState : State simpleExpr (falseGuardProgram.terminalCtx) :=
  Env.cons (x := doomedOut) PublicationResult.failure <|
  Env.cons (x := doomed) (PublicationResult.success true) <|
  Env.empty (CellVal simpleExpr)

private theorem false_guard_run : falseGuardProgram.run falseProfile
    (Env.empty (CellVal simpleExpr)) = FinDist.pure falseGuardState := by
  unfold SourceProgram.run falseGuardProgram
  rw [SourceProgram.runWith]
  dsimp only [SourceProgram.commitKernel, falseProfile]
  rw [FinDist.pure_bind]
  rw [SourceProgram.runWith]
  dsimp only [SourceProgram.revealKernel, SourceProgram.afterCommit, falseProfile]
  rw [FinDist.pure_bind]
  rfl

example : (falseGuardProgram.run falseProfile (Env.empty (CellVal simpleExpr))).map
    falseGuardProgram.evaluatePayoffs = FinDist.pure [(.alice, -1)] := by
  rw [false_guard_run, FinDist.map_pure]
  rfl

end

end VegasTests.SourceSemantics
