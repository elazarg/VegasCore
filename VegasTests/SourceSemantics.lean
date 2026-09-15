/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Source.Semantics
import Vegas.Core.ExprSimple

/-! Mixed examples for the revised source language.

The program deliberately uses every source constructor and begins with both
public and private initial data. Its execution tests cover ordinary success,
invalid and unopenable bindings, withholding, and forced failure.
-/

namespace VegasTests.SourceSemantics

open GameTheory GameTheory.Math.Probability Interaction Vegas

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
private seed. The guard can be decided only after the seed is published. -/
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

/-- Reverse disclosure is intentional: `choiceOut` becomes public while its
guard still waits for `seedOut`; the retained obligation is closed later. -/
def mixedProgram : SourceProgram Player simpleExpr InitialCtx {seed} :=
  .commit choice .alice (by decide) choiceGuard <|
  .reveal choiceOut .alice choice (by decide) .here (by decide) <|
  .reveal seedOut .alice seed (by decide) (.there (.there .here)) (by decide) <|
  .sample coin (by decide) dependentCoin <|
  .ret [(.alice, payoff)]

private def initialState : State simpleExpr InitialCtx :=
  Env.cons (x := seed) (BoundValue.value true, .pending) <|
    Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

@[simp] private theorem choice_none_waits :
    choiceGuard.check (.value none)
      (Env.cons (x := seed) (BoundValue.value true, .pending) <|
        Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))) = .pending := by
  decide

@[simp] private theorem choice_some_waits :
    choiceGuard.check (.value (some false))
      (Env.cons (x := seed) (BoundValue.value true, .pending) <|
        Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))) = .pending := by
  decide

@[simp] private theorem choice_none_closes :
    choiceGuard.check (.value none)
      (Env.cons (x := seed) (BoundValue.value true, .value true) <|
        Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))) = .satisfied := by
  decide

@[simp] private theorem choice_some_rejects :
    choiceGuard.check (.value (some false))
      (Env.cons (x := seed) (BoundValue.value true, .value true) <|
        Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))) = .rejected := by
  decide

def mixedInitial : SourceProgram.Initial (Player := Player) (L := simpleExpr) where
  context := InitialCtx
  namesNodup := by decide
  state := initialState
  privatePending := by
    simp [SourceProgram.PrivatePending, initialState, Env.get, Env.cons]
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

@[simp] private theorem false_guard_rejects :
    ∀ state : State simpleExpr [], falseGuard.check (.value true) state = .rejected := by
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

private def mixedProfile (bound : BoundValue (Option Bool))
    (discloseChoice : Bool) : mixedProgram.BehavioralProfile :=
  fun
    | .alice =>
      (fun _ _ => FinDist.pure bound,
        (fun _ _ => FinDist.pure discloseChoice,
          (fun _ _ => FinDist.pure true, PUnit.unit)))

@[simp] private theorem boundResult_here_value {Γ : SourceCtx Player simpleExpr}
    {name : VarId} {payload : BaseTy} (a : Val payload)
    (publication : Publication (Val payload)) (state : State simpleExpr Γ)
    (disclose : Bool) :
    SourceProgram.boundResult
      (Env.cons (x := name)
        (τ := CellTy.privateData Player.alice payload)
        (BoundValue.value a, publication) state)
      (.here : HasVar ((name, .privateData Player.alice payload) :: Γ) name
        (.privateData Player.alice payload)) disclose =
      if disclose then .success a else .failure := by
  cases disclose <;> rfl

@[simp] private theorem boundResult_here_unopenable {Γ : SourceCtx Player simpleExpr}
    {name : VarId} {payload : BaseTy}
    (publication : Publication (Val payload)) (state : State simpleExpr Γ)
    (disclose : Bool) :
    SourceProgram.boundResult
      (Env.cons (x := name)
        (τ := CellTy.privateData Player.alice payload)
        (BoundValue.unopenable _, publication) state)
      (.here : HasVar ((name, .privateData Player.alice payload) :: Γ) name
        (.privateData Player.alice payload)) disclose = .failure := by
  rfl

private def successfulState (sample : Bool) : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) sample <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.success Option.none) <|
  Env.cons (x := choice) (BoundValue.value Option.none, Publication.value Option.none) <|
  Env.cons (x := seed) (BoundValue.value true, Publication.value true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private def invalidState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.failure) <|
  Env.cons (x := choiceOut) (PublicationResult.success (some false)) <|
  Env.cons (x := choice) (BoundValue.value (some false), Publication.value (some false)) <|
  Env.cons (x := seed) (BoundValue.value true, Publication.failed) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private def unopenableState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.failure) <|
  Env.cons (x := choice) (BoundValue.unopenable _, Publication.failed) <|
  Env.cons (x := seed) (BoundValue.value true, Publication.value true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

private def withheldState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.failure) <|
  Env.cons (x := choice) (BoundValue.value Option.none, Publication.failed) <|
  Env.cons (x := seed) (BoundValue.value true, Publication.value true) <|
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
    mixedProgram.run (mixedProfile (BoundValue.value Option.none) true) initialState =
      fairBool.denote.map successfulState := by
  solve_mixed_run
  rfl

private theorem invalid_run :
    mixedProgram.run (mixedProfile (BoundValue.value (some false)) true) initialState =
      FinDist.pure invalidState := by
  solve_mixed_run
  change (RationalLaw.pure false).denote.bind _ = _
  rw [point_law, FinDist.pure_bind]
  rfl

private theorem unopenable_run :
    mixedProgram.run (mixedProfile (BoundValue.unopenable _) true) initialState =
      FinDist.pure unopenableState := by
  solve_mixed_run
  change (RationalLaw.pure false).denote.bind _ = _
  rw [point_law, FinDist.pure_bind]
  rfl

private theorem withholding_run :
    mixedProgram.run (mixedProfile (BoundValue.value Option.none) false) initialState =
      FinDist.pure withheldState := by
  solve_mixed_run
  change (RationalLaw.pure false).denote.bind _ = _
  rw [point_law, FinDist.pure_bind]
  rfl

example (value : Bool) :
    ((mixedProgram.run (mixedProfile (BoundValue.value Option.none) true) initialState).map
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
    (mixedProgram.run (mixedProfile (BoundValue.value Option.none) true) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, 10)] := by
  rw [successful_run, FinDist.map_comp]
  change fairBool.denote.map (fun _ => ([(Player.alice, 10)] : List (Player × Int))) = _
  exact FinDist.map_const _ _

example :
    (mixedProgram.run (mixedProfile (BoundValue.value (some false)) true) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, -5)] := by
  rw [invalid_run, FinDist.map_pure]
  rfl

example :
    (mixedProgram.run (mixedProfile (BoundValue.unopenable _) true) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, -10)] := by
  rw [unopenable_run, FinDist.map_pure]
  rfl

example :
    (mixedProgram.run (mixedProfile (BoundValue.value Option.none) false) initialState).map
      mixedProgram.evaluatePayoffs = FinDist.pure [(.alice, -10)] := by
  rw [withholding_run, FinDist.map_pure]
  rfl

private def falseProfile : falseGuardProgram.BehavioralProfile :=
  fun
    | .alice =>
      (fun _ _ => FinDist.pure (BoundValue.value true),
        (fun _ _ => FinDist.pure true, PUnit.unit))

private def falseGuardState : State simpleExpr (falseGuardProgram.terminalCtx) :=
  Env.cons (x := doomedOut) PublicationResult.failure <|
  Env.cons (x := doomed) (BoundValue.value true, Publication.failed) <|
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
