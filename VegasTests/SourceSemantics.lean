module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.Setup
public import Vegas.Expr.Simple
public import GameTheoryExtensions.Math.Probability.Support

@[expose] public section

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

abbrev flag : VarId := 10
abbrev seed : VarId := 11
abbrev choice : VarId := 12
abbrev choiceOut : VarId := 13
abbrev seedOut : VarId := 14
abbrev coin : VarId := 15

abbrev InitialCtx : SourceCtx Player simpleExpr :=
  [(seed, .commitment .alice .bool), (flag, .publicData .bool)]

/-- `choice` is checked against an earlier public flag and Alice's retained
private seed. The guard is checked when the last of its inputs is revealed. -/
def choiceGuard :
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
    | .there .here => .commitment .here

abbrev AfterRevealsPublicCtx : CtxSimple :=
  [(seedOut, .result .bool), (choiceOut, .result (.option .bool)), (flag, .bool)]

def choiceResult :
    Expr AfterRevealsPublicCtx (.result (.option .bool)) :=
  .var choiceOut (.there .here)

def fairBool : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

/-- Total dependent chance: failure, successful `none`, and successful
`some b` all select an ordinary Boolean law. -/
def dependentCoin : DistExpr AfterRevealsPublicCtx .bool :=
  .ite (.isFailure choiceResult)
    (.weighted (.pure false))
    (.ite (.isNone (.getResultD choiceResult .none))
      (.weighted fairBool)
      (.ite (.getD (.getResultD choiceResult .none) (.constBool false))
        (.weighted (.pure true)) (.weighted (.pure false))))

abbrev TerminalPublicCtx : CtxSimple :=
  [(coin, .bool), (seedOut, .result .bool),
    (choiceOut, .result (.option .bool)), (flag, .bool)]

/-- Failure-sensitive settlement explicitly inspects both publication results.
No failed result is coerced to an ordinary payload or winning comparison. -/
def payoff : Expr TerminalPublicCtx .int :=
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

def mixedState : State simpleExpr InitialCtx :=
  Env.cons (x := seed) (.success true) <|
    Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

abbrev ChoiceCtx : SourceCtx Player simpleExpr :=
  (choice, .commitment .alice (.option .bool)) :: InitialCtx

abbrev ChoiceOutCtx : SourceCtx Player simpleExpr :=
  (choiceOut, .publication (.option .bool)) :: ChoiceCtx

def choiceObligation : SourceProgram.Registry ChoiceCtx :=
  [{ owner := .alice, subject := choice, payload := .option .bool, source := .here,
     guard := choiceGuard.weaken }]

def afterCommit : Revelations ChoiceCtx :=
  Revelations.weaken (Revelations.initial InitialCtx)

def choiceRevealed : Revelations ChoiceOutCtx :=
  Revelations.reveal (published := choiceOut) afterCommit .here

/-- Revealing `choice` completes no check: its guard also reads `seed`. -/
example : (choiceObligation.completedBy (published := choiceOut) afterCommit .here).length = 0 := by
  rfl

/-- Revealing `seed` completes the check of the guard on `choice`. -/
example : (choiceObligation.weaken.completedBy (published := seedOut) choiceRevealed
    (.there (.there .here))).length = 1 := by
  rfl

/-- Evaluate the guard on `choice` at the reveal of `seed`. -/
def acceptsAtSeed (published : PublicationResult (Option Bool))
    (proposal : PublicationResult Bool) : Bool :=
  (choiceObligation.weaken.completedBy (published := seedOut) choiceRevealed
    (.there (.there .here))).all fun obligation =>
      obligation.accepts (choiceRevealed.reveal (published := seedOut) (.there (.there .here)))
        (Env.cons (x := seedOut) (τ := .publication .bool) proposal <|
          Env.cons (x := choiceOut) (τ := .publication (.option .bool)) published <|
          Env.cons (x := choice) (τ := .commitment .alice (.option .bool))
            (PublicationResult.success Option.none) mixedState)

example : acceptsAtSeed (.success Option.none) (.success true) = true := by decide
example : acceptsAtSeed (.success (some false)) (.success true) = false := by decide
/-- A failed subject publication or a failed input discharges the guard. -/
example : acceptsAtSeed .failure (.success true) = true := by decide
example : acceptsAtSeed (.success (some false)) .failure = true := by decide

def mixedSetup : SourceProgram.Setup (Player := Player) (L := simpleExpr) where
  context := InitialCtx
  namesNodup := by decide
  initialLaw := PMF.pure mixedState
  obligations := {seed}
  program := mixedProgram
  accounts := rfl
  exitTransfers := fun _ => 0

abbrev doomed : VarId := 20
abbrev doomedOut : VarId := 21

def falseGuard :
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

def mixedProfile (bound : PublicationResult (Option Bool))
    (discloseChoice : Bool) : mixedProgram.BehavioralProfile :=
  fun
    | .alice =>
      (fun _ _ _ => PMF.pure (some bound),
        (fun _ _ _ => PMF.pure discloseChoice,
          (fun _ _ _ => PMF.pure true, PUnit.unit)))

def successfulState (sample : Bool) : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) sample <|
  Env.cons (x := seedOut) (PublicationResult.success true) <|
  Env.cons (x := choiceOut) (PublicationResult.success Option.none) <|
  Env.cons (x := choice) (PublicationResult.success Option.none) <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

def invalidState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) (PublicationResult.failure) <|
  Env.cons (x := choiceOut) (PublicationResult.success (some false)) <|
  Env.cons (x := choice) (PublicationResult.success (some false)) <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

def unopenableState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) PublicationResult.failure <|
  Env.cons (x := choiceOut) (PublicationResult.failure) <|
  Env.cons (x := choice) PublicationResult.failure <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

def withheldState : State simpleExpr (mixedProgram.terminalCtx) :=
  Env.cons (x := coin) false <|
  Env.cons (x := seedOut) PublicationResult.failure <|
  Env.cons (x := choiceOut) (PublicationResult.failure) <|
  Env.cons (x := choice) (PublicationResult.success Option.none) <|
  Env.cons (x := seed) (PublicationResult.success true) <|
  Env.cons (x := flag) true (Env.empty (CellVal simpleExpr))

@[simp] private theorem point_law (value : Bool) :
    (RationalLaw.pure value).denote = PMF.pure value := by
  ext other
  rw [RationalLaw.denote_apply, PMF.pure_apply]
  simp [RationalLaw.pure, RationalLaw.entryMass]

macro "solve_mixed_run" : tactic =>
  `(tactic| (
    unfold SourceProgram.run mixedProgram
    rw [SourceProgram.runFrom]
    change ((PMF.pure _).bind _).map SourceProgram.Config.state = _
    rw [PMF.pure_bind, SourceProgram.runFrom]
    change ((PMF.pure _).bind _).map SourceProgram.Config.state = _
    rw [PMF.pure_bind, SourceProgram.runFrom]
    change ((PMF.pure _).bind _).map SourceProgram.Config.state = _
    rw [PMF.pure_bind]))

private theorem successful_run :
    (mixedProgram.run (mixedProfile (.success Option.none) true) mixedState).map
      SourceProgram.Config.state =
      fairBool.denote.map successfulState := by
  solve_mixed_run
  change (fairBool.denote.bind _).map SourceProgram.Config.state = _
  simp only [SourceProgram.runFrom]
  rw [PMF.map_bind]
  simp only [PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  rfl

private theorem invalid_run :
    (mixedProgram.run (mixedProfile (.success (some false)) true) mixedState).map
      SourceProgram.Config.state =
      PMF.pure invalidState := by
  solve_mixed_run
  change ((RationalLaw.pure false).denote.bind _).map SourceProgram.Config.state = _
  rw [point_law, PMF.pure_bind]
  change (PMF.pure _).map SourceProgram.Config.state = _
  rw [PMF.pure_map]
  rfl

private theorem unopenable_run :
    (mixedProgram.run (mixedProfile .failure true) mixedState).map
      SourceProgram.Config.state =
      PMF.pure unopenableState := by
  solve_mixed_run
  change ((RationalLaw.pure false).denote.bind _).map SourceProgram.Config.state = _
  rw [point_law, PMF.pure_bind]
  change (PMF.pure _).map SourceProgram.Config.state = _
  rw [PMF.pure_map]
  rfl

private theorem withholding_run :
    (mixedProgram.run (mixedProfile (.success Option.none) false) mixedState).map
      SourceProgram.Config.state =
      PMF.pure withheldState := by
  solve_mixed_run
  change ((RationalLaw.pure false).denote.bind _).map SourceProgram.Config.state = _
  rw [point_law, PMF.pure_bind]
  change (PMF.pure _).map SourceProgram.Config.state = _
  rw [PMF.pure_map]
  rfl

example (value : Bool) :
    ((((mixedProgram.run (mixedProfile (.success Option.none) true) mixedState).map
      SourceProgram.Config.state).map
      (fun state => state.get .here)) value).toReal = 1 / 2 := by
  rw [successful_run, PMF.map_comp]
  change ((fairBool.denote.map id) value).toReal = _
  rw [PMF.map_id]
  rw [RationalLaw.denote_apply]
  change (∑ index : Fin 2, if value = (fairBool.entries.get index).1 then
    RationalLaw.entryMass (fairBool.entries.get index) else 0).toReal = _
  rw [Fin.sum_univ_two]
  cases value <;> norm_num [fairBool, RationalLaw.entryMass]

example :
    ((mixedProgram.run (mixedProfile (.success Option.none) true) mixedState).map
      SourceProgram.Config.state).map
      mixedProgram.evaluatePayoffs = PMF.pure [(.alice, 10)] := by
  rw [successful_run, PMF.map_comp]
  change fairBool.denote.map (fun _ => ([(Player.alice, 10)] : List (Player × Int))) = _
  exact PMF.map_const _ _

example :
    ((mixedProgram.run (mixedProfile (.success (some false)) true) mixedState).map
      SourceProgram.Config.state).map
      mixedProgram.evaluatePayoffs = PMF.pure [(.alice, -5)] := by
  rw [invalid_run, PMF.pure_map]
  rfl

example :
    ((mixedProgram.run (mixedProfile .failure true) mixedState).map
      SourceProgram.Config.state).map
      mixedProgram.evaluatePayoffs = PMF.pure [(.alice, -10)] := by
  rw [unopenable_run, PMF.pure_map]
  rfl

example :
    ((mixedProgram.run (mixedProfile (.success Option.none) false) mixedState).map
      SourceProgram.Config.state).map
      mixedProgram.evaluatePayoffs = PMF.pure [(.alice, -10)] := by
  rw [withholding_run, PMF.pure_map]
  rfl

def falseProfile : falseGuardProgram.BehavioralProfile :=
  fun
    | .alice =>
      (fun _ _ _ => PMF.pure (some (.success true)),
        (fun _ _ _ => PMF.pure true, PUnit.unit))

def falseGuardState : State simpleExpr (falseGuardProgram.terminalCtx) :=
  Env.cons (x := doomedOut) PublicationResult.failure <|
  Env.cons (x := doomed) (PublicationResult.success true) <|
  Env.empty (CellVal simpleExpr)

private theorem false_guard_run : (falseGuardProgram.run falseProfile
    (Env.empty (CellVal simpleExpr))).map
      SourceProgram.Config.state = PMF.pure falseGuardState := by
  unfold SourceProgram.run falseGuardProgram
  rw [SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map SourceProgram.Config.state = _
  rw [PMF.pure_bind, SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map SourceProgram.Config.state = _
  rw [PMF.pure_bind]
  change (PMF.pure _).map SourceProgram.Config.state = _
  rw [PMF.pure_map]
  rfl

example : ((falseGuardProgram.run falseProfile
      (Env.empty (CellVal simpleExpr))).map
      SourceProgram.Config.state).map falseGuardProgram.evaluatePayoffs =
      PMF.pure [(.alice, -1)] := by
  rw [false_guard_run, PMF.pure_map]
  rfl

end

end VegasTests.SourceSemantics
