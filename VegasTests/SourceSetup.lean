/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup
import Vegas.Expr.Simple

/-! # A shared-policy private setup regression -/

namespace VegasTests.SourceSetup

open GameTheory GameTheory.Math.Probability Vegas

noncomputable section

inductive Player where
  | alice
  | bob
  deriving DecidableEq

private abbrev secret : VarId := 0
private abbrev guess : VarId := 1
private abbrev guessOut : VarId := 2
private abbrev secretOut : VarId := 3

private abbrev InitialCtx : SourceCtx Player simpleExpr :=
  [(secret, .privateData .alice .bool)]

private def guessGuard : SourceGuard simpleExpr InitialCtx .bob guess .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun h => nomatch h

def program : SourceProgram Player simpleExpr InitialCtx {secret} :=
  .commit guess .bob (by decide) guessGuard <|
  .reveal guessOut .bob guess (by decide) .here (by decide) <|
  .reveal secretOut .alice secret (by decide) (.there (.there .here)) (by decide) <|
  .ret []

private def initialState (bit : Bool) : State simpleExpr InitialCtx :=
  Env.cons (x := secret) (.success bit) (Env.empty (CellVal simpleExpr))

def fairSetup : SourceProgram.Setup (Player := Player) (L := simpleExpr) where
  context := InitialCtx
  namesNodup := by decide
  initialLaw := FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (initialState false)) (FinDist.pure (initialState true))
  obligations := {secret}
  program := program
  accounts := rfl

/-- Bob receives no value for Alice's private cell in either world. This is
the information-theoretic reason one shared guessing policy cannot optimize
separately for both draws. -/
theorem bob_initial_secret_hidden (bit : Bool) :
    (sourceObserve Player.bob (initialState bit)).cells.get
      (.here : HasVar InitialCtx secret (.privateData Player.alice .bool)) = none := by
  change (if Player.alice = Player.bob then
    some ((initialState bit).get (.here : HasVar InitialCtx secret
      (.privateData Player.alice .bool))) else none) = none
  simp

/-- The setup prior really contains both private worlds with equal weight. -/
theorem fairSetup_initialLaw :
    fairSetup.initialLaw =
      FinDist.mix (1 / 2) (by norm_num) (by norm_num)
        (FinDist.pure (initialState false)) (FinDist.pure (initialState true)) := by
  rfl

def profile (chosen : Bool) : SourceProgram.BehavioralProfile program := fun
  | .alice =>
      ((fun h => nomatch h),
        ((fun h => nomatch h),
          (fun _ _ => FinDist.pure true, PUnit.unit)))
  | .bob =>
      (fun _ _ => FinDist.pure (.success chosen),
        (fun _ _ => FinDist.pure true,
          ((fun h => nomatch h), PUnit.unit)))

end
end VegasTests.SourceSetup
