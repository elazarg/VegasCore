/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.GraphSetup
import Vegas.Expr.Simple

/-! # A shared-policy private setup regression -/

namespace VegasTests.SourceSetup

open GameTheory GameTheory.Math.Probability Interaction Vegas

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
  Env.cons (x := secret) (BoundValue.value bit, .pending) (Env.empty (CellVal simpleExpr))

private def checkedState (bit : Bool) :
    { state : State simpleExpr InitialCtx // SourceProgram.PrivatePending state } :=
  ⟨initialState bit, by simp [SourceProgram.PrivatePending, initialState, Env.get, Env.cons]⟩

def fairSetup : SourceProgram.Setup (Player := Player) (L := simpleExpr) where
  context := InitialCtx
  namesNodup := by decide
  initialLaw := FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (checkedState false)) (FinDist.pure (checkedState true))
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
        (FinDist.pure (checkedState false)) (FinDist.pure (checkedState true)) := by
  rfl

def profile (chosen : Bool) : SourceProgram.BehavioralProfile program := fun
  | .alice =>
      ((fun h => nomatch h),
        ((fun h => nomatch h),
          (fun _ _ => FinDist.pure true, PUnit.unit)))
  | .bob =>
      (fun _ _ => FinDist.pure (BoundValue.value chosen),
        (fun _ _ => FinDist.pure true,
          ((fun h => nomatch h), PUnit.unit)))

/-- The full two-state setup law transfers through graph compilation without
selecting an initial secret for the strategy compiler. -/
theorem compiled_setup_law (chosen : Bool) :
    (fairSetup.graphGameForm.play
      (fairSetup.compileGraphProfile (profile chosen))).map fairSetup.decodeGraph =
      fairSetup.run (profile chosen) :=
  fairSetup.graph_honest_law (profile chosen)

/-- A concrete native graph deviation has one source backtranslation shared
across both states of the prior. -/
theorem graph_deviation_uses_shared_prior (chosen : Bool) (who : Player)
    (replacement : fairSetup.graphGameForm.sig.Strategy who) :
    (fairSetup.graphGameForm.play
      (Profile.update (fairSetup.compileGraphProfile (profile chosen)) who replacement)).map
        fairSetup.decodeGraph =
      fairSetup.run (Profile.update (sig := SourceProgram.gameSignature fairSetup.program)
        (profile chosen) who
        (SourceProgram.backtranslateGraphPolicy fairSetup.program fairSetup.namesNodup
          SourceProgram.initialMap [] who replacement)) :=
  fairSetup.graph_deviation_law (profile chosen) who replacement

end
end VegasTests.SourceSetup
