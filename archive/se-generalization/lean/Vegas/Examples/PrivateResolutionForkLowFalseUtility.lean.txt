/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkSource
import Vegas.Source.InitialState

/-! # Public-result utility for the private-type resolution fork

The utility reads the immutable initial type and the public publication results.
It does not distinguish an expired opening from an accepted withholding result.
The lower FALSE reward removes the authentic-certificate withholding tie while
retaining Alice's total payoff range two. Native equilibrium and builder
certification are separate obligations.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram

def typeParameter (state : State simpleExpr setup.context) : Bool :=
  state.get (.there (.there .here))

def lowFalsePublicUtility (result : Bool × PublicOutcome setup.program) (who : Player) : ℝ :=
  let high := result.1
  let disclosed := (result.2.get (.there .here)).isSuccess
  let guessedHigh := (result.2.get .here).isSuccess
  if who = alice then
    if high then (if disclosed then 2 else 0)
    else if disclosed then (if guessedHigh then 2 else 1 / 2)
    else if guessedHigh then 0 else 1
  else if guessedHigh = high then 1 else 0

def lowFalseSourceUtility (state : State simpleExpr setup.program.terminalCtx)
    (who : Player) : ℝ :=
  lowFalsePublicUtility (setup.parameterOutcome typeParameter state) who

theorem lowFalse_source_utility (high disclose guess : Bool) (who : Player) :
    lowFalseSourceUtility (sourceDone high disclose guess).state who =
      if who = alice then
        (if high then (if disclose then 2 else 0)
        else if disclose then (if guess then 2 else 1 / 2)
        else if guess then 0 else 1)
      else if guess = high then 1 else 0 := by
  cases high <;> cases disclose <;> cases guess <;> fin_cases who <;> rfl

theorem lowFalse_public_utility_range (result : Bool × PublicOutcome setup.program)
    (who : Player) : 0 ≤ lowFalsePublicUtility result who ∧
      lowFalsePublicUtility result who ≤ 2 := by
  unfold lowFalsePublicUtility
  dsimp only
  split_ifs <;> norm_num

end Vegas.PrivateResolutionFork
