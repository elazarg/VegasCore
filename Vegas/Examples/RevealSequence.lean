/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.RevealSequence
import Vegas.Expr.Simple

/-! # Repeated owners and withholding in a reveal-only source program

Alice reveals, Bob reveals, then Alice reveals a different initialized binding.
Failure of the first disclosure does not silently add a guard on later ones.
-/

noncomputable section

namespace Vegas.Examples.RevealSequence

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

abbrev Player := Fin 2

def context : SourceCtx Player simpleExpr :=
  [(2, .commitment 0 .bool), (1, .commitment 1 .bool), (0, .commitment 0 .bool)]

def program : SourceProgram Player simpleExpr context {0, 1, 2} :=
  .reveal 3 0 0 (by decide) (.there (.there .here)) (by decide) <|
  .reveal 4 1 1 (by decide) (.there (.there .here)) (by decide) <|
  .reveal 5 0 2 (by decide) (.there (.there .here)) (by decide) <|
  .ret [(0, .constInt 0), (1, .constInt 0)]

theorem reveal_only : program.RevealOnly := by trivial

theorem three_decisions : program.instructionCount = 3 :=
  RevealOnly.instructionCount_eq_card program reveal_only

def initial (first middle last : Bool) : State simpleExpr context :=
  Env.cons (.success last) (Env.cons (.success middle)
    (Env.cons (.success first) (Env.empty _)))

def profile (first middle last : Bool) : BehavioralProfile program := fun _ =>
  (fun _ _ => PMF.pure first, fun _ _ => PMF.pure middle,
    fun _ _ => PMF.pure last, PUnit.unit)

def results (state : State simpleExpr program.terminalCtx) :
    PublicationResult Bool × PublicationResult Bool × PublicationResult Bool :=
  (state.get (.there (.there .here)), state.get (.there .here), state.get .here)

/-- Source order and repeated ownership introduce no dependency of a later
successful disclosure on the earlier owner's decision to withhold. -/
theorem withholding_then_opening (first middle last : Bool) :
    (program.run (profile false true true) (initial first middle last)).map results =
      PMF.pure (.failure, .success middle, .success last) := by
  simp only [program, SourceProgram.run, runWith, revealKernel, profile,
    afterReveal, PMF.pure_bind, PMF.pure_map]
  rfl

end Vegas.Examples.RevealSequence
