/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Distributed initial setup for source games

An initial setup samples a finite law of public and private source states before
play, while the players use one behavioral profile across the whole law.
-/

noncomputable section
namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

/-- A checked source program whose initial state is sampled before play. -/
structure Setup where
  context : SourceCtx Player L
  namesNodup : (context.map Prod.fst).Nodup
  initialLaw : FinDist (State L context)
  obligations : Finset VarId
  program : SourceProgram Player L context obligations
  accounts : obligations = commitmentNames context

namespace Setup

def run (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    FinDist (State L setup.program.terminalCtx) :=
  setup.initialLaw.bind fun initial => SourceProgram.run setup.program profile initial

/-- The public result law of a profile. `run` keeps the complete terminal
state; only this projection is an outcome. -/
def publicRun (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    FinDist (SourceProgram.PublicOutcome setup.program) :=
  (setup.run profile).map (SourceProgram.publicOutcome setup.program)

def gameForm (setup : Setup (Player := Player) (L := L)) : GameForm Player where
  sig := SourceProgram.gameSignature setup.program
  play := setup.publicRun

end Setup
end Vegas.SourceProgram
