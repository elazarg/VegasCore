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

/-- Finiteness applies to new binding decisions and imposes no restriction on
initial parameters, chance distributions, or publication payloads. -/
def FiniteBindingTypes : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Prop
  | _, _, .ret _ => True
  | _, _, .sample _ _ _ next => FiniteBindingTypes next
  | _, _, .commit (payload := payload) _ _ _ _ next =>
      Finite (L.Val payload) ∧ FiniteBindingTypes next
  | _, _, .reveal _ _ _ _ _ _ next => FiniteBindingTypes next

/-- A checked source program whose initial state is sampled before play. -/
structure Setup where
  context : SourceCtx Player L
  namesNodup : (context.map Prod.fst).Nodup
  initialLaw : PMF (State L context)
  obligations : Finset VarId
  program : SourceProgram Player L context obligations
  accounts : obligations = commitmentNames context

namespace Setup

def run (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    PMF (State L setup.program.terminalCtx) :=
  setup.initialLaw.bind fun initial => SourceProgram.run setup.program profile initial

/-- The public result law of a profile. `run` keeps the complete terminal
state; only this projection is an outcome. -/
def publicRun (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    PMF (SourceProgram.PublicOutcome setup.program) :=
  (setup.run profile).map (SourceProgram.publicOutcome setup.program)

def gameForm (setup : Setup (Player := Player) (L := L)) : GameForm Player where
  sig := SourceProgram.gameSignature setup.program
  play := setup.publicRun

end Setup
end Vegas.SourceProgram
