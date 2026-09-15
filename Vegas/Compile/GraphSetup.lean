/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup
import Vegas.Compile.GraphLaw

/-! # Compilation law for distributed source setup -/

noncomputable section
namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

def graph (setup : Setup (Player := Player) (L := L)) :
    Graph Player L (graphCtx setup.context) (graphCtx setup.program.terminalCtx) :=
  compileGraph setup.program setup.namesNodup initialMap []

def graphGameForm (setup : Setup (Player := Player) (L := L)) : GameForm Player where
  sig := Graph.gameSignature setup.graph
  play profile := setup.initialLaw.bind fun initial =>
    Graph.run setup.graph profile (encodeState initial.1)

def decodeGraph (setup : Setup (Player := Player) (L := L)) :
    VEnv L (graphCtx setup.program.terminalCtx) → State L setup.program.terminalCtx :=
  decodeState (terminalMap setup.program setup.namesNodup initialMap)

def compileGraphProfile (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) : Graph.BehavioralProfile setup.graph :=
  fun who => compileGraphPolicy setup.program setup.namesNodup initialMap [] who (profile who)

/-- Compiled and source executions have the same terminal-state law after the
shared initial draw. -/
theorem graph_honest_law (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    (setup.graphGameForm.play (setup.compileGraphProfile profile)).map setup.decodeGraph =
      setup.run profile := by
  unfold graphGameForm Graph.gameSignature run graph decodeGraph compileGraphProfile
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial _
  change
    (Graph.runWith (compileGraph setup.program setup.namesNodup initialMap [])
      (fun who => compileGraphPolicy setup.program setup.namesNodup initialMap [] who
        (profile who))
      (encodeState initial.1) (fun _ => [])).map
        (decodeState (terminalMap setup.program setup.namesNodup initialMap)) =
      runWith setup.program profile initial.1 [] (fun _ => [])
  have law := compileGraph_runWith setup.program setup.namesNodup initialMap [] profile
    (encodeState initial.1) (fun _ => [])
  rw [decodeState_encodeState_initial initial.1 initial.2] at law
  exact law

end Vegas.SourceProgram.Setup
