/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphDeviation
import GameTheoryExtensions.Core.MixtureSimulation

/-! # Strategic correctness of full-source asynchronous graph compilation

The game executes the compiler's dependency-driven graph under an adaptive
public scheduler. Its strategy compiler and outcome readout are the actual
source compiler's policy translation and total terminal-state decoder.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- The operational game of the compiled event graph, with private setup
sampled inside execution and one public scheduling policy fixed for the game. -/
def eventGame (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler) : GameForm Player :=
  setup.eventGraph.gameForm
    (setup.initialLaw.map fun initial => setup.eventInputs initial.1) scheduler

/-- The full-source compiler simulates every unilateral asynchronous graph
deviation by a finite mixture of source policies. -/
def eventSimulation (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler) :
    GameForm.MixtureSimulationOn setup.gameForm (setup.eventGame scheduler) id
      (terminalState setup.program setup.namesNodup) (fun _ _ => True) where
  compileStrategy := compileEventPolicy setup.program setup.namesNodup
  honest_law profile := by
    change ((setup.eventGame scheduler).play
      (compileEventProfile setup.program setup.namesNodup profile)).map
        (terminalState setup.program setup.namesNodup) = (setup.run profile).map id
    rw [FinDist.map_id]
    simpa only [eventGame, Vegas.EventGraph.gameForm, FinDist.map_bind,
      FinDist.bind_map] using scheduled_setup_law setup scheduler profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    obtain ⟨mixture, law⟩ := scheduled_setup_deviation_law setup scheduler
      profile who replacement
    refine ⟨mixture, ?_⟩
    change ((setup.eventGame scheduler).play
      (Profile.update (sig := setup.eventGraph.gameSignature)
        (compileEventProfile setup.program setup.namesNodup profile) who replacement)).map
          (terminalState setup.program setup.namesNodup) =
        mixture.bind fun alternative =>
          (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
            profile who alternative)).map id
    simpa only [eventGame, Vegas.EventGraph.gameForm, FinDist.map_bind,
      FinDist.bind_map, FinDist.map_id] using law

/-- Same-error Nash preservation and reflection at compiled source profiles
for every real-valued utility of the complete terminal source state. -/
theorem eventGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (terminalState setup.program setup.namesNodup outcome) who)
        ε (compileEventProfile setup.program setup.namesNodup profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  (setup.eventSimulation scheduler).isεNash_compileProfile_iff utility ε profile
    (fun _ _ => trivial)

/-- Every source terminal-state lower bound against unilateral deviations
holds against arbitrary asynchronous graph replacements as well. -/
theorem eventGame_deviation_guarantee
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : State L setup.program.terminalCtx → ℝ) (bound : ℝ)
    (sourceBound : ∀ alternative : BehavioralPolicy who setup.program,
      bound ≤ (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    bound ≤ ((setup.eventGame scheduler).play
      (Profile.update (sig := setup.eventGraph.gameSignature)
        (compileEventProfile setup.program setup.namesNodup profile) who replacement)).expect
          (fun outcome => value (terminalState setup.program setup.namesNodup outcome)) :=
  (setup.eventSimulation scheduler).guarantee profile who value bound sourceBound replacement
    trivial

end Vegas.SourceProgram.Setup
