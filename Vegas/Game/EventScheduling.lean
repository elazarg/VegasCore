module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphScheduling
public import GameTheory.Core.MixtureSimulation

@[expose] public section

/-! # Exact scheduling equivalence for compiler-generated graphs -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Observe the complete typed terminal store while forgetting its terminality
certificate and chronological trace. -/
def terminalStore (result : graph.gameSignature.Outcome) :
    EventGraph.Store graph.layout := result.1.store

/-- The store law of a play, with the outcome's terminality certificate and
chronological trace forgotten. -/
theorem gameForm_play_map_terminalStore
    (inputs : PMF graph.Inputs) (scheduler : graph.PublicScheduler)
    (profile : graph.BehavioralProfile) :
    ((graph.gameForm inputs scheduler).play profile).map graph.terminalStore =
      inputs.bind fun initial =>
        (graph.runPolicies scheduler profile initial).map Config.store := by
  unfold gameForm terminalStore
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  calc
    (graph.terminalOutcomes scheduler profile initial).map
        (fun result => result.1.store) =
      ((graph.terminalOutcomes scheduler profile initial).map Subtype.val).map
        Config.store := by rw [PMF.map_comp]; rfl
    _ = (graph.runPolicies scheduler profile initial).map Config.store := by
      rw [graph.terminalOutcomes_map_val]

end Vegas.EventGraph

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiled graph game under the supplied public scheduler. -/
def eventGame (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.informationGraph.PublicScheduler) : GameForm Player :=
  setup.informationGraph.gameForm
    (setup.initialDistribution.map fun initial => setup.eventInputs initial) scheduler

/-- The same compiled game under its canonical scheduler. -/
def canonicalEventGame (setup : Setup (Player := Player) (L := L)) : GameForm Player :=
  setup.eventGame setup.informationGraph.canonicalScheduler

/-- The information graph gives every public scheduler the same full outcome law. -/
theorem eventGame_play_eq (setup : Setup (Player := Player) (L := L))
    (first second : setup.informationGraph.PublicScheduler)
    (profile : setup.informationGraph.BehavioralProfile) :
    (setup.eventGame first).play profile = (setup.eventGame second).play profile := by
  unfold eventGame EventGraph.gameForm
  simp only [PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  exact toInformationGraph_terminalOutcomes_eq setup.program profile first second _

/-- Scheduling preserves every terminal observation with unchanged player strategies.
Each unilateral deviation has the same law as that one deviation canonically. -/
def eventSchedulingSimulationOn {Observation : Type}
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.informationGraph.PublicScheduler)
    (observe : setup.informationGraph.gameSignature.Outcome → Observation) :
    GameForm.MixtureSimulationOn setup.canonicalEventGame (setup.eventGame scheduler)
      observe observe (fun _ _ => True) where
  compileStrategy _ strategy := strategy
  honest_law profile := by
    change ((setup.eventGame scheduler).play profile).map observe =
      (setup.canonicalEventGame.play profile).map observe
    exact congrArg (PMF.map observe)
      (setup.eventGame_play_eq scheduler setup.informationGraph.canonicalScheduler profile)
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨PMF.pure replacement, ?_⟩
    rw [PMF.pure_bind]
    change ((setup.eventGame scheduler).play (Profile.update profile who replacement)).map observe =
      (setup.canonicalEventGame.play (Profile.update profile who replacement)).map observe
    exact congrArg (PMF.map observe)
      (setup.eventGame_play_eq scheduler setup.informationGraph.canonicalScheduler _)

end Vegas.SourceProgram.Setup
