module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedCompilationLaw
public import Vegas.Game.ConditionedSourceRationality

@[expose] public section

/-! # Compiling across locally observed source components -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} (signal : State L setup.context → Signal)
    (supported : ∀ key, key ∈ (setup.initialLaw.map signal).support)
    (inside : ∀ key who (site : (setup.conditionInitial signal key).intendedModel.InformationSite
      who) (history : setup.intendedModel.InformationHistory who site.1),
      setup.initialComponent signal key history.1.state)
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    {Parameter : Type} {parameter : State L setup.context → Parameter}
    {utility : Parameter × PublicOutcome setup.program → Player → ℝ} {exit : Player → ℝ}
    (spec : ∀ key, ClientSpec (setup.conditionInitial signal key) timeouts leaks bounds horizon
      scheduler parameter utility exit)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)

local notation "app" => application setup timeouts leaks

/-- Compile the supplied global intended assessment in each component, retaining its beliefs
at off-path decisions through source restriction. -/
def compileComponent (key : Signal) :
    ClientCompilation (spec key)
      (setup.conditionInitial_assessment signal key (supported key) (inside key) intended) :=
  (spec key).compile _ (setup.conditionInitial_intendedSequentialEquilibrium signal key
    (supported key) (inside key) parameter utility intended equilibrium)

/-- The compiled, locally selected clients preserve the full joint configuration and
settled-payoff law of the original intended equilibrium with the original joint prior. -/
theorem compileComponent_outcomeLaw
    (read : Player → (app).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialLaw.support, ∀ execution : (app).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
        execution.application → ∀ who, read who (execution.observe app who) = signal draw)
    (formed : setup.WellFormed)
    (observation : (app).ProtocolState →
      PMF (Option (Config Player L setup.program.terminalCtx) × (Player → ℝ)))
    (same : ∀ key, (spec key).observation = observation) :
    ((app).finish (Vegas.initialLaw setup) horizon scheduler (signalClients read fun key =>
      (compileComponent signal supported inside spec intended equilibrium key).clients) none).bind
        observation =
      (setup.intendedModel.runBehavioral intended.strategy (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility exit) := by
  apply setup.signalClients_intendedLaw signal horizon read observed _ formed intended.strategy
    parameter utility exit observation
  intro key _
  rw [← same key]
  exact (compileComponent signal supported inside spec intended equilibrium key).clients_outcomeLaw

end Vegas.SourceProgram.Setup
