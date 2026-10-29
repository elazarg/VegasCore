/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryClientCompiler

/-! # Observable laws and equilibrium outcome coverage of compiled clients

Stochastic observations preserve the certified joint terminal-store and payoff
law. Every intended equilibrium law belongs to the clean runtime equilibrium
laws; no reflection claim about additional runtime equilibria is required.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (recoveryApplication runtime leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}
  {spec : RecoveryClientSpec setup runtime leaks bounds horizon scheduler
    parameter utility excludedPayoff}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "app" => recoveryApplication runtime leaks
local notation "raw" => Recovery.rawMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information
  (Recovery.rawMenu runtime leaks bounds) Initial horizon scheduler

namespace RecoveryClientCompilation

variable {intended : setup.intendedModel.BehavioralAssessment}
  (compiled : RecoveryClientCompilation spec intended)

/-- Any stochastic observation of the joint typed-source readout and settled
payoff has exactly its intended law; the observation needs no finite-support premise. -/
theorem clients_postprocessLaw {Result : Type}
    (read : Option (State L setup.program.terminalCtx) × (Player → ℝ) → PMF Result) :
    ((app).finish Initial horizon scheduler compiled.clients none).bind
        (fun state => (spec.observation state).bind read) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).bind
        (fun final =>
          read (intendedReadoutExclusion setup parameter utility excludedPayoff final)) := by
  have same := congrArg (fun law => law.bind read) compiled.clients_outcomeLaw
  simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using same

/-- Ledger clients preserve every stochastic observation of the same certified joint law. -/
theorem ledgerClients_postprocessLaw (unobserved : leaks.DeliversNothing) {Result : Type}
    (read : Option (State L setup.program.terminalCtx) × (Player → ℝ) → PMF Result) :
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind
        (fun state => (spec.observation state).bind read) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).bind
        (fun final =>
          read (intendedReadoutExclusion setup parameter utility excludedPayoff final)) := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved]
  exact compiled.clients_postprocessLaw read

end RecoveryClientCompilation

namespace RecoveryClientSpec

/-- Every intended sequential-equilibrium joint law has a runtime equilibrium
implementation with no exclusions or audit charges on its supported paths. -/
theorem intended_outcomeLaws_subset (spec : RecoveryClientSpec setup runtime leaks bounds
    horizon scheduler parameter utility excludedPayoff) :
    {law | ∃ intended : setup.intendedModel.BehavioralAssessment,
      setup.IntendedSequentialEquilibrium parameter utility intended ∧
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) = law} ⊆
    {law | ∃ target : (model).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((raw).decisionInformationAntichain Initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun final => spec.payoff who final.state) (2 * horizon + 1)) ∧
      (∀ final ∈ ((model).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control → control.execution.application.excluded = ∅) ∧
      (∀ final ∈ ((model).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge (app).stateTraffic
          (Recovery.countAudit runtime leaks spec.evidenceService.sample) final.state who = 0) ∧
      ((model).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => spec.observation final.state) = law} := by
  rintro law ⟨intended, equilibrium, rfl⟩
  let compiled := spec.compile intended equilibrium
  exact ⟨compiled.assessment, compiled.equilibrium, compiled.noExclusions,
    compiled.noCharges, compiled.outcomeLaw⟩

end RecoveryClientSpec

end Vegas
