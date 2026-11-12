module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientCompiler

@[expose] public section

/-! # Observable laws and equilibrium outcome coverage of compiled clients

Stochastic observations preserve the certified joint source-configuration and payoff
law. Every intended equilibrium law belongs to the clean runtime equilibrium
laws; no reflection claim about additional runtime equilibria is required.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}
  {spec : ClientSpec setup timeouts leaks bounds horizon scheduler
    parameter utility excludedPayoff}

local notation "Initial" => initialLaw setup
local notation "app" => application setup timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) Initial horizon scheduler

namespace ClientCompilation

variable {intended : setup.intendedModel.BehavioralAssessment}
  (compiled : ClientCompilation spec intended)

/-- Every stochastic observation of the complete source configuration and settled
payoff has its intended law; the observation needs no finite-support premise. -/
theorem clients_postprocessLaw {Result : Type}
    (read : Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) → PMF Result) :
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
    (read : Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) → PMF Result) :
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind
        (fun state => (spec.observation state).bind read) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).bind
        (fun final =>
          read (intendedReadoutExclusion setup parameter utility excludedPayoff final)) := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved]
  exact compiled.clients_postprocessLaw read

end ClientCompilation

namespace ClientSpec

/-- Every intended sequential-equilibrium joint law has a runtime equilibrium
implementation with no public defaults or audit charges on its supported paths. -/
theorem intended_outcomeLaws_subset (spec : ClientSpec setup timeouts leaks bounds
    horizon scheduler parameter utility excludedPayoff) :
    {law | ∃ intended : setup.intendedModel.BehavioralAssessment,
      setup.IntendedSequentialEquilibrium parameter utility intended ∧
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) = law} ⊆
    {law | ∃ target : (model).BehavioralAssessment,
      target.IsSequentialEquilibrium
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      ((raw).bounded Initial horizon scheduler).wellFoundedHistories
      (fun who final => spec.payoff who final.state) ∧
      (∀ final ∈ ((raw).run Initial horizon scheduler target.strategy).support,
        ∀ control, final.state = some control →
          control.execution.application.config.defaulted = ∅) ∧
      (∀ final ∈ ((raw).run Initial horizon scheduler target.strategy).support,
        ∀ who, TerminalAudit.charge (app).stateTraffic
          ((countAudit timeouts) leaks spec.evidenceService.sample) final.state who = 0) ∧
      ((raw).run Initial horizon scheduler target.strategy).bind
        (fun final => spec.observation final.state) = law} := by
  rintro law ⟨intended, equilibrium, rfl⟩
  let compiled := spec.compile intended equilibrium
  exact ⟨compiled.assessment, compiled.equilibrium, compiled.noDefaults,
    compiled.noCharges, compiled.outcomeLaw⟩

end ClientSpec

end Vegas
