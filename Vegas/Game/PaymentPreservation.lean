/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ClientCompiler
import Vegas.Game.NativePaymentReadout
import Vegas.Game.TerminalObservation

/-! # Monetary sequential preservation

Valuation and executable receipts share the native public default and complete
source readout. Their joint utility law determines the realized cash law while
retaining the initial inputs, terminal state and public results.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [instDecEq : DecidableEq Player] [instFintype : Fintype Player]
  {L : IExpr} [instResult : IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

local notation "app" => application setup timeouts leaks
local notation "Initial" => initialLaw setup

local notation "raw" => bounds.rawMenu timeouts leaks
local notation "R" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) Initial horizon scheduler

variable {Parameter : Type} (parameter : State L setup.context → Parameter)

variable {setup timeouts leaks bounds horizon scheduler parameter} in
/-- Audited executable receipts retain the same fixed source readers. -/
def ClientSpec.programPaymentObservation
    {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
    {exitPayoff : Player → ℝ}
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility exitPayoff)
    (state : (app).ProtocolState) : PMF (TerminalObservation setup) :=
  (TerminalAudit.settlement
    (exclusionBase setup timeouts parameter (fun outcome who => setup.transfers outcome.2 who)
      (fun who => (setup.exitTransfers who : ℝ)) leaks)
    (app).stateTraffic ((countAudit timeouts) leaks spec.evidenceService.sample)
    spec.deposit state).map fun receipts =>
      TerminalObservation.read setup
        ((sourceReadout setup timeouts leaks state).map
          (fun config => (config.state, config.defaults))) receipts

/-- Intended source play, read jointly with the setup's executable receipts. -/
def SourceProgram.Setup.intendedPaymentLaw
    (intended : setup.intendedModel.BehavioralAssessment) : PMF (TerminalObservation setup) :=
  (setup.intendedModel.runBehavioral intended.strategy (instructionCount setup.program + 1)).map
    fun final => TerminalObservation.read setup
      ((setup.protocolReadout final.state).map (fun config => (config.state, config.defaults)))
      (fun who => (setup.protocolReadout final.state).elim 0 (fun terminal =>
        setup.transfers (setup.program.publicOutcome terminal) who))

variable (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
  (exitValuation : Player → ℝ)

local notation "utility" => setup.parameterPaymentUtility valuation
local notation "exitTransfer" => (fun who => (setup.exitTransfers who : ℝ))
local notation "exitPayoff" => (fun who => exitValuation who + exitTransfer who)

local notation "base" => exclusionBase setup timeouts parameter utility exitPayoff leaks
local notation "read" => sourceReadout setup timeouts leaks

/-- Every supplied native compilation preserves realized cash jointly with
initial inputs, terminal state and public results. Cash uses the setup's declared
exit transfer; valuation is supplied separately. -/
theorem intended_raw_programPayments_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility exitPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (compiled : ClientCompilation spec intended) :
    ((R).runBehavioral compiled.assessment.strategy (2 * horizon + 1)).bind
        (fun final => spec.programPaymentObservation final.state) =
      setup.intendedPaymentLaw intended := by
  classical
  let observe := (app).stateTraffic
  let audit := (countAudit timeouts) leaks spec.evidenceService.sample
  let settle := TerminalAudit.settlement base observe audit spec.deposit
  let target := compiled.assessment
  have clear := compiled.noDefaults
  have joint : ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs => (read final.state, payoffs)) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility exitPayoff) := compiled.outcomeLaw
  let targetLaw := ((R).runBehavioral target.strategy (2 * horizon + 1)).map History.state
  let sourceLaw := (setup.intendedModel.runBehavioral intended.strategy
    (instructionCount setup.program + 1)).map (fun final =>
      let terminal := setup.protocolReadout final.state
      (terminal, fun who => terminal.elim 0 (fun state =>
        setup.transfers (setup.program.publicOutcome state) who)))
  have utilityLaw :
      (TerminalAudit.jointSettlement targetLaw base observe audit spec.deposit).map
        (fun realized => (read realized.1, realized.2)) =
        sourceLaw.map (utilityReadout (fun terminal who => terminal.elim 0 (fun state =>
          valuation (setup.parameterOutcome parameter state) who))) := by
    have left : (TerminalAudit.jointSettlement targetLaw base observe audit spec.deposit).map
        (fun realized => (read realized.1, realized.2)) =
        ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs => (read final.state, payoffs)) := by
      simp only [targetLaw, TerminalAudit.jointSettlement, PMF.map_bind, PMF.bind_map,
        PMF.map_comp, Function.comp_def]
      rfl
    rw [left, joint]
    simp only [sourceLaw, PMF.map_comp]
    congr 1
    funext final
    apply Prod.ext
    · rfl
    · funext who
      change exclusionReadoutUtility setup parameter utility exitPayoff
          (setup.protocolReadout final.state) who =
        (setup.protocolReadout final.state).elim 0 (fun terminal =>
          valuation (setup.parameterOutcome parameter terminal) who) +
        (setup.protocolReadout final.state).elim 0 (fun terminal =>
          setup.transfers (setup.program.publicOutcome terminal) who)
      rw [setup.intended_exclusionReadoutUtility spec.wellFormed parameter utility exitPayoff
        final who]
      cases setup.protocolReadout final.state <;>
        simp only [Option.elim_none, Option.elim_some, Setup.parameterPaymentUtility_eq, add_zero]
      rfl
  have cleanSupport : ∀ control, some control ∈ targetLaw.support →
      control.execution.application.config.defaulted = ∅ := by
    intro control supported
    obtain ⟨final, finalSupported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact clear final finalSupported control same
  have factors := exclusionBase_valuation_factors (timeouts := timeouts) (leaks := leaks)
    parameter valuation exitValuation targetLaw cleanSupport
  have cash := jointCashLaw_of_utility_law (timeouts := timeouts) (leaks := leaks) parameter
    valuation (fun outcome who => setup.transfers outcome.2 who)
    exitValuation exitTransfer targetLaw sourceLaw factors observe audit spec.deposit utilityLaw
  have observed := congrArg (PMF.map (fun realized =>
    TerminalObservation.read setup
      (realized.1.map (fun config => (config.state, config.defaults))) realized.2)) cash
  simpa only [targetLaw, sourceLaw, target, ClientSpec.programPaymentObservation,
    Setup.intendedPaymentLaw, TerminalAudit.jointSettlement, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def] using observed


/-- The exact physical clients decoded from any supplied compilation preserve
program receipts; no source-equilibrium premise is needed for this law. -/
theorem ClientCompilation.clients_programPayments_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility exitPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (compiled : ClientCompilation spec intended) :
    ((app).finish Initial horizon scheduler compiled.clients none).bind
        spec.programPaymentObservation =
      setup.intendedPaymentLaw intended := by
  rw [← compiled.clients_stateLaw, PMF.bind_map]
  exact intended_raw_programPayments_preserved setup timeouts leaks bounds horizon scheduler
    parameter valuation exitValuation spec intended compiled

end Vegas
