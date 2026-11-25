module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientCompiler
public import Vegas.Game.NativePaymentReadout
public import Vegas.Game.TerminalObservation

@[expose] public section

/-! # Monetary sequential preservation

The complete source readout and absence of public defaults and audit charges
determine the realized executable receipts, independently of the utility used
to prove equilibrium.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [instDecEq : DecidableEq Player] [instFintype : Fintype Player]
  {L : IExpr} [instResult : IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
  (bounds : MessageBounds setup.informationGraph) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

local notation "app" => application setup timeouts leaks
local notation "Initial" => initialDistribution setup

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
def SourceProgram.Setup.intendedPaymentDistribution
    (intended : setup.intendedModel.BehavioralAssessment) : PMF (TerminalObservation setup) :=
  (setup.intendedModel.runBehavioral intended.strategy (instructionCount setup.program + 1)).map
    fun final => TerminalObservation.read setup
      ((setup.protocolReadout final.state).map (fun config => (config.state, config.defaults)))
      (fun who => (setup.protocolReadout final.state).elim 0 (fun terminal =>
        setup.transfers (setup.program.publicOutcome terminal) who))


variable (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (exitPayoff : Player → ℝ)

local notation "read" => sourceReadout setup timeouts leaks

/-- Clean compiled play preserves executable receipts for any equilibrium utility. -/
theorem intended_raw_programPayments_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility exitPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (compiled : ClientCompilation spec intended) :
    ((raw).run Initial horizon scheduler compiled.assessment.strategy).bind
        (fun final => spec.programPaymentObservation final.state) =
      setup.intendedPaymentDistribution intended := by
  classical
  let native := (raw).run Initial horizon scheduler compiled.assessment.strategy
  let source := setup.intendedModel.runBehavioral intended.strategy
    (instructionCount setup.program + 1)
  let states := native.map History.state
  let cash : Parameter × PublicOutcome setup.program → Player → ℝ :=
    fun outcome who => setup.transfers outcome.2 who
  let exit := fun who => (setup.exitTransfers who : ℝ)
  let reader := fun terminal : Option (Config Player L setup.program.terminalCtx) =>
    TerminalObservation.read setup (terminal.map (fun config => (config.state, config.defaults)))
      (fun who => terminal.elim 0 (fun config => setup.transfers
        (setup.program.publicOutcome config) who))
  have readLaw : native.map (fun final => read final.state) =
      source.map (fun final => setup.protocolReadout final.state) := by
    have projected := congrArg (PMF.map Prod.fst) compiled.outcomeDistribution_eq
    have constant (final : ((raw).protocol Initial horizon scheduler).History) :
        (spec.settlement final.state).map (fun _ => read final.state) =
          PMF.pure (read final.state) := PMF.map_const _ _
    simp only [ClientSpec.observation, PMF.map_bind, PMF.map_comp, Function.comp_def,
      intendedReadoutExclusion] at projected
    simp_rw [constant] at projected
    exact projected
  have clear : ∀ control, some control ∈ states.support →
      control.execution.application.config.defaulted = ∅ := by
    intro control supported
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact compiled.noDefaults final reached control same
  have factors := exclusionBase_valuation_factors (timeouts := timeouts) (leaks := leaks)
    parameter cash exit states clear
  have cleanObservation (final) (supported : final ∈ native.support) :
      spec.programPaymentObservation final.state = PMF.pure (reader (read final.state)) := by
    have present : final.state ∈ states.support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
    rw [ClientSpec.programPaymentObservation,
      TerminalAudit.settlement_clean _ _ _ _ _ (compiled.noCharges final supported),
      PMF.pure_map, factors final.state present]
    rfl
  calc
    _ = native.map (fun final => reader (read final.state)) := by
      rw [← PMF.bind_pure_comp]
      exact bind_congr_on_support _ cleanObservation
    _ = setup.intendedPaymentDistribution intended := by
      have observed := congrArg (PMF.map reader) readLaw
      simp only [PMF.map_comp, Function.comp_def] at observed
      exact observed

/-- The same cash law holds for the compiled physical clients. -/
theorem ClientCompilation.clients_programPayments_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility exitPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (compiled : ClientCompilation spec intended) :
    ((app).finish Initial horizon scheduler compiled.clients none).bind
        spec.programPaymentObservation =
      setup.intendedPaymentDistribution intended := by
  rw [← compiled.clients_stateDistribution, PMF.bind_map]
  exact intended_raw_programPayments_preserved setup timeouts leaks bounds horizon scheduler
    parameter utility exitPayoff spec intended compiled

end Vegas
