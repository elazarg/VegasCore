/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySequentialCompilation
import Vegas.Game.NativePaymentReadout
import Vegas.Game.TerminalObservation

/-! # Monetary preservation by the permanent-exclusion runtime

The source's executable receipts and private valuation remain distinct. The
existing recovery theorem supplies its exact utility law and clean support;
the same readout then recovers the realized cash vector, with all original
inputs, typed terminal data and public results jointly retained.
-/

noncomputable section

namespace Vegas.Recovery

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [instDecEq : DecidableEq Player] [instFintype : Fintype Player]
  {L : IExpr} [instResult : IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "app" => recoveryApplication runtime leaks
local notation "Initial" => PMF.map
  (fun native : EventGraphRuntime.State (Vegas.graph setup) =>
    (RecoveryState.mk native (∅ : Finset Player) : RecoveryState (Vegas.graph setup)))
      (Vegas.initialLaw setup)

variable [finiteNature : (recoveryApplication runtime leaks).FiniteNature
    (PMF.map
      (fun native =>
        (RecoveryState.mk native (∅ : Finset Player) : RecoveryState (Vegas.graph setup)))
      (Vegas.initialLaw setup)) scheduler]
  [finiteSource : Finite setup.intendedProtocol.History]

include finiteNature finiteSource

local notation "raw" => Recovery.rawMenu runtime leaks bounds
local notation "R" => ReactiveApplication.ResponseMenu.information
  (Recovery.rawMenu runtime leaks bounds) Initial horizon scheduler

variable {Public : Type*} {signal : State L setup.context → Public}

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
  (exitValuation exitTransfer : Player → ℝ)

local notation "utility" => setup.program.parameterPaymentUtility valuation
local notation "exitPayoff" => (fun who => exitValuation who + exitTransfer who)

local notation "base" => recoveryExclusionBase (runtime := runtime) (leaks := leaks)
  parameter utility exitPayoff
local notation "read" => fun state => sourceReadout setup runtime leaks
  (RecoveryProjection.protocolState runtime leaks state)

/-- The original raw sequential-equilibrium guarantee also preserves the actual
cash vector. The actual intended histories have no failed publication, so no
restriction on valuation or executable transfers at other source outcomes is
required. Declared exit valuation and cash remain separate runtime inputs. -/
theorem intended_raw_programPayments_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (timely : AsyncTimely runtime delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, exitPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (exitPayoff who) (upperUtility who)) -
          min 0 (min (exitPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let observe := (app).stateTraffic
    let audit := Recovery.countAudit runtime leaks service.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (R).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((raw).decisionInformationAntichain Initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun final => payoff final.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.excluded = ∅) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs => (read final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility exitPayoff) ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => (TerminalAudit.settlement
          (recoveryExclusionBase (runtime := runtime) (leaks := leaks) parameter
            (fun outcome who => setup.program.publicTransfers outcome.2 who) exitTransfer)
          observe audit deposit final.state).map fun receipts =>
            TerminalObservation.read setup (read final.state) receipts) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map (fun final =>
            TerminalObservation.read setup (setup.protocolReadout final.state)
              (fun who => (setup.protocolReadout final.state).elim 0 (fun terminal =>
                setup.program.publicTransfers (setup.program.publicOutcome terminal) who))) := by
  classical
  intro observe audit payoff settle
  obtain ⟨target, targetSE, clear, clean, joint⟩ :=
    recovery_intended_raw_sequentialEquilibrium_preserved (setup := setup) (runtime := runtime)
      (leaks := leaks) (bounds := bounds) (horizon := horizon) (scheduler := scheduler) parameter
      utility exitPayoff wellFormed independent observable opportunity inclusion completes timely
      lowerUtility upperUtility lower_le le_upper below intended equilibrium covers coversInputs
      capacity service observationRate deliveryRate delivery_nonnegative coverage deposit
      deposit_nonnegative sufficient
  refine ⟨target, targetSE, clear, clean, joint, ?_⟩
  let targetLaw := ((R).runBehavioral target.strategy (2 * horizon + 1)).map History.state
  let sourceLaw := (setup.intendedModel.runBehavioral intended.strategy
    (instructionCount setup.program + 1)).map (fun final =>
      let terminal := setup.protocolReadout final.state
      (terminal, fun who => terminal.elim 0 (fun state =>
        setup.program.publicTransfers (setup.program.publicOutcome state) who)))
  have utilityLaw :
      (TerminalAudit.jointSettlement targetLaw base observe audit deposit).map
        (fun realized => (read realized.1, realized.2)) =
        sourceLaw.map (utilityReadout (fun terminal who => terminal.elim 0 (fun state =>
          valuation (setup.parameterOutcome parameter state) who))) := by
    have left : (TerminalAudit.jointSettlement targetLaw base observe audit deposit).map
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
          setup.program.publicTransfers (setup.program.publicOutcome terminal) who)
      rw [setup.intended_exclusionReadoutUtility wellFormed parameter utility exitPayoff final who]
      cases setup.protocolReadout final.state <;>
        simp only [Option.elim_none, Option.elim_some, parameterPaymentUtility_eq, add_zero]
      rfl
  have cleanSupport : ∀ control, some control ∈ targetLaw.support →
      control.execution.application.excluded = ∅ := by
    intro control supported
    obtain ⟨final, finalSupported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact clear final finalSupported control same
  have factors := exclusionBase_valuation_factors (runtime := runtime) (leaks := leaks)
    parameter valuation exitValuation targetLaw cleanSupport
  have cash := jointCashLaw_of_utility_law (runtime := runtime) (leaks := leaks) parameter
    valuation (fun outcome who => setup.program.publicTransfers outcome.2 who)
    exitValuation exitTransfer targetLaw sourceLaw factors observe audit deposit utilityLaw
  have observed := congrArg (PMF.map (fun realized =>
    TerminalObservation.read setup realized.1 realized.2)) cash
  simpa only [targetLaw, sourceLaw, TerminalAudit.jointSettlement, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def] using observed

end Vegas.Recovery
