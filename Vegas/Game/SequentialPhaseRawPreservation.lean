/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhasePreservation
import Vegas.Game.SequentialPhaseRawLaw

/-! # Intended sequential equilibria in the audited raw phase runtime

The sequential compiled graph uses singleton phases with the original physical
service contract, arbitrary observations and the realized terminal audit utility.
-/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]

local notation "app" => phaseApplication (runtime setup) leaks
local notation "raw" => PhaseCount.rawMenu (runtime setup) leaks bounds
local notation "R" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.rawMenu (runtime setup) leaks bounds) (initialLaw setup) horizon scheduler

variable {Public : Type*} {signal : State L setup.context → Public}

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "base" => phaseExclusionBase setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks
  (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
local notation "read" => phaseSourceReadout setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks

/-- Every intended sequential equilibrium has an audited raw phase implementation
with the same joint typed readout and realized settled payoff law. Equilibrium
paths exclude nobody and incur zero count-audit charges. -/
theorem intended_raw_sequentialEquilibrium_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon
      scheduler bound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup) horizon
      scheduler)
    (timely : AsyncTimely (runtime setup) delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (service : EvidenceReportService (PhaseCount.Evidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : PhaseCount.EvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let observe := (app).stateTraffic
    let audit := PhaseCount.audit (runtime setup) leaks service.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (R).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((raw).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun final => payoff final.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.current.excluded = ∅) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs => (read final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  intro observe audit payoff settle
  obtain ⟨canonical, canonicalSE, clear, law⟩ :=
    intended_sequentialEquilibrium_preserved setup leaks bounds horizon scheduler parameter
      utility excludedPayoff wellFormed independent observable opportunity inclusion completes
      timely
      lowerUtility upperUtility lower_le le_upper below intended equilibrium covers coversInputs
      capacity
  obtain ⟨target, targetSE, noExclusion, noCharges, _states, joint⟩ :=
    canonical_raw_sequentialEquilibrium setup leaks bounds horizon scheduler parameter utility
      excludedPayoff intended canonical canonicalSE clear law service observationRate deliveryRate
      delivery_nonnegative coverage lowerUtility upperUtility lower_le le_upper deposit
      deposit_nonnegative sufficient
  exact ⟨target, targetSE, noExclusion, noCharges, joint⟩

end Vegas.SequentialPhase
