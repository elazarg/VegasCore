/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSequentialCompilation
import Vegas.Game.OnePacketBindingRepairAssembly

/-! # Sequential preservation by the default runtime with exclusion payoff

Actual private-binding repairs supply the regular counterparts required by
sequential compilation for the default bounded raw runtime with exclusion payoff.
The resulting equilibrium has zero count-audit charges and preserves the intended
joint readout and payoff law.

The exclusion payoff is determined by the terminal source readout. This theorem
does not equip the runtime with persistent exclusion state that forces later
actions or disables readiness after exclusion.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local instance bindingRepairCompilationHistoryFintype :
    Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol
    (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu (runtime setup) leaks).historyFintype (initialLaw setup) horizon scheduler

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- Every intended sequential equilibrium is implemented by a zero-charge
sequential equilibrium of the default bounded raw runtime with exclusion payoff,
preserving its joint readout and payoff law. -/
theorem onePacket_intended_raw_sequentialEquilibrium_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
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
    (slots_pos : 0 < bounds.candidateCount)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := bounds.rawMenu (runtime setup) leaks
    let observe := (application setup leaks).stateTraffic
    let audit := (runtime setup).countAudit leaks service.sample
    let base := exclusionBase setup parameter utility excludedPayoff leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information (initialLaw setup) horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information (initialLaw setup) horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  refine onePacket_intended_raw_sequentialEquilibrium_of_counterparts
    parameter utility excludedPayoff wellFormed independent contract timely
    (retainsCoveredCanonical_of_adequate bounds covers capacity horizon scheduler bound)
    lowerUtility upperUtility lower_le le_upper below intended equilibrium
    covers coversInputs capacity slots_pos ?_ service observationRate deliveryRate
    delivery_nonnegative coverage deposit deposit_nonnegative sufficient
  intro sequence mixed weights targetSequence assembled mixedTarget _bayes
    who site notFree notOwing past view atSite event turn
  exact OnePacketCounterpartInputs.ofBindingRepairs wellFormed independent mixed
    (fun n => trembleScale_pos
      (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)))
    (fun n => trembleScale_le_one
      (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)).le
      (combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n)))
    (fun _ => rfl) covers coversInputs capacity weights assembled mixedTarget
    notFree notOwing atSite turn

end Vegas
