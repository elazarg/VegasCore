/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryOnePacketPreservation
import Vegas.Game.RecoveryOnePacketRawLaw

/-! # Sequential preservation by the permanent-exclusion recovery runtime

The original common recovery completion supplies the operational weights, Bayes
beliefs and limit used by every local comparison. Its equilibrium realizes the
intended joint law of typed readout and settled payoff with zero count charges.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (recoveryApplication runtime leaks).Scheduler}
  [(recoveryApplication runtime leaks).FiniteNature
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) scheduler]
  [Finite setup.intendedProtocol.History]

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- Every intended sequential equilibrium is implemented by an equilibrium of
actual permanent-exclusion recovery, preserving its joint readout and settled
payoff law, with no exclusion or audit charge on its equilibrium paths. -/
theorem recovery_intended_raw_sequentialEquilibrium_preserved
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
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := Recovery.rawMenu runtime leaks bounds
    let observe := (recoveryApplication runtime leaks).stateTraffic
    let audit := Recovery.countAudit runtime leaks service.sample
    let base := recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information Initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain Initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information Initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control → control.execution.application.excluded = ∅) ∧
      (∀ final ∈ ((raw.information Initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information Initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks
              final.state), payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  obtain ⟨native, nativeSE, nativeClear, nativeLaw⟩ :=
    RecoveryOnePacket.intended_sequentialEquilibrium_preserved (runtime := runtime) parameter
      utility excludedPayoff
      wellFormed independent observable opportunity inclusion completes timely lowerUtility
      upperUtility lower_le le_upper below intended equilibrium covers coversInputs capacity
  obtain ⟨target, targetSE, clean, states, joint⟩ :=
    recovery_intended_raw_sequentialEquilibrium_of_onePacket (runtime := runtime) parameter
      utility excludedPayoff
      intended native nativeSE nativeLaw service observationRate deliveryRate delivery_nonnegative
      coverage lowerUtility upperUtility lower_le le_upper deposit deposit_nonnegative sufficient
  refine ⟨target, targetSE, ?_, clean, joint⟩
  intro final supported control current
  let raw := Recovery.rawMenu runtime leaks bounds
  let normalize := (Recovery.normalization runtime leaks).state
  have represented : normalize final.state ∈
      (((raw.information Initial horizon scheduler).runBehavioral target.strategy
        (2 * horizon + 1)).map (fun history => normalize history.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  rw [states] at represented
  obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp represented
  rw [current] at same
  exact nativeClear original reached
    { control with execution :=
      ((Recovery.normalization runtime leaks).execution control.execution) } same

end Vegas
