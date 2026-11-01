/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketEquilibriumPreservation
import Vegas.Game.OnePacketRawLaw

/-! # Intended sequential equilibria in the audited native raw runtime

The actual bounded raw menu retains the source equilibrium's joint complete
configuration and settled payoff law. Sequential rationality covers whole
continuation policies in that supplied bounded menu. Supported play has no
public defaults and pays no count-audit charge.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => initialLaw setup

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- An intended sequential equilibrium compiles to an actual native assessment
that is sequentially rational against every policy in the supplied bounded raw
menu and preserves the joint complete source configuration and settled payoff. -/
theorem intended_raw_sequentialEquilibrium_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (completes : CompletesPlay runtime leaks Initial horizon scheduler)
    (timely : runtime.AsyncTimely delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
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
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := bounds.rawMenu runtime leaks
    let observe := (application setup runtime leaks).stateTraffic
    let audit := runtime.countAudit leaks service.sample
    let base := exclusionBase setup runtime parameter utility excludedPayoff leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information Initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain Initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information Initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.config.defaulted = ∅) ∧
      (∀ final ∈ ((raw.information Initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information Initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup runtime leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  obtain ⟨native, nativeSE, nativeClear, nativeLaw⟩ :=
    intended_onePacket_sequentialEquilibrium_preserved (runtime := runtime) parameter utility
      excludedPayoff wellFormed independent observable opportunity inclusion completes timely
      lowerUtility upperUtility lower_le le_upper below intended equilibrium covers coversInputs
      capacity
  obtain ⟨target, targetSE, clean, states, joint⟩ :=
    intended_raw_sequentialEquilibrium_of_onePacket (runtime := runtime) (initial := Initial)
      parameter utility excludedPayoff intended native nativeSE nativeLaw service observationRate
      deliveryRate delivery_nonnegative coverage lowerUtility upperUtility
      (fun _ _ _ who => lower_le _ who) (fun _ _ _ who => le_upper _ who)
      deposit deposit_nonnegative sufficient
  refine ⟨target, targetSE, ?_, clean, joint⟩
  intro final supported control current
  let raw := bounds.rawMenu runtime leaks
  let normalize := (runtime.reactiveNormalization leaks).state
  have represented : normalize final.state ∈
      (((raw.information Initial horizon scheduler).runBehavioral target.strategy
        (2 * horizon + 1)).map (fun history => normalize history.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  rw [states] at represented
  obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp represented
  rw [current] at same
  exact nativeClear original reached
    { control with execution :=
      (runtime.reactiveNormalization leaks).execution control.execution } same

end Vegas
