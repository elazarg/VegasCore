/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComponents
import Vegas.Game.PhaseResponseAliasEquilibrium
import Vegas.Game.PhaseOnePacketExtension
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.OnePacketLawApproximation

/-! # Audited raw extension of the canonical singleton phase equilibrium

Operational private aliases are restored before the existing count-audit
extension. The original phase source readout and base utility are retained.
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
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "app" => phaseApplication (runtime setup) leaks
local notation "canonicalMenu" => menu setup leaks bounds
local notation "counted" => PhaseCount.onePacketMenu (runtime setup) leaks bounds
local notation "raw" => PhaseCount.rawMenu (runtime setup) leaks bounds
local notation "normal" => PhaseCount.normalization (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "C" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu (runtime setup) leaks bounds) (phaseInitialLaw setup) horizon scheduler
local notation "R" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.rawMenu (runtime setup) leaks bounds) (phaseInitialLaw setup) horizon scheduler

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "base" => phaseExclusionBase setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks
  (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
local notation "read" => phaseSourceReadout setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks

/-- A canonical phase equilibrium with its actual initialized law extends to
the audited raw phase game. Multiplicative funding suffices even at zero rates;
no division, extra rate positivity or exit-floor inequality is imposed. -/
theorem canonical_raw_sequentialEquilibrium
    (source : setup.intendedModel.BehavioralAssessment)
    (canonical : (M).BehavioralAssessment)
    (equilibrium : canonical.IsSequentialEquilibriumFor
      ((canonicalMenu).decisionInformationAntichain (phaseInitialLaw setup) horizon scheduler)
      (fun who site => canonical.truncatedContinuationContext site
        (fun final => base final.state who) (2 * horizon + 1)))
    (clear : ∀ final ∈ ((M).runBehavioral canonical.strategy (2 * horizon + 1)).support,
      ∀ control, final.state = some control → control.execution.application.current.excluded = ∅)
    (law : ((M).runBehavioral canonical.strategy (2 * horizon + 1)).map (fun final =>
      (read final.state, base final.state)) =
      (setup.intendedModel.runBehavioral source.strategy (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff))
    (service : EvidenceReportService (PhaseCount.Evidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : PhaseCount.EvidenceCoverage service observationRate deliveryRate)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
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
        ((raw).decisionInformationAntichain (phaseInitialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun final => payoff final.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.current.excluded = ∅) ∧
      (∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).map
        (fun final => (normal).state final.state) =
          ((M).runBehavioral canonical.strategy (2 * horizon + 1)).map History.state ∧
      ((R).runBehavioral target.strategy (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs => (read final.state, payoffs)) =
        (setup.intendedModel.runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  intro observe audit payoff settle
  have normalized (state : (app).ProtocolState) : base ((normal).state state) = base state := by
    cases state <;> rfl
  have normalizedRead (state : (app).ProtocolState) : read ((normal).state state) = read state := by
    cases state <;> rfl
  obtain ⟨aliases, _aliasStrategy, aliasSE, _aliasBeliefs, aliasStates⟩ :=
    PhaseCount.onePacket_alias_sequentialEquilibrium (runtime setup) leaks bounds (phaseInitialLaw
        setup)
      horizon scheduler canonical (fun who state => base state who)
      (fun who state => congrFun (normalized state) who) equilibrium
  let countedCertificate := ((counted).bounded (phaseInitialLaw setup) horizon
    scheduler).wellFoundedHistories
  let rawCertificate := ((raw).bounded (phaseInitialLaw setup) horizon
      scheduler).wellFoundedHistories
  have countedSE := (aliases.isSequentialEquilibrium_iff_truncated_of_bounded (C)
    ((counted).decisionInformationAntichain (phaseInitialLaw setup) horizon scheduler)
    countedCertificate ((counted).bounded (phaseInitialLaw setup) horizon scheduler)
    (fun who final => base final.state who)).mpr aliasSE
  obtain ⟨target, targetSE, _extends, _beliefs, terminalLaw, _settled, clean⟩ :=
    PhaseCount.onePacket_raw_sequentialEquilibrium (runtime := runtime setup) (leaks := leaks)
      (bounds := bounds) (initial := phaseInitialLaw setup) (horizon := horizon) (scheduler :=
          scheduler)
      service observationRate deliveryRate delivery_nonnegative coverage base
      (fun who => min 0 (min (excludedPayoff who) (lowerUtility who)))
      (fun who => max 0 (max (excludedPayoff who) (upperUtility who))) deposit
      (fun state who => (phaseExclusionBase_mem_Icc setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        lowerUtility upperUtility (fun terminal => lower_le (setup.parameterOutcome parameter
          terminal)) (fun terminal => le_upper (setup.parameterOutcome parameter terminal))
        state who).1)
      (fun state who => (phaseExclusionBase_mem_Icc setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        lowerUtility upperUtility (fun terminal => lower_le (setup.parameterOutcome parameter
          terminal)) (fun terminal => le_upper (setup.parameterOutcome parameter terminal))
        state who).2)
      deposit_nonnegative sufficient aliases countedSE
  have countedEvaluation := (C).runBehavioralTerminalFrom_initHistory countedCertificate
    aliases.strategy ((counted).bounded (phaseInitialLaw setup) horizon scheduler)
  have rawEvaluation := (R).runBehavioralTerminalFrom_initHistory rawCertificate target.strategy
    ((raw).bounded (phaseInitialLaw setup) horizon scheduler)
  rw [countedEvaluation, rawEvaluation] at terminalLaw
  have rawStates : ((R).runBehavioral target.strategy (2 * horizon + 1)).map
      (fun final => (normal).state final.state) =
        ((M).runBehavioral canonical.strategy (2 * horizon + 1)).map History.state := by
    have projected := congrArg
      (PMF.map fun final => (normal).state final.state) terminalLaw
    rw [PMF.map_comp] at projected
    have first : ((R).runBehavioral target.strategy (2 * horizon + 1)).map
        (fun final => (normal).state final.state) =
      ((C).runBehavioral aliases.strategy (2 * horizon + 1)).map
        (fun final => (normal).state final.state) := by
      exact projected.symm
    exact first.trans aliasStates
  have rawClean : ∀ final ∈ ((R).runBehavioral target.strategy (2 * horizon + 1)).support,
      ∀ who, TerminalAudit.charge observe audit final.state who = 0 := by
    simpa only [rawEvaluation] using clean
  refine ⟨target, ?_, ?_, rawClean, rawStates, ?_⟩
  · exact (target.isSequentialEquilibrium_iff_truncated_of_bounded (R)
      ((raw).decisionInformationAntichain (phaseInitialLaw setup) horizon scheduler) rawCertificate
      ((raw).bounded (phaseInitialLaw setup) horizon scheduler) _).mp targetSE
  · intro final supported control current
    have represented : (normal).state final.state ∈
        (((M).runBehavioral canonical.strategy (2 * horizon + 1)).map History.state).support := by
      rw [← rawStates, PMF.mem_support_map_iff]
      exact ⟨final, supported, rfl⟩
    obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp represented
    rw [current] at same
    exact clear original reached
      { control with execution := (normal).execution control.execution } same
  · calc
      _ = ((R).runBehavioral target.strategy (2 * horizon + 1)).map
          (fun final => (read final.state, base final.state)) := by
        rw [← PMF.bind_pure_comp]
        apply bind_congr_on_support
        intro final supported
        change (TerminalAudit.settlement base observe audit deposit final.state).map
          (fun payoffs => (read final.state, payoffs)) = _
        rw [TerminalAudit.settlement_clean base observe audit deposit final.state
          (rawClean final supported), PMF.pure_map]
        rfl
      _ = ((M).runBehavioral canonical.strategy (2 * horizon + 1)).map
          (fun final => (read final.state, base final.state)) := by
        have paired := congrArg (PMF.map fun state => (read state, base state)) rawStates
        simpa only [PMF.map_comp, Function.comp_def, normalized, normalizedRead] using paired
      _ = _ := law

end Vegas.SequentialPhase
