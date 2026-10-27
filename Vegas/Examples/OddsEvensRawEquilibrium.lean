/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensService
import Vegas.Examples.OddsEvensEquilibrium
import Vegas.Game.SequentialPhaseRawPreservation
import Vegas.Pending.PhaseThinnedCollection

/-! # Funded raw equilibrium under positive reaction and inclusion latency -/

noncomputable section

namespace Vegas.Examples.OddsEvensRaw

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

open OddsEvensService

local notation "runtime" => OddsEvensService.runtime
local notation "horizon" => OddsEvensService.horizon
local notation "scheduler" => OddsEvensService.scheduler

def halfRate : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

abbrev evidenceService :=
  EvidenceReportService.thinned (Evidence := PhaseCount.Evidence compiled) halfRate halfRate

/-- Each actual evidence item is collected with probability exactly one quarter. -/
theorem collection_probability (actual : List (PhaseCount.Evidence compiled))
    (evidence : PhaseCount.Evidence compiled) (member : evidence ∈ actual) :
    ((evidenceService.sample actual).toOuterMeasure
      {collected | evidence ∈ collected}).toReal = 1 / 4 := by
  have mass := EvidenceReportService.thinned_collection_mass halfRate halfRate
    actual evidence member
  norm_num [halfRate] at mass
  exact mass

/-- Every intended source equilibrium has a clean raw-runtime realization under
the concrete two-player service and imperfect audit. -/
theorem intended_equilibrium_preserved
    (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium :
      intended.IsSequentialEquilibrium fixture.intended_decision_antichain
        fixture.intended_bounded.wellFoundedHistories
        (fun who final => (fixture.protocolReadout final.state).elim 0
          (fun terminal => OddsEvens.sourceUtility
            (fixture.parameterOutcome (fun _ => ()) terminal) who))) :
    let raw := PhaseCount.rawMenu runtime leaks OddsEvens.bounds
    let observe := app.stateTraffic
    let audit := PhaseCount.audit runtime leaks
      evidenceService.sample
    let base := phaseExclusionBase fixture .sequential runtime leaks
      (fun terminal => OddsEvens.sourceUtility
        (fixture.parameterOutcome (fun _ => ()) terminal))
      (fun who => (fixture.exitTransfers who : ℝ))
    let payoff := GameTheory.Enforcement.TerminalAudit.utility base observe audit (fun _ => 800)
    let settle := TerminalAudit.settlement base observe audit (fun _ => 800)
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler)
        (raw.bounded initial horizon scheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.current.excluded = ∅) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (phaseSourceReadout fixture .sequential runtime leaks final.state, payoffs)) =
        (fixture.intendedModel.runBehavioral intended.strategy
          (instructionCount fixture.program + 1)).map
          (intendedReadoutExclusion fixture (fun _ => ()) OddsEvens.sourceUtility
            (fun who => (fixture.exitTransfers who : ℝ))) := by
  intro raw observe audit base payoff settle
  let : app.FiniteNature (SequentialPhase.phaseInitialLaw fixture) scheduler :=
    (inferInstance : app.FiniteNature initial scheduler)
  obtain ⟨target, rational, clear, noCharges, joint⟩ :=
    SequentialPhase.intended_raw_sequentialEquilibrium_preserved fixture runtime leaks
      OddsEvens.bounds horizon scheduler (fun _ => ())
      OddsEvens.sourceUtility (fun who => (fixture.exitTransfers who : ℝ))
      OddsEvens.wellFormed OddsEvens.independent
      OddsEvens.observable opportunity protectedInclusion completesPlay timely
      (fun _ => 0) (fun _ => 200)
      (fun result who => (OddsEvens.sourceUtility_bounds result who).1)
      (fun result who => (OddsEvens.sourceUtility_bounds result who).2)
      (fun final terminal _ who => le_trans (by norm_num [fixture, OddsEvens.setup, halfRate])
        (OddsEvens.sourceUtility_bounds
          (fixture.parameterOutcome (fun _ => ()) terminal) who).1)
      intended equilibrium OddsEvens.outputValues OddsEvens.inputValues
      OddsEvens.candidateCapacity
      evidenceService
      (fun _ => halfRate.val) (fun _ => halfRate.val) (fun _ => by norm_num [halfRate])
      (PhaseCount.thinnedEvidence_coverage halfRate halfRate)
      (fun _ => 800) (fun _ => by norm_num)
      (fun _ => by norm_num [fixture, OddsEvens.setup, halfRate])
  refine ⟨target, ?_, clear, noCharges, joint⟩
  exact (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial horizon scheduler) _).mpr rational

/-- An actual source and raw sequential equilibrium exist for the funded
two-player game. No uniform-strategy identification is asserted. -/
theorem funded_raw_equilibrium_exists :
    let raw := PhaseCount.rawMenu runtime leaks OddsEvens.bounds
    let observe := app.stateTraffic
    let audit := PhaseCount.audit runtime leaks
      evidenceService.sample
    let base := phaseExclusionBase fixture .sequential runtime leaks
      (fun terminal => OddsEvens.sourceUtility
        (fixture.parameterOutcome (fun _ => ()) terminal))
      (fun who => (fixture.exitTransfers who : ℝ))
    let payoff := GameTheory.Enforcement.TerminalAudit.utility base observe audit (fun _ => 800)
    let settle := TerminalAudit.settlement base observe audit (fun _ => 800)
    ∃ intended : fixture.intendedModel.BehavioralAssessment,
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      intended.IsSequentialEquilibrium fixture.intended_decision_antichain
        fixture.intended_bounded.wellFoundedHistories
        (fun who final => (fixture.protocolReadout final.state).elim 0
          (fun terminal => OddsEvens.sourceUtility
            (fixture.parameterOutcome (fun _ => ()) terminal) who)) ∧
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler)
        (raw.bounded initial horizon scheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.current.excluded = ∅) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (phaseSourceReadout fixture .sequential runtime leaks final.state, payoffs)) =
        (fixture.intendedModel.runBehavioral intended.strategy
          (instructionCount fixture.program + 1)).map
          (intendedReadoutExclusion fixture (fun _ => ()) OddsEvens.sourceUtility
            (fun who => (fixture.exitTransfers who : ℝ))) := by
  intro raw observe audit base payoff settle
  obtain ⟨intended, equilibrium⟩ := OddsEvens.intended_equilibrium_exists
  obtain ⟨target, rational, clear, noCharges, joint⟩ :=
    intended_equilibrium_preserved intended equilibrium
  exact ⟨intended, target, equilibrium, rational, clear, noCharges, joint⟩

end Vegas.Examples.OddsEvensRaw
