/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensRecoveryService
import Vegas.Examples.OddsEvensRecoveryReceipts
import Vegas.Examples.OddsEvensRecoveryCompletion
import Vegas.Examples.OddsEvensRecoveryOpportunity
import Vegas.Examples.OddsEvensFairLaw
import Vegas.Examples.OddsEvensEquilibrium
import Vegas.Game.RecoverySequentialCompilation
import Vegas.Pending.ThinnedCountCollection

/-! # Funded raw equilibrium under positive reaction and inclusion latency -/

noncomputable section

namespace Vegas.Examples.OddsEvensRecoveryRaw

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

open OddsEvensRecoveryService

local notation "rt" => OddsEvensRecoveryService.runtime
local notation "steps" => OddsEvensRecoveryService.horizon
local notation "serviceScheduler" => OddsEvensRecoveryService.scheduler

def halfRate : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

abbrev evidenceService :=
  EvidenceReportService.thinned (Evidence := CountEvidence compiled) halfRate halfRate

/-- Each actual evidence item is collected with probability exactly one quarter. -/
theorem collection_probability (actual : List (CountEvidence compiled))
    (evidence : CountEvidence compiled) (member : evidence ∈ actual) :
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
    let raw := Recovery.rawMenu rt leaks OddsEvens.bounds
    let observe := app.stateTraffic
    let audit := Recovery.countAudit rt leaks
      evidenceService.sample
    let base := recoveryExclusionBase (runtime := rt) (leaks := leaks)
      (fun _ : State simpleExpr fixture.context => ()) OddsEvens.sourceUtility (fun _ => 0)
    let payoff := GameTheory.Enforcement.TerminalAudit.utility base observe audit (fun _ => 800)
    let settle := TerminalAudit.settlement base observe audit (fun _ => 800)
    ∃ target : (raw.information initial steps serviceScheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial steps serviceScheduler)
        (raw.bounded initial steps serviceScheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ ((raw.information initial steps serviceScheduler).runBehavioral
          target.strategy (2 * steps + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.excluded = ∅) ∧
      (∀ final ∈ ((raw.information initial steps serviceScheduler).runBehavioral
          target.strategy (2 * steps + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial steps serviceScheduler).runBehavioral target.strategy
          (2 * steps + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout fixture rt leaks
            (RecoveryProjection.protocolState rt leaks final.state), payoffs)) =
        (fixture.intendedModel.runBehavioral intended.strategy
          (instructionCount fixture.program + 1)).map
          (intendedReadoutExclusion fixture (fun _ => ()) OddsEvens.sourceUtility
            (fun _ => 0)) := by
  intro raw observe audit base payoff settle
  let : app.FiniteNature ((Vegas.initialLaw fixture).map fun native =>
      (⟨native, ∅⟩ : RecoveryState compiled)) serviceScheduler :=
    (inferInstance : app.FiniteNature initial serviceScheduler)
  obtain ⟨target, rational, clear, noCharges, joint⟩ :=
    Vegas.recovery_intended_raw_sequentialEquilibrium_preserved
      (setup := fixture) (runtime := rt) (leaks := leaks) (bounds := OddsEvens.bounds)
      (horizon := steps) (scheduler := serviceScheduler) (fun _ => ())
      OddsEvens.sourceUtility (fun _ => 0)
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
      (thinnedCountEvidence_coverage halfRate halfRate)
      (fun _ => 800) (fun _ => by norm_num)
      (fun _ => by norm_num [fixture, OddsEvens.setup, halfRate])
  refine ⟨target, ?_, clear, noCharges, joint⟩
  exact (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial steps serviceScheduler) _).mpr rational

/-- The actual forced-exit runtime realizes the fair independent-bit source
assessment, with its complete typed/payoff law and expected payoff one hundred. -/
theorem fair_equilibrium_exists :
    let raw := Recovery.rawMenu rt leaks OddsEvens.bounds
    let observe := app.stateTraffic
    let audit := Recovery.countAudit rt leaks
      evidenceService.sample
    let base := recoveryExclusionBase (runtime := rt) (leaks := leaks)
      (fun _ : State simpleExpr fixture.context => ()) OddsEvens.sourceUtility (fun _ => 0)
    let payoff := GameTheory.Enforcement.TerminalAudit.utility base observe audit (fun _ => 800)
    let settle := TerminalAudit.settlement base observe audit (fun _ => 800)
    ∃ target : (raw.information initial steps serviceScheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial steps serviceScheduler)
        (raw.bounded initial steps serviceScheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ ((raw.information initial steps serviceScheduler).runBehavioral
          target.strategy (2 * steps + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.excluded = ∅) ∧
      (∀ final ∈ ((raw.information initial steps serviceScheduler).runBehavioral
          target.strategy (2 * steps + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial steps serviceScheduler).runBehavioral target.strategy
          (2 * steps + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout fixture rt leaks
            (RecoveryProjection.protocolState rt leaks final.state), payoffs)) =
              OddsEvens.uniformJointLaw ∧
      ∀ who, expect (
        ((raw.information initial steps serviceScheduler).runBehavioral target.strategy
          (2 * steps + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout fixture rt leaks
            (RecoveryProjection.protocolState rt leaks final.state), payoffs)))
          (fun realized => realized.2 who) = 100 := by
  intro raw observe audit base payoff settle
  obtain ⟨target, rational, clear, noCharges, joint⟩ :=
    intended_equilibrium_preserved OddsEvens.uniformAssessment (by
      exact OddsEvens.uniformAssessment_equilibrium)
  have sourceLaw := OddsEvens.uniform_source_joint_law
  have actual := joint.trans sourceLaw
  refine ⟨target, rational, clear, noCharges, actual, ?_⟩
  intro who
  rw [actual]
  exact OddsEvens.uniformJointLaw_expected who

end Vegas.Examples.OddsEvensRecoveryRaw
