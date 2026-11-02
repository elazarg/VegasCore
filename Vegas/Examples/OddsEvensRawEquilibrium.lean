/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensService
import Vegas.Examples.OddsEvensServiceReceipts
import Vegas.Examples.OddsEvensServiceCompletion
import Vegas.Examples.OddsEvensServiceOpportunity
import Vegas.Examples.OddsEvensFairLaw
import Vegas.Examples.OddsEvensEquilibrium
import Vegas.Game.SequentialCompilation
import Vegas.Pending.ThinnedCountCollection

/-! # Funded raw equilibrium under positive reaction and inclusion latency -/

noncomputable section

namespace Vegas.Examples.OddsEvensRaw

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

open OddsEvensService

local notation "rt" => OddsEvensService.runtime
local notation "steps" => OddsEvensService.horizon
local notation "serviceScheduler" => OddsEvensService.scheduler

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

/-- The source, service and audit certificates of the two-player runtime. -/
def specification : Vegas.ClientSpec
    fixture rt leaks Vegas.Examples.OddsEvens.bounds steps serviceScheduler
    (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility (fun _ => 0) where
  finiteNature := by change app.FiniteNature initial serviceScheduler; infer_instance
  finiteSource := inferInstance
  Public := Unit
  signal := Vegas.Examples.OddsEvens.signal
  wellFormed := Vegas.Examples.OddsEvens.wellFormed
  independent := Vegas.Examples.OddsEvens.independent
  observable := Vegas.Examples.OddsEvens.observable
  delay := fun _ => 3
  bound := fun _ => 2
  opportunity := opportunity
  inclusion := protectedInclusion
  completes := completesPlay
  timely := timely
  lowerUtility := fun _ => 0
  upperUtility := fun _ => 200
  lower_le := fun _ terminal _ who => (Vegas.Examples.OddsEvens.sourceUtility_bounds
    (fixture.parameterOutcome (fun _ => ()) terminal) who).1
  le_upper := fun _ terminal _ who => (Vegas.Examples.OddsEvens.sourceUtility_bounds
    (fixture.parameterOutcome (fun _ => ()) terminal) who).2
  exitBelow := fun _ terminal _ who =>
    (Vegas.Examples.OddsEvens.sourceUtility_bounds
      (fixture.parameterOutcome (fun _ => ()) terminal) who).1
  outputValues := Vegas.Examples.OddsEvens.outputValues
  inputValues := Vegas.Examples.OddsEvens.inputValues
  capacity := Vegas.Examples.OddsEvens.candidateCapacity
  evidenceService := evidenceService
  observationRate := fun _ => halfRate.val
  deliveryRate := fun _ => halfRate.val
  delivery_nonnegative := fun _ => by norm_num [halfRate]
  coverage := thinnedCountEvidence_coverage halfRate halfRate
  deposit := fun _ => 800
  deposit_nonnegative := fun _ => by norm_num
  funded := fun _ => by norm_num [fixture, Vegas.Examples.OddsEvens.setup, halfRate]

/-- Every intended source equilibrium has a clean raw-runtime realization under
the concrete two-player service and imperfect audit. -/
theorem intended_equilibrium_preserved
    (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium :
      fixture.IntendedSequentialEquilibrium (fun _ => ()) OddsEvens.sourceUtility intended) :
    let raw := OddsEvens.bounds.rawMenu rt leaks
    let observe := app.stateTraffic
    let audit := (rt).countAudit leaks
      evidenceService.sample
    let base := exclusionBase fixture rt (fun _ : State simpleExpr fixture.context => ())
      OddsEvens.sourceUtility (fun _ => 0) leaks
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
          control.execution.application.config.defaulted = ∅) ∧
      (∀ final ∈ ((raw.information initial steps serviceScheduler).runBehavioral
          target.strategy (2 * steps + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial steps serviceScheduler).runBehavioral target.strategy
          (2 * steps + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout fixture rt leaks final.state, payoffs)) =
        (fixture.intendedModel.runBehavioral intended.strategy
          (instructionCount fixture.program + 1)).map
          (intendedReadoutExclusion fixture (fun _ => ()) OddsEvens.sourceUtility
            (fun _ => 0)) := by
  intro raw observe audit base payoff settle
  let : app.FiniteNature (Vegas.initialLaw fixture) serviceScheduler :=
    (inferInstance : app.FiniteNature initial serviceScheduler)
  obtain ⟨compiled⟩ := Vegas.intended_raw_sequentialEquilibrium_preserved
    specification intended equilibrium
  let target := compiled.assessment
  have rational := compiled.equilibrium
  have clear := compiled.noDefaults
  have noCharges := compiled.noCharges
  have joint := compiled.outcomeLaw
  refine ⟨target, ?_, clear, noCharges, joint⟩
  exact (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial steps serviceScheduler) _).mpr rational

/-- The actual forced-exit runtime realizes the fair independent-bit source
assessment, with its complete typed/payoff law and expected payoff one hundred. -/
theorem fair_equilibrium_exists :
    let raw := OddsEvens.bounds.rawMenu rt leaks
    let observe := app.stateTraffic
    let audit := (rt).countAudit leaks
      evidenceService.sample
    let base := exclusionBase fixture rt (fun _ : State simpleExpr fixture.context => ())
      OddsEvens.sourceUtility (fun _ => 0) leaks
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
          control.execution.application.config.defaulted = ∅) ∧
      (∀ final ∈ ((raw.information initial steps serviceScheduler).runBehavioral
          target.strategy (2 * steps + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial steps serviceScheduler).runBehavioral target.strategy
          (2 * steps + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout fixture rt leaks final.state, payoffs)) =
              OddsEvens.uniformJointLaw ∧
      ∀ who, expect (
        ((raw.information initial steps serviceScheduler).runBehavioral target.strategy
          (2 * steps + 1)).bind
        (fun final => (settle final.state).map fun payoffs =>
          (sourceReadout fixture rt leaks final.state, payoffs)))
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

end Vegas.Examples.OddsEvensRaw
