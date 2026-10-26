/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseDelayedService
import Vegas.Examples.SequentialPhaseServiceEquilibrium

/-! # Funded raw equilibrium under positive reaction and inclusion latency -/

noncomputable section

namespace Vegas.Examples.SequentialPhaseDelayedService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

/-- The configured positive-latency service admits an actual funded raw
sequential equilibrium with the intended readout and settled-payoff law,
no physical exits, and no audit charges. -/
theorem funded_raw_equilibrium_exists :
    let raw := PhaseCount.rawMenu runtime leaks SequentialPhaseService.bounds
    let observe := app.stateTraffic
    let audit := PhaseCount.audit runtime leaks
      (Interaction.EvidenceReportService.complete (PhaseCount.Evidence compiled)).sample
    let base := phaseExclusionBase fixture .sequential runtime leaks
      (fun terminal => SequentialPhaseService.sourceUtility
        (fixture.parameterOutcome (fun _ => ()) terminal))
      (fun who => (fixture.exitTransfers who : ℝ))
    let payoff := GameTheory.Enforcement.TerminalAudit.utility base observe audit (fun _ => 3)
    let settle := TerminalAudit.settlement base observe audit (fun _ => 3)
    ∃ intended : fixture.intendedModel.BehavioralAssessment,
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      intended.IsSequentialEquilibrium fixture.intended_decision_antichain
        fixture.intended_bounded.wellFoundedHistories
        (fun who final => (fixture.protocolReadout final.state).elim 0
          (fun terminal => SequentialPhaseService.sourceUtility
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
          (intendedReadoutExclusion fixture (fun _ => ()) SequentialPhaseService.sourceUtility
            (fun who => (fixture.exitTransfers who : ℝ))) := by
  intro raw observe audit base payoff settle
  let : app.FiniteNature (SequentialPhase.phaseInitialLaw fixture) scheduler :=
    (inferInstance : app.FiniteNature initial scheduler)
  obtain ⟨intended, equilibrium⟩ := SequentialPhaseService.intended_equilibrium_exists
  obtain ⟨target, rational, clear, noCharges, joint⟩ :=
    SequentialPhase.intended_raw_sequentialEquilibrium_preserved fixture runtime leaks
      SequentialPhaseService.bounds horizon scheduler (fun _ => ())
      SequentialPhaseService.sourceUtility (fun who => (fixture.exitTransfers who : ℝ))
      SequentialPhaseService.wellFormed SequentialPhaseService.independent
      SequentialPhaseService.observable opportunity protectedInclusion completesPlay timely
      (fun _ => 0) (fun _ => 2)
      (fun result who => (SequentialPhaseService.sourceUtility_bounds result who).1)
      (fun result who => (SequentialPhaseService.sourceUtility_bounds result who).2)
      (fun final terminal _ who => le_trans (by norm_num [fixture, SequentialPhaseService.setup])
        (SequentialPhaseService.sourceUtility_bounds
          (fixture.parameterOutcome (fun _ => ()) terminal) who).1)
      intended equilibrium SequentialPhaseService.outputValues SequentialPhaseService.inputValues
      SequentialPhaseService.candidateCapacity
      (Interaction.EvidenceReportService.complete (PhaseCount.Evidence compiled))
      (fun _ => 1) (fun _ => 1) (fun _ => by norm_num) PhaseCount.completeEvidence_coverage
      (fun _ => 3) (fun _ => by norm_num)
      (fun _ => by norm_num [fixture, SequentialPhaseService.setup])
  refine ⟨intended, target, equilibrium, ?_, clear, noCharges, joint⟩
  exact (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial horizon scheduler) _).mpr rational

end Vegas.Examples.SequentialPhaseDelayedService
