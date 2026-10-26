/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseServiceEquilibrium
import Vegas.Game.SequentialPhasePaymentPreservation
import Vegas.Game.PhaseCash

/-! # Executable cash preservation for private Boolean publication

The existing four-command service satisfies the physical assumptions on every
legal raw history. Zero valuation and zero declared exit cash instantiate
the monetary theorem. The original private Boolean draw determines actual
receipts of two or zero, retained jointly with its original typed input.
-/

noncomputable section

namespace Vegas.Examples.SequentialPhaseService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement

theorem zeroValuation_paymentUtility_eq :
    program.parameterPaymentUtility (fun (_ : Unit × PublicOutcome program) _ => 0) =
      sourceUtility := by
  funext result who
  rw [parameterPaymentUtility, zero_add, sourceUtility_eq_programTransfer]

/-- A genuine source equilibrium produces an audited raw equilibrium with the
same joint original input, full terminal state, public result and cash vector. -/
theorem funded_raw_cash_equilibrium_exists :
    let initial := SequentialPhase.phaseInitialLaw setup
    let raw := PhaseCount.rawMenu runtime leaks bounds
    let observe := app.stateTraffic
    let audit := PhaseCount.audit runtime leaks
      (EvidenceReportService.complete (PhaseCount.Evidence compiled)).sample
    let base := fun state who => (phaseCash setup .sequential runtime leaks state who : ℝ)
    let payoff := TerminalAudit.utility base observe audit (fun _ => 3)
    ∃ intended : setup.intendedModel.BehavioralAssessment,
      ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
        intended.IsSequentialEquilibrium setup.intended_decision_antichain
          setup.intended_bounded.wellFoundedHistories
          (fun who final => (setup.protocolReadout final.state).elim 0 (fun terminal =>
            sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who)) ∧
        target.IsSequentialEquilibrium
          (raw.decisionInformationAntichain initial horizon scheduler)
          (raw.bounded initial horizon scheduler).wellFoundedHistories
          (fun who final => payoff final.state who) ∧
        (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral target.strategy
            (2 * horizon + 1)).support, ∀ control, final.state = some control →
          control.execution.application.current.excluded = ∅) ∧
        (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral target.strategy
            (2 * horizon + 1)).support, ∀ who,
          TerminalAudit.charge observe audit final.state who = 0) ∧
        ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (TerminalAudit.settlement base observe audit (fun _ => 3)
            final.state).map fun receipts => TerminalObservation.read setup
              (phaseSourceReadout setup .sequential runtime leaks final.state) receipts) =
          (setup.intendedModel.runBehavioral intended.strategy
            (instructionCount program + 1)).map (fun final =>
              TerminalObservation.read setup (setup.protocolReadout final.state)
                (fun who => (setup.cash ∅ (setup.protocolReadout final.state) who : ℝ))) := by
  intro initial raw observe audit base payoff
  let : app.FiniteNature (SequentialPhase.phaseInitialLaw setup) scheduler :=
    (inferInstance : app.FiniteNature Vegas.Examples.SequentialPhaseService.initial scheduler)
  obtain ⟨intended, equilibrium⟩ := intended_equilibrium_exists
  have paymentEq : setup.program.parameterPaymentUtility
      (fun (_ : Unit × PublicOutcome program) _ => 0) = sourceUtility :=
    zeroValuation_paymentUtility_eq
  have paymentEquilibrium := equilibrium
  rw [← paymentEq] at paymentEquilibrium
  obtain ⟨target, rational, clear, clean, _utilityLaw, cash⟩ :=
    SequentialPhase.intended_raw_programPayments_preserved setup leaks bounds horizon scheduler
      (fun _ => (() : Unit))
      (fun (_ : Unit × PublicOutcome program) (_ : Player) => 0) (fun _ => 0)
      (fun who => (setup.exitTransfers who : ℝ))
      wellFormed independent observable opportunity protectedInclusion completesPlay timely
      (fun _ => 0) (fun _ => 2)
      (fun result who => by
        rw [paymentEq]
        exact (sourceUtility_bounds result who).1)
      (fun result who => by
        rw [paymentEq]
        exact (sourceUtility_bounds result who).2)
      (fun final terminal _ who => by
        rw [paymentEq]
        simpa only [setup, Int.cast_zero, zero_add] using
          (sourceUtility_bounds (setup.parameterOutcome (fun _ => ()) terminal) who).1)
      intended paymentEquilibrium outputValues inputValues candidateCapacity
      (EvidenceReportService.complete (PhaseCount.Evidence compiled))
      (fun _ => 1) (fun _ => 1) (fun _ => by norm_num) PhaseCount.completeEvidence_coverage
      (fun _ => 3) (fun _ => by norm_num) (fun _ => by norm_num [setup])
  have canonicalCash := cash
  rw [← phaseCash_cast_eq_base setup .sequential runtime leaks] at canonicalCash
  have baseEq : phaseExclusionBase setup .sequential (Vegas.runtime setup) leaks
      (fun terminal => setup.program.parameterPaymentUtility
        (fun (_ : Unit × PublicOutcome program) (_ : Player) => 0)
        (setup.parameterOutcome (fun _ => (() : Unit)) terminal))
      (fun who => 0 + (setup.exitTransfers who : ℝ)) = base := by
    unfold base
    rw [phaseCash_cast_eq_base]
    congr 1
    · funext terminal who
      exact zero_add _
    · funext who
      exact zero_add _
  refine ⟨intended, target, equilibrium, ?_, clear, clean, ?_⟩
  · rw [baseEq] at rational
    exact (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
      (raw.bounded initial horizon scheduler) _).mpr rational
  · refine canonicalCash.trans ?_
    apply congrArg (fun reader => (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount program + 1)).map reader)
    funext final
    apply congrArg (TerminalObservation.read setup _)
    funext who
    symm
    rw [sourceCash_cast, ite_eq_right (Finset.notMem_empty _)]

end Vegas.Examples.SequentialPhaseService
