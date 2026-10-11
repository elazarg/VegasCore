/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
import Vegas.Examples.LateOpeningRuntimePreservingSettlement
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditSettlement

/-! # Preservation of realized settlement under all-or-none traffic sampling

Positive sampling has the full audit's zero-charge states. Reproducing the
source's joint store and realized payoff law forces every actual deduction to
vanish, so the same profile reproduces that law under full audit at scaled deposits.
This is a law-preservation implication, without an equilibrium transfer claim.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAllOrNonePreservingSettlement

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility
  LateOpeningRuntimePreservingLaw LateOpeningRuntimeAllOrNoneTrafficAudit

/-- Positive all-or-none sampling has exactly the full audit's zero-charge states,
including states with public binding omissions. -/
theorem charge_zero_iff (probability : ℝ) (positive : 0 < probability)
    (bounded : probability ≤ 1) (state : app.ProtocolState) (who : Player) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks
          (sample probability positive.le bounded)) state who = 0 ↔
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        state who = 0 := by
  cases state with
  | none =>
      change TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
          app.sampledTrafficAudit (fun traffic => ((record, traffic.envelope) : Evidence))
            (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
              (sample probability positive.le bounded)) none who = 0 ↔
        TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
            app.sampledTrafficAudit (fun traffic => ((record, traffic.envelope) : Evidence))
              (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
                (fun actual => PMF.pure actual)) none who = 0
      rw [serviceAudit_charge_none, serviceAudit_charge_none]
  | some control =>
      rw [charge]
      by_cases missing : control.execution.application.publicView.missedBindingBy who = true
      · rw [ite_eq_left missing, full_charge_of_omission control who missing]
      · have clear := Bool.eq_false_iff.mpr missing
        simp only [clear, Bool.false_eq_true, ↓reduceIte, mul_eq_zero, positive.ne', false_or]

/-- Reproducing the source's realized joint law makes both audits' deductions vanish;
the unchanged profile realizes that law under full audit at scaled deposits. -/
theorem preserving_implies_full
    (probability : ℝ) (positive : 0 < probability) (bounded : probability ≤ 1)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (reward forfeit : ℝ)
    (deposit : Player → ℝ)
    (profile : ∀ who, (LateOpeningRuntimeGame.model weight nonnegative).BehavioralPolicy who)
    (same : nativeTerminalLaw weight nonnegative reward forfeit
      (sample probability positive.le bounded) deposit profile = safeTerminalLaw reward) :
    nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      (fun who => probability * deposit who) profile = safeTerminalLaw reward := by
  classical
  refine Eq.trans ?_ same
  unfold nativeTerminalLaw
  apply bind_congr_on_support _
  intro history reached
  have sampledZero (who : Player) (nonzero : deposit who ≠ 0) :=
    LateOpeningRuntimePreservingSettlement.history_charge_zero weight nonnegative reward forfeit
      (sample probability positive.le bounded) deposit profile same history reached who
        nonzero
  have sampledDeductions (who : Player) :
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks
          (sample probability positive.le bounded)) history.state who * deposit who = 0 := by
    by_cases zero : deposit who = 0
    · rw [zero, mul_zero]
    · rw [sampledZero who zero, zero_mul]
  have fullDeductions (who : Player) :
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          history.state who * (probability * deposit who) = 0 := by
    by_cases zero : deposit who = 0
    · rw [zero, mul_zero, mul_zero]
    · rw [(charge_zero_iff probability positive bounded history.state who).mp
        (sampledZero who zero), zero_mul]
  have sampledClean := (TerminalAudit.settlement_eq_pure_iff_zero_deductions
    (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (sample probability positive.le bounded))
    deposit history.state).mpr sampledDeductions
  have fullClean := (TerminalAudit.settlement_eq_pure_iff_zero_deductions
    (nativeBaseUtility reward forfeit)
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
    (fun who => probability * deposit who) history.state).mpr fullDeductions
  change (TerminalAudit.settlement _ _ _ _ _).map _ =
    (TerminalAudit.settlement _ _ _ _ _).map _
  rw [fullClean, sampledClean]

end Vegas.Examples.LateOpeningRuntimeAllOrNonePreservingSettlement
