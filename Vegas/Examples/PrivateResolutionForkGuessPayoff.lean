/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkWithholdingValue
import Vegas.Game.SourceServiceInitialGuessPayoff
import GameTheoryExtensions.Analysis.Protocol.TerminalPayoffCongruence

/-! # The fixture's actual public utility and the fixed guessing payoff

Every real completed native endpoint reads the same initialized type and Bob's
actual public publication. The runtime guessing payoff is therefore the actual
fixture utility, including its real sampled charge, under arbitrary continuations.
This does not certify a particular native scheduler or incoming information fiber.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph))

/-- At an actual complete endpoint, the guessing payoff is precisely Bob's
original initial-parameter/public-outcome payoff. -/
theorem native_bob_initial_guess_value_eq
    (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal)
    (initial : State simpleExpr setup.context)
    (read : sourceInitialReadout setup control.execution.application.config = some initial) :
    baseUtility setup leaks lowFalseSourceUtility (some control) bob =
      sourceInitialPublicationGuessValue setup leaks typeParameter bobResolution .bool rfl
        (some control) := by
  rw [native_bob_public_utility_eq leaks control terminal initial read]
  simp only [sourceInitialPublicationGuessValue, Option.elim_some, read]

open Classical in
/-- The two actual terminal utility functions agree on every legal native
terminal history. Real complete play and initialized provenance supply the facts. -/
theorem native_bob_initial_guess_terminal_payoff_eq
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup)) (deposit : Player → ℝ)
    (final : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (terminal : (menu.protocol (initialLaw setup) horizon scheduler).terminal final.state) :
    TerminalAudit.utility (baseUtility setup leaks lowFalseSourceUtility)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample)
      deposit final.state bob =
    TerminalAudit.utility
      (fun state _ => sourceInitialPublicationGuessValue setup leaks typeParameter bobResolution
        .bool rfl state) ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks backend.sample) deposit final.state bob := by
  cases current : final.state with
  | none =>
      simp only [TerminalAudit.utility, baseUtility, sourceReadout,
        sourceInitialPublicationGuessValue, sourcePublicationGuessValue,
        Option.bind_none, Option.elim_none]
  | some control =>
      have rawTrace := current ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
      have complete := completes control rawTrace (current ▸ terminal)
      obtain ⟨initial, _selected, read⟩ := sourceInitialReadout_history setup leaks horizon
        scheduler control rawTrace
      have value := native_bob_initial_guess_value_eq leaks control complete initial read
      simpa only [TerminalAudit.utility, current] using congrArg (fun base =>
        base - TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks backend.sample) (some control) bob * deposit bob) value

open Classical in
/-- Bob's ordinary whole-policy rationality is the same predicate for the
actual original public payoff and the fixed runtime guessing payoff. -/
theorem native_bob_guess_rationality_iff
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup)) (deposit : Player → ℝ)
    (assessment : (menu.information (initialLaw setup) horizon scheduler).BehavioralAssessment)
    (site : (menu.information (initialLaw setup) horizon scheduler).InformationSite bob) :
    let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext certificate site
      (fun final => TerminalAudit.utility (baseUtility setup leaks lowFalseSourceUtility)
        ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) deposit final.state bob)) ↔
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext certificate site
      (fun final => TerminalAudit.utility
        (fun state _ => sourceInitialPublicationGuessValue setup leaks typeParameter bobResolution
          .bool rfl state) ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks backend.sample) deposit final.state bob)) := by
  intro certificate
  exact assessment.isSequentiallyRationalAt_iff_of_terminal_payoff_eq certificate site _ _
    (native_bob_initial_guess_terminal_payoff_eq leaks menu horizon scheduler completes
      backend deposit)

end Vegas.PrivateResolutionFork
