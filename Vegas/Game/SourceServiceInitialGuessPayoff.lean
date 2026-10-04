/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstInputTerminalLaw
import Vegas.Game.SourceServiceWithholdingGuessBound
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # The fixed terminal payoff for an initialized publication guess

The parameter is read from the actual immutable input table at the terminal
configuration. Along every native continuation it is the same selected initial
parameter as at its starting history. This makes the payoff in a continuation
context independent of which hidden history the context sampled.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The actual initial parameter and actual public publication determine the
terminal guessing payoff. Neither is supplied by a source witness. -/
def sourceInitialPublicationGuessValue
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (parameter : State L setup.context → Bool) (event : (graph setup).EventId)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .publication payload)
    (state : (application setup leaks).ProtocolState) : ℝ :=
  sourcePublicationGuessValue setup leaks event payload outputEq
    (state.elim false fun control =>
      (sourceInitialReadout setup control.execution.application.config).elim false parameter) state

variable [Fintype Player]

open Classical in
/-- The same real initial readout persists through every native terminal
continuation, including arbitrary further packets and foreign policies. -/
theorem sourceInitialPublicationGuess_continuation_value_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (parameter : State L setup.context → Bool) (event : (graph setup).EventId)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .publication payload)
    (profile : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (control : (application setup leaks).Control) (current : history.state = some control)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : Player → ℝ) (who : Player) :
    let high := (sourceInitialReadout setup control.execution.application.config).elim false
      parameter
    let law := (menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
      (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories profile history
    expect law (fun final => TerminalAudit.utility
      (fun state _ => sourceInitialPublicationGuessValue setup leaks parameter event payload
        outputEq state) ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit final.state who) =
    expect law (fun final => TerminalAudit.utility
      (fun state _ => sourcePublicationGuessValue setup leaks event payload outputEq high state)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit final.state who) := by
  intro high law
  let model := menu.information (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  have runner := model.runBehavioralTerminalFrom_eq_remaining certificate profile
    (menu.bounded (initialLaw setup) horizon scheduler) history
  apply expect_congr_on_support
  intro final supported
  have path := (menu.protocol (initialLaw setup) horizon scheduler).runRandomizedFor_reachesWithin
    (model.randomizedChooser profile) (2 * horizon + 1 - history.trace.length) history final
      (by
        change final ∈ (model.runBehavioralFrom profile
          (2 * horizon + 1 - history.trace.length) history).support
        rw [← runner]
        exact supported)
  cases finalState : final.state with
  | none =>
      simp only [TerminalAudit.utility, sourceInitialPublicationGuessValue,
        sourcePublicationGuessValue, Option.elim_none]
  | some after =>
      have same := sourceInitialReadout_reaches (initialLaw setup) horizon scheduler
        (menu.reaches_raw (initialLaw setup) horizon scheduler path) control after current
        finalState
      simp only [TerminalAudit.utility, sourceInitialPublicationGuessValue,
        Option.elim_some, same]
      rfl

end Vegas
