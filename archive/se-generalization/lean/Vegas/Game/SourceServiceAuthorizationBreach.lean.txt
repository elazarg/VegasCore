/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceSettledEvidence
import Vegas.Game.SourceServiceRiskSlots
import Vegas.Game.SourceServiceCanonicalConformance

/-! # Final rejection of signed authorization breaches

An actual emitted envelope with no valid readiness token cannot receive an
accepting receipt. Neither can an envelope addressed to an event whose actor
differs from its authenticated sender. These immutable packet properties are
independent of private binding material and opening capability.

The emitter attaches tokens from its actual public view. Premature calls can
therefore carry no token, while arbitrary forged token contents are not an
available response. The predicate below checks the emitted token rather than
classifying every off-turn call as forbidden.

At a complete actual settlement, receipt soundness and envelope identity give
the final forbidden verdict. A hypothetical envelope never actually emitted
is not covered: its identifier might name another envelope in the receipts.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Immutable authorization failure read from the signed packet and the
public graph. It does not read send time or a hidden candidate value. -/
def ServiceAuthorizationBreach
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  message.payload.tokenValid = false ∨
    ∃ event, message.payload.call.event? (graph setup) = some event ∧
      (graph setup).actor? event ≠ some message.sender

/-- Actual receipt soundness rules out acceptance of the same emitted
envelope. Identifier equality alone would not establish that identity. -/
theorem ServiceAuthorizationBreach.not_accepted
    {execution : (application setup leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks execution message)
    (breach : ServiceAuthorizationBreach message) :
    (message.id, true) ∉ execution.receipts := by
  intro accepted
  obtain ⟨_, valid, event, named, owned⟩ := facts.accepted_emitted emitted accepted
  rcases breach with invalid | ⟨other, addressed, unauthorized⟩
  · rw [valid] at invalid
    cases invalid
  · cases Option.some.inj (addressed.symm.trans named)
    exact unauthorized owned

/-- At every complete legal settlement, an actually emitted authorization
breach is forbidden. Later responses and scheduler choices are unrestricted. -/
theorem ServiceAuthorizationBreach.forbidden_history
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks control.execution message)
    (breach : ServiceAuthorizationBreach message)
    (complete : control.execution.application.config.cut.Terminal) :
    ((runtime setup).settledRecord leaks control.execution).permits message = false := by
  have rejected := breach.not_accepted (settledFacts_history (initialLaw setup) horizon
    scheduler trace) emitted
  cases named : message.payload.call.event? (graph setup) with
  | none => exact SettledRecord.permits_eq_false_of_none _ message named
  | some event =>
      apply SettledRecord.permits_eq_false_of_settled _ message event named ?_
        (fun accepted => rejected (by
          simpa only [SettledRecord.Accepts, settledRecord] using accepted.1))
      apply (control.execution.application.config.history_exact event).mpr
      rw [complete]
      exact Finset.mem_univ event

/-- A fresh conforming packet has a token for its event and is authored by
that event's actor. Both checks concern the actual emitted envelope. -/
theorem ServiceAuthorizationBreach.not_freshServiceEnvelope
    {message : Message Player (WitnessedPacket (graph setup))}
    (breach : ServiceAuthorizationBreach message)
    (view : PublicView (graph setup)) :
    ¬ (runtime setup).freshServiceEnvelope view message := by
  intro conform
  rcases breach with invalid | ⟨event, named, unauthorized⟩
  · have valid : message.payload.tokenValid = true := by
      apply (WitnessedPacket.tokenValid_iff _).mpr
      cases call : message.payload.call with
      | commitment event candidate =>
          simp only [freshServiceEnvelope, call] at conform
          exact ⟨event, rfl, conform.2.2.2⟩
      | opening event candidate raw =>
          simp only [freshServiceEnvelope, call] at conform
          cases node : nodeView (graph setup) event with
          | bind owner payload outputEq codeEq => simp only [node, and_false] at conform
          | sample payload law outputEq codeEq => simp only [node, and_false] at conform
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [node] at conform
              exact ⟨event, rfl, conform.2.2.2.2.2.2.2.2⟩
      | withhold event =>
          simp only [freshServiceEnvelope, call] at conform
          exact ⟨event, rfl, conform.2.2.2.1⟩
      | malformed raw => simp only [freshServiceEnvelope, call] at conform
    rw [valid] at invalid
    cases invalid
  · obtain ⟨other, addressed, _, owned⟩ :=
      (runtime setup).freshServiceEnvelope_owned view message conform
    cases Option.some.inj (addressed.symm.trans named)
    exact unauthorized owned

variable [Fintype Player]

/-- A real authorization breach cannot be retained at a clear legal risk-menu
activation. Initialized slot invariants supply canonical packet conformance. -/
theorem serviceAuthorizationBreach_risk_excluded
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (breach : ServiceAuthorizationBreach
      ⟨(who, execution.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit execution.application who material) who
          (execution.network.known who) material⟩) :
    response ∉ bounds.riskActions (runtime setup) leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) := by
  intro member
  rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear] at member
  have persistent := ((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_history bounds bound _ trace who persistent
  obtain ⟨event, action, turn, _, _, timely, unrecorded, _, decided⟩ :=
    bounds.canonicalActions_submission (runtime setup) leaks who _ _ response member material
      transmission
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have fresh := canonicalSlot_fresh_of_used rawTrace who atTurn slots event turn unrecorded
  have conform := canonicalServiceDecision_freshServiceEnvelope rawTrace event turn timely fresh
    action material (by rw [← decided]; exact transmission)
  exact breach.not_freshServiceEnvelope execution.application.publicView conform

end Vegas
