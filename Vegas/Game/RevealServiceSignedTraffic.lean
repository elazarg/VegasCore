/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceTraffic

/-! # A send-time rule attributed to the signed envelope author

The rule omits the broadcaster. Published envelopes may be replayed by anyone
without accusing their author. Fresh openings are checked against their
transmission phase and prior ledger. No audit verdict uses this rule: it is a
proof device, and in a reveal-only graph its breach breaches the service rule
(`Vegas.permittedEnvelope_of_permittedService`), which dooms the author at
settlement.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The public phase, prior ledger and signed envelope of a transmission. -/
abbrev EnvelopeEvidence :=
  (application setup leaks).PublicObservation ×
    List (Message Player (application setup leaks).Payload) ×
      Message Player (application setup leaks).Payload

def envelopeEvidence (record : (application setup leaks).TrafficRecord) :
    EnvelopeEvidence setup leaks :=
  (record.observation, record.ledger, record.input.envelope)

open Classical in
def permittedEnvelope (evidence : EnvelopeEvidence setup leaks) : Bool :=
  decide (evidence.2.2.id ∈ evidence.2.1.map Message.id ∨
    openingTraffic setup leaks ⟨evidence.1, evidence.2.1,
      ⟨evidence.2.2.sender, evidence.2.2⟩⟩)

theorem permittedEnvelope_iff (record : (application setup leaks).TrafficRecord)
    (authored : record.input.broadcaster = record.input.envelope.sender) :
    permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true ↔
      record.input.envelope.id ∈ record.ledger.map Message.id ∨
        openingTraffic setup leaks record := by
  classical
  change decide (_ ∨ openingTraffic setup leaks
    { record with input := ⟨record.input.envelope.sender, record.input.envelope⟩ }) = true ↔ _
  simp only [decide_eq_true_eq]
  rw [← authored]
  rfl

theorem permittedEnvelope_forbidden (watcher : Player)
    (record : (application setup leaks).TrafficRecord)
    (ordinary : record.input.broadcaster ≠ watcher)
    (authored : record.input.broadcaster = record.input.envelope.sender)
    (forbidden : permittedTraffic setup leaks watcher record = false) :
    permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
  cases verdict : permittedEnvelope setup leaks (envelopeEvidence setup leaks record) with
  | false => rfl
  | true =>
    have allowed := (permittedTraffic_iff setup leaks watcher record).mpr
      ⟨ordinary, (permittedEnvelope_iff setup leaks record authored).mp verdict⟩
    rw [forbidden] at allowed
    cases allowed

/-- In a reveal-only graph the signed-envelope rule is no stricter than the
service rule: a packet the service rule permits is published or a conforming
opening. A breach of the signed-envelope rule therefore breaches the service
rule. -/
theorem permittedEnvelope_of_permittedService (reveals : setup.program.RevealOnly)
    (view : (application setup leaks).PublicObservation)
    (ledger : List (Message Player (application setup leaks).Payload))
    (message : Message Player (application setup leaks).Payload)
    (allowed : (runtime setup).permittedServiceEnvelope view ledger message = true) :
    permittedEnvelope setup leaks (view, ledger, message) = true := by
  classical
  rw [(runtime setup).permittedServiceEnvelope_iff] at allowed
  unfold permittedEnvelope
  apply decide_eq_true
  rcases allowed with published | ⟨_, fresh⟩
  · exact Or.inl published
  · exact Or.inr (openingTraffic_of_fresh setup leaks reveals view ledger message fresh)

end Vegas
