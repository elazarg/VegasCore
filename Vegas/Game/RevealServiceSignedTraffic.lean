/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceTraffic

/-! # Phase evidence attributed to the signed envelope author

The evidence projection omits the broadcaster. Published envelopes may be
replayed by anyone without accusing their author. Fresh openings are checked
against their public transmission phase and prior ledger. A deployment must
supply authentic phase and prior-publication evidence; envelope signatures alone
do not establish those facts.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Only public phase, prior ledger and signed envelope are authenticated. -/
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

theorem openingTraffic_authored (record : (application setup leaks).TrafficRecord)
    (allowed : openingTraffic setup leaks record) :
    record.input.broadcaster = record.input.envelope.sender := by
  cases call : record.input.envelope.payload.call with
  | commitment | withhold | malformed => simp only [openingTraffic, call] at allowed
  | opening event candidate raw =>
    simp only [openingTraffic, call] at allowed
    obtain ⟨_, _, _, linked⟩ := allowed
    cases node : nodeView (graph setup) event with
    | bind | sample => simp only [node] at linked
    | resolve owner payload binding checks outputEq codeEq =>
      simp only [node] at linked
      exact linked.1.trans linked.2.1.symm

theorem permittedEnvelope_published (record : (application setup leaks).TrafficRecord)
    (published : record.input.envelope.id ∈ record.ledger.map Message.id) :
    permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  classical
  exact decide_eq_true (Or.inl published)

theorem permittedEnvelope_of_traffic (watcher : Player)
    (record : (application setup leaks).TrafficRecord)
    (allowed : permittedTraffic setup leaks watcher record = true) :
    permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  classical
  obtain ⟨_ordinary, published | opening⟩ :=
    (permittedTraffic_iff setup leaks watcher record).mp allowed
  · exact permittedEnvelope_published setup leaks record published
  · have authored := openingTraffic_authored setup leaks record opening
    apply decide_eq_true
    apply Or.inr
    change openingTraffic setup leaks
      { record with input := ⟨record.input.envelope.sender, record.input.envelope⟩ }
    rw [← authored]
    exact opening

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

end Vegas
