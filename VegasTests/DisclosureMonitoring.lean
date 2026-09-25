/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveReadinessRestrictions

/-! # Which observations can detect the selective disclosure?

The existing native witness transmits a certified candidate before including a
different, certificate-free packet. A monitor of the ledger alone misses the
early certificate. A monitor with the network input record can identify the
broadcast, without observing who read it. An ordinary uninformed player's view
does not supply that record.

These are observation and attribution experiments on the actual native prefix.
They implement neither a watcher, a proof-of-transmission service, nor slashing.
The alarms recognize explicit carried certificates only, not every information
channel. Recording the network's broadcaster is an ideal-model fact, not a
cryptographic proof that a particular strategic principal authorized a message.
-/

noncomputable section

namespace VegasTests.DisclosureMonitoring

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open VegasTests.SelectiveAssociation VegasTests.ReactiveAssociationEvidence

/-- An intentionally narrow alarm for certificates carried by Alice's envelopes. -/
def ledgerAlarm (ledger : List (Message Player (WitnessedPacket nativeGraph))) : Bool :=
  ledger.any fun message => message.sender == alice && message.payload.evidence.isSome

/-- Access to the network input record supplies a separate broadcaster identity. -/
def inputAlarm (inputs : List (NetworkInput Player (WitnessedPacket nativeGraph))) : Bool :=
  inputs.any fun input => input.broadcaster == alice && input.envelope.payload.evidence.isSome

theorem pending_certificate_detected (bit : Bool) :
    inputAlarm (first bit).network.publicView.inputs = true ∧
      ledgerAlarm (first bit).network.ledger = false := by
  cases bit <;> exact ⟨rfl, rfl⟩

/-- This state is reached by the first five instructions of the native service,
with the silent Bob response used by the existing readiness experiment. -/
theorem certificate_free_inclusion_keeps_gap (bit : Bool) :
    inputAlarm (includedAfter bit ⟨none⟩).network.publicView.inputs = true ∧
      ledgerAlarm (includedAfter bit ⟨none⟩).network.ledger = false := by
  cases bit <;> exact ⟨rfl, rfl⟩

/-- Detecting transmission does not require a record of the private leak sample. -/
theorem input_alarm_ignores_readers (network : MessageNetwork Player
    (WitnessedPacket nativeGraph)) (who : Player) (selected : Finset (MessageId Player)) :
    inputAlarm (network.learn who selected).publicView.inputs =
      inputAlarm network.publicView.inputs := rfl

def uncertifiedFirst (bit : Bool) : nativeApp.Execution :=
  activatedInitial.respond nativeApp alice
    ⟨some (.submit ⟨⟨.commitment aliceBinding candidate, some ⟨.bool, bit⟩⟩, .none⟩)⟩

theorem no_alarm_for_uncertified_submission (bit : Bool) :
    inputAlarm (uncertifiedFirst bit).network.publicView.inputs = false := by
  cases bit <;> rfl

/-- The certified and uncertified submissions produce identical current inputs
for Carol, while Bob has acquired the certificate in the certified prefix. -/
theorem uninformed_player_same_input (bit : Bool) :
    ((observed bit).recall carol, (observed bit).observe nativeApp carol) =
      ((uncertifiedFirst bit).recall carol, (uncertifiedFirst bit).observe nativeApp carol) := by
  cases bit <;> rfl

/-- No detector using only that complete player input separates these prefixes. -/
theorem no_uninformed_player_detector (bit : Bool) :
    ¬ ∃ detect : List nativeApp.PlayerEntry × nativeApp.PlayerView → Bool,
      detect ((observed bit).recall carol, (observed bit).observe nativeApp carol) = true ∧
      detect ((uncertifiedFirst bit).recall carol,
        (uncertifiedFirst bit).observe nativeApp carol) = false := by
  rintro ⟨detect, detects, quiet⟩
  rw [uninformed_player_same_input bit, quiet] at detects
  cases detects

end VegasTests.DisclosureMonitoring
