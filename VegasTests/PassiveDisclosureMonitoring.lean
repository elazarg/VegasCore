/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.DisclosureMonitoring
import Vegas.Pending.ReactiveConformance
import Interaction.MessageMonitoring
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Detecting the native candidate leak through an ordinary sampled view

The alarm inspects only leaked packets and the ledger. It permits an opening
certificate matching its ordinary opening call, but rejects certificates on
other call bodies. Every compiler decision satisfies this certificate shape
discipline, including failure, withholding, and guard-aware disclosure.

The actual selective-association certificate is reportable from Bob's sampled
view while absent from the ledger. A separate sample in Carol's information
position detects the same packet with exactly its sampling probability. This
is an observation experiment, not an inserted watchdog, report-delivery or
slashing service, nor a proof that all conforming traffic is strategically safe.
In particular the alarm checks certificate shape, not emission time.
-/

noncomputable section

namespace VegasTests.PassiveDisclosureMonitoring

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

open VegasTests.SelectiveAssociation VegasTests.ReactiveAssociationEvidence

def violation (message : Message Player (WitnessedPacket nativeGraph)) : Bool :=
  unsupportedEvidence message.payload

def certifiedEnvelope (bit : Bool) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 0), ⟨.commitment aliceBinding candidate, some (opening bit)⟩⟩

theorem actual_bob_report (bit : Bool) :
    ((observed bit).observe nativeApp bob).messages.reports violation =
      [certifiedEnvelope bit] := by
  cases bit <;> rfl

theorem ledger_does_not_report (bit : Bool) :
    ({ leaked := [], ledger := (first bit).network.ledger } :
      MessageNetwork.PlayerView Player (WitnessedPacket nativeGraph)).reports violation = [] := rfl

theorem report_survives_certificate_free_inclusion (bit : Bool) :
    ((includedAfter bit ⟨none⟩).observe nativeApp bob).messages.reports violation =
      [certifiedEnvelope bit] := by
  cases bit <;> rfl

/-- Sampling the foreign pending packet uses only the ordinary observation
operation; this is Carol's information position, not an added runtime actor. -/
def sampledReports (bit : Bool) (selected : Finset (MessageId Player)) :
    List (Message Player (WitnessedPacket nativeGraph)) :=
  (((first bit).network.learn carol selected).observe carol).reports violation

theorem sample_finds_report (bit : Bool) :
    sampledReports bit {(alice, 0)} = [certifiedEnvelope bit] := by
  cases bit <;> rfl

theorem empty_sample_no_report (bit : Bool) : sampledReports bit ∅ = [] := by
  rw [sampledReports, MessageNetwork.learn_empty]
  rfl

def partialSample (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMostOne : probability ≤ 1) : FinDist (Finset (MessageId Player)) :=
  FinDist.mix probability nonnegative atMostOne
    (FinDist.pure {(alice, 0)}) (FinDist.pure ∅)

theorem report_sample_law (bit : Bool) (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMostOne : probability ≤ 1) :
    (partialSample probability nonnegative atMostOne).map (sampledReports bit) =
      FinDist.mix probability nonnegative atMostOne
        (FinDist.pure [certifiedEnvelope bit]) (FinDist.pure []) := by
  simp [partialSample, FinDist.map_mix, sample_finds_report, empty_sample_no_report]

theorem exact_detection_probability (bit : Bool) (probability : ℝ)
    (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1) :
    (((partialSample probability nonnegative atMostOne).map (sampledReports bit)).map
      (fun reports => !reports.isEmpty)).prob true = probability := by
  rw [report_sample_law]
  simp [FinDist.map_mix, FinDist.prob_mix, FinDist.prob_pure_eq_ite]

end VegasTests.PassiveDisclosureMonitoring
