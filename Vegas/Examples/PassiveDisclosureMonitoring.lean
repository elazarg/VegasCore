/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.DisclosureMonitoring
import Vegas.Pending.ReactiveConformance
import Interaction.MessageMonitoring
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

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

namespace Vegas.Examples.PassiveDisclosureMonitoring

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

open Vegas.Examples.SelectiveAssociation Vegas.Examples.ReactiveAssociationEvidence

def violation (message : Message Player (WitnessedPacket nativeGraph)) : Bool :=
  unsupportedEvidence message.payload

def certifiedEnvelope (bit : Bool) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 0), ⟨.commitment aliceBinding candidate, some (opening bit), some ⟨aliceBinding⟩⟩⟩

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
    (atMostOne : probability ≤ 1) : PMF (Finset (MessageId Player)) :=
  mix probability nonnegative atMostOne
    (PMF.pure {(alice, 0)}) (PMF.pure ∅)

theorem report_sample_law (bit : Bool) (probability : ℝ) (nonnegative : 0 ≤ probability)
    (atMostOne : probability ≤ 1) :
    (partialSample probability nonnegative atMostOne).map (sampledReports bit) =
      mix probability nonnegative atMostOne
        (PMF.pure [certifiedEnvelope bit]) (PMF.pure []) := by
  simp [partialSample, mix_map, PMF.pure_map, sample_finds_report, empty_sample_no_report]

theorem exact_detection_probability (bit : Bool) (probability : ℝ)
    (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1) :
    ((((partialSample probability nonnegative atMostOne).map (sampledReports bit)).map
      (fun reports => !reports.isEmpty)) true).toReal = probability := by
  rw [report_sample_law]
  simp [mix_map, PMF.pure_map, nonnegative]

end Vegas.Examples.PassiveDisclosureMonitoring
