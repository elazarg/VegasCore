/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePacketEvidence
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventCommitmentBinding

/-! # Sound carried opening evidence in the native reactive runtime

All raw responses, passive leaks, forwarding, inclusion failures, and later
continuations preserve the truth of every opening certificate. The fact is
about its candidate, independently of event readiness or accepted association.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem openingFactInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (fact : OpeningFact graph) :
    (runtime.reactiveApplication leaks).Invariant fact.Holds where
  submit state who material valid := by
    have fixed : state.candidates.lookup fact.handle ≠ .fresh := by
      rw [valid]
      simp
    have registered : (material.call.register state who).candidates.lookup fact.handle =
        state.candidates.lookup fact.handle := by
      rw [material.call.register_eq]
      cases material.call.registrationCommand who with
      | none => rfl
      | some command => exact privateStep_lookup_of_not_fresh state who command _ fixed
    exact (submitStep_lookup_of_not_fresh _ who material.call.packet fact.handle
      (by rwa [registered])).trans (registered.trans valid)
  handle state message next valid accepted := by
    have fixed : state.candidates.lookup fact.handle ≠ .fresh := by
      rw [valid]
      simp
    exact (handle_lookup_of_not_fresh runtime state next
      ⟨message.id, message.payload.call⟩ fact.handle fixed accepted).trans valid
  environment state command next valid reached := by
    change next.candidates.lookup fact.handle = .openable fact.raw
    rw [(environmentStep_tables runtime state next command reached).2]
    exact valid

/-- Issuance and forwarding instantiate the generic all-history evidence theorem. -/
def packetEvidence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).PacketEvidence where
  Fact := OpeningFact graph
  valid state fact := fact.Holds state
  decode packet := packet.evidence.toList
  persists := runtime.openingFactInvariant leaks
  issued state who known material received fact certified := by
    change fact ∈ (material.emit state who known).evidence.toList at certified
    exact material.emit_sound state who known (by
      intro message member fact evidence
      apply received message member fact
      simp [evidence]) fact (by simpa using certified)

/-- One response may fix a fresh commitment and disclose its authentic opening.
No preparation turn or intervening inclusion is required. -/
theorem reactive_commitment_disclosure (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (serial : Nat) (raw : Raw L)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let fact : OpeningFact graph := ⟨(who, .prepared serial), raw⟩
    let submission : WitnessedSubmission graph :=
      ⟨⟨.commitment event fact.handle, some raw⟩, .owned fact⟩
    (execution.respond (runtime.reactiveApplication leaks) who
      ⟨some (.submit submission)⟩).network.pending = execution.network.pending ++
        [⟨(who, execution.network.nextSerial who),
          ⟨.commitment event fact.handle, some fact⟩⟩] := by
  let fact : OpeningFact graph := ⟨(who, .prepared serial), raw⟩
  let call : Submission graph := ⟨.commitment event fact.handle, some raw⟩
  let state := submitStep (call.register execution.application who) who call.packet
  have valid : fact.Holds state := by
    change (submitStep (call.register execution.application who) who call.packet).candidates.lookup
      (who, .prepared serial) = .openable raw
    simpa [call, fact, Submission.register, submitStep] using
      execution.application.candidates.lookup_freeze_prepare who (.prepared serial) raw fresh
  have verified : state.candidates.verify fact.handle raw = true :=
    (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr valid
  change execution.network.pending ++
    [⟨(who, execution.network.nextSerial who),
      (WitnessedSubmission.mk call (.owned fact)).emit state who
        (execution.network.known who)⟩] = _
  simp [WitnessedSubmission.emit, verified, call, fact]

end Vegas.EventGraphRuntime
