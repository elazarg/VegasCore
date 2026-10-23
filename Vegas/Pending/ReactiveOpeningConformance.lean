/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.ReactiveSafety
import Interaction.ReactiveReceipts
import Vegas.Pending.EventBindingInvariant

/-! # Canonical certified opening packets

The public format admits only an opening with its exactly matching certificate.
Accepted packets in this format identify the current binding's fixed value.
Owned and forwarded requests for that certificate have the same semantic normal
form, without assuming an empty known-packet list or a particular value type.

This is a packet-format theorem. Readiness, deadlines and source conformance
remain separate obligations. In particular, a truthful opening can still yield
guard-rejected publication failure; identifying it with a source opening requires
guard-free code or a proof that the publication checks succeed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The packet admits neither missing/mismatching evidence nor another call kind.
It does not inspect a private expected value, event phase, or source strategy. -/
def certifiedOpening (packet : WitnessedPacket graph) : Bool :=
  match packet.call, packet.evidence with
  | .opening _ candidate raw, some fact => decide (fact = ⟨candidate, raw⟩)
  | _, _ => false

theorem certifiedOpening_iff (packet : WitnessedPacket graph) :
    certifiedOpening packet = true ↔
      ∃ event candidate raw token, packet =
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩, token⟩ := by
  constructor
  · intro conforming
    rcases packet with ⟨call, evidence, token⟩
    cases call <;> cases evidence <;>
      simp only [certifiedOpening, Bool.false_eq_true, decide_eq_true_eq] at conforming
    rename_i event candidate raw fact
    subst fact
    exact ⟨event, candidate, raw, token, rfl⟩
  · rintro ⟨event, candidate, raw, token, rfl⟩
    simp only [certifiedOpening, decide_true]

theorem disclosureSubmission_certified (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (owned : candidate.1 = who)
    (fixed : state.candidates.lookup candidate = .openable raw) :
    certifiedOpening ((disclosureSubmission (.opening event candidate raw)).emit
      state who known) = true := by
  have verified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr fixed
  simp only [disclosureSubmission, WitnessedSubmission.emit, owned, verified,
    and_self, ↓reduceIte, certifiedOpening, decide_true]

private theorem opening_submit_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player) (submission : WitnessedSubmission graph)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (opening : submission.call.packet = .opening event candidate raw) :
    (runtime.reactiveApplication leaks).submit state who submission = state := by
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at opening
  subst packet
  cases material <;> rfl

/-- Honest owned emission remains certified after semantic normalization, even
when the representative is a forwarding request for a previously known fact. -/
theorem normalized_disclosureSubmission_certified (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (owned : candidate.1 = who)
    (fixed : state.candidates.lookup candidate = .openable raw) :
    certifiedOpening
      (((disclosureSubmission (.opening event candidate raw)).normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who) known).emit
          state who known) = true := by
  have packet := WitnessedSubmission.normalizeReactive_emit runtime leaks state who known
    (disclosureSubmission (.opening event candidate raw))
  have unchanged := opening_submit_eq runtime leaks state who
    (disclosureSubmission (.opening event candidate raw)) event candidate raw rfl
  change (runtime.reactiveApplication leaks).submit state who
    (disclosureSubmission (.opening event candidate raw)) = state at unchanged
  change ((disclosureSubmission (.opening event candidate raw)).normalizeReactive who
      ((runtime.reactiveApplication leaks).observePlayer state who) known).emit
      ((runtime.reactiveApplication leaks).submit state who
        (disclosureSubmission (.opening event candidate raw))) who known = _ at packet
  rw [unchanged] at packet
  rw [packet]
  exact disclosureSubmission_certified state who known event candidate raw owned fixed

private theorem normalize_opening_of_matching_packet
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (token : Option (ReadinessToken graph))
    (emitted : submission.emit state who known =
      ⟨.opening event candidate raw, some ⟨candidate, raw⟩, token⟩)
    (owned : candidate.1 = who) (fixed : state.candidates.lookup candidate = .openable raw) :
    submission.normalizeReactive who ((runtime.reactiveApplication leaks).observePlayer state who)
        known =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who) known := by
  have call := congrArg WitnessedPacket.call emitted
  change submission.call.packet = .opening event candidate raw at call
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at call
  subst packet
  have evidenceEq := congrArg WitnessedPacket.evidence emitted
  rw [WitnessedSubmission.emit_eq_resolve] at evidenceEq
  change evidence.resolve who (fun slot => state.candidates.lookup (who, slot)) known =
    some ⟨candidate, raw⟩ at evidenceEq
  have localFixed : state.candidates.lookup (who, candidate.2) = .openable raw := by
    simpa only [← owned] using fixed
  simp only [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive,
    openingEffective, ↓reduceIte, Submission.candidateAfter_opening, disclosureSubmission]
  congr 1
  apply (EvidenceRequest.normalize_eq_iff_resolve_eq ..).mpr
  change evidence.resolve who (fun slot => state.candidates.lookup (who, slot)) known =
    (EvidenceRequest.owned ⟨candidate, raw⟩).resolve who
      (fun slot => state.candidates.lookup (who, slot)) known
  rw [evidenceEq]
  simp only [EvidenceRequest.resolve, owned, localFixed, and_self, ↓reduceIte]

end Vegas.EventGraphRuntime
