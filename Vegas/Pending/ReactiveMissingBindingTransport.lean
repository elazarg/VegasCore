/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingCertificateRepair
import Vegas.Pending.ReactiveFiniteResponses

/-! # Actual certificate transport after a missing opening is repaired

Replacing a blocked candidate by an openable candidate adds capabilities without
removing an existing one. Original effective responses therefore retain their
certificate semantics. Unavailable owned requests in the raw menu need not have
this property, since repair can make such a request newly successful.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A normalized request cannot secretly gain a certificate when the receiver's
owned capabilities increase. Forwarding keeps the actual first-match known list. -/
theorem EvidenceRequest.resolve_normalized_of_openable_mono
    (who : Player)
    (left right : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph)))
    (preserved : ∀ slot raw, left slot = .openable raw → right slot = .openable raw)
    (request : EvidenceRequest graph)
    (normal : request.normalize who left known = request) :
    request.resolve who left known = request.resolve who right known := by
  classical
  cases request with
  | none => rfl
  | forward id => rfl
  | owned fact =>
      have available : fact.handle.1 = who ∧ left fact.handle.2 = .openable fact.raw := by
        by_contra absent
        simp only [EvidenceRequest.normalize, EvidenceRequest.resolve, absent, ↓reduceIte,
          EvidenceRequest.canonical] at normal
        cases normal
      simp only [EvidenceRequest.resolve, available.1, available.2,
        preserved _ _ available.2, and_self, ↓reduceIte]

/-- The same actual private registration preserves every old openable value
when both candidate tables have the same fresh slots. -/
theorem Submission.candidateAfter_openable_mono
    (who : Player) (left right : CandidateSlot graph → CommitmentCandidate (Raw L))
    (fresh : ∀ slot, left slot = .fresh ↔ right slot = .fresh)
    (preserved : ∀ slot raw, left slot = .openable raw → right slot = .openable raw)
    (call : Submission graph) :
    ∀ slot raw, call.candidateAfter who left slot = .openable raw →
      call.candidateAfter who right slot = .openable raw := by
  classical
  intro slot raw available
  cases packet : call.packet with
  | commitment event handle =>
      by_cases selected : handle.1 = who ∧ slot = handle.2
      · obtain ⟨author, same⟩ := selected
        subst slot
        simp only [candidateAfter, packet, author, and_self, ↓reduceIte] at available ⊢
        cases meaning : left handle.2 with
        | fresh =>
            rw [(fresh handle.2).mp meaning]
            simpa only [meaning] using available
        | unopenable =>
            simp only [meaning] at available
            cases available
        | openable value =>
            rw [preserved handle.2 value meaning]
            simpa only [meaning] using available
      · simpa only [candidateAfter, packet, selected, ↓reduceIte] using
          preserved slot raw (by
            simpa only [candidateAfter, packet, selected, ↓reduceIte] using available)
  | opening | withhold | malformed =>
      simpa only [candidateAfter, packet] using
        preserved slot raw (by simpa only [candidateAfter, packet] using available)

omit [DecidableEq Player] in
private theorem openingEffective_congr_of_fresh
    (who : Player) (left right : ReactivePlayerView graph)
    (fresh : ∀ slot, left.candidates slot = .fresh ↔ right.candidates slot = .fresh)
    (packet : Payload graph) : openingEffective who left packet ↔
      openingEffective who right packet := by
  cases packet with
  | commitment event handle =>
      rcases handle with ⟨author, slot⟩
      cases slot with
      | initial input => rfl
      | prepared serial => exact and_congr_right fun _ => fresh (.prepared serial)
  | opening | withhold | malformed => rfl

/-- Every effective witnessed submission keeps its normal form and resolved
certificate when only unavailable owned capabilities are added. -/
theorem WitnessedSubmission.normalized_openable_transport
    (who : Player) (left right : ReactivePlayerView graph)
    (known : List (Message Player (WitnessedPacket graph)))
    (fresh : ∀ slot, left.candidates slot = .fresh ↔ right.candidates slot = .fresh)
    (preserved : ∀ slot raw, left.candidates slot = .openable raw →
      right.candidates slot = .openable raw)
    (submission : WitnessedSubmission graph)
    (normal : submission.normalizeReactive who left known = submission) :
    submission.normalizeReactive who right known = submission ∧
      submission.evidence.resolve who (submission.call.candidateAfter who left.candidates) known =
        submission.evidence.resolve who (submission.call.candidateAfter who right.candidates)
          known := by
  have evidenceNormal := congrArg WitnessedSubmission.evidence normal
  change submission.evidence.normalize who
    (submission.call.candidateAfter who left.candidates) known = submission.evidence
      at evidenceNormal
  have resolved := EvidenceRequest.resolve_normalized_of_openable_mono who _ _ known
    (submission.call.candidateAfter_openable_mono who left.candidates right.candidates fresh
      preserved) submission.evidence evidenceNormal
  refine ⟨?_, resolved⟩
  have callEq : submission.call.normalizeReactive who left =
      submission.call.normalizeReactive who right := by
    unfold Submission.normalizeReactive
    rw [propext (openingEffective_congr_of_fresh who left right fresh submission.call.packet)]
  have evidenceEq : submission.evidence.normalize who
      (submission.call.candidateAfter who left.candidates) known =
        submission.evidence.normalize who
          (submission.call.candidateAfter who right.candidates) known := by
    exact congrArg (EvidenceRequest.canonical known) resolved
  calc
    submission.normalizeReactive who right known =
        submission.normalizeReactive who left known := by
      unfold normalizeReactive
      rw [← callEq, ← evidenceEq]
    _ = submission := normal

private theorem effectiveResponse_openable_transport [Fintype Player]
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (network : left.network = right.network)
    (publicEq : left.application.publicView = right.application.publicView)
    (fresh : ∀ slot, left.application.candidates.lookup (who, slot) = .fresh ↔
      right.application.candidates.lookup (who, slot) = .fresh)
    (preserved : ∀ slot raw, left.application.candidates.lookup (who, slot) = .openable raw →
      right.application.candidates.lookup (who, slot) = .openable raw)
    (response : (runtime.reactiveApplication leaks).Action)
    (allowed : response ∈ (bounds.menu runtime leaks).actions who (left.recall who)
      (left.observe (runtime.reactiveApplication leaks) who)) :
    let app := runtime.reactiveApplication leaks
    response ∈ (bounds.menu runtime leaks).actions who (right.recall who)
        (right.observe app who) ∧
      (left.respond app who response).network = (right.respond app who response).network ∧
      ∀ material, response.transmission = some material →
        app.packet (app.submit left.application who material) who (left.network.known who)
            material =
          app.packet (app.submit right.application who material) who (right.network.known who)
            material := by
  let app := runtime.reactiveApplication leaks
  have known : left.network.known who = right.network.known who :=
    congrArg (fun net => net.known who) network
  have leftKnown : ReactiveApplication.ResponseMenu.knownPackets (left.recall who)
      (left.observe app who) = left.network.known who :=
    (app.known_from_recall left who leftRecall).symm
  have rightKnown : ReactiveApplication.ResponseMenu.knownPackets (right.recall who)
      (right.observe app who) = right.network.known who :=
    (app.known_from_recall right who rightRecall).symm
  rw [bounds.menu_mem] at allowed
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      exact ⟨(bounds.menu_mem runtime leaks who _ _ _).mpr ⟨trivial, rfl⟩,
        network, fun _ absent => by cases absent⟩
  | some submission =>
      change WitnessedSubmission graph at submission
      have normal : submission.normalizeReactive who (app.observePlayer left.application who)
          (left.network.known who) = submission := by
        have same := congrArg ReactiveApplication.Action.transmission allowed.2
        change some (submission.normalizeReactive who (app.observePlayer left.application who)
          (ReactiveApplication.ResponseMenu.knownPackets (left.recall who)
            (left.observe app who))) = some submission at same
        rw [leftKnown] at same
        exact Option.some.inj same
      have transported := submission.normalized_openable_transport who
        (app.observePlayer left.application who) (app.observePlayer right.application who)
        (left.network.known who) fresh preserved normal
      have emitted : app.packet (app.submit left.application who submission) who
          (left.network.known who) submission =
        app.packet (app.submit right.application who submission) who
          (right.network.known who) submission := by
        change submission.emit
          (submitStep (submission.call.register left.application who) who submission.call.packet)
          who (left.network.known who) = submission.emit
            (submitStep (submission.call.register right.application who) who submission.call.packet)
            who (right.network.known who)
        rw [WitnessedSubmission.emit_eq_resolve, WitnessedSubmission.emit_eq_resolve]
        have leftCandidates := funext (submission.call.candidateAfter_eq who left.application)
        have rightCandidates := funext (submission.call.candidateAfter_eq who right.application)
        rw [submitStep_publicView, (submission.call.register_facts who left.application).2.2,
          submitStep_publicView, (submission.call.register_facts who right.application).2.2,
          publicEq]
        rw [leftCandidates, rightCandidates, ← known]
        exact congrArg (fun certificate => WitnessedPacket.mk submission.call.packet certificate
          (right.application.publicView.tokenFor submission.call.packet)) transported.2
      refine ⟨(bounds.menu_mem runtime leaks who _ _ _).mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · have bound := allowed.1
        change (bounds.AllowsPacket submission.call.packet ∧
          bounds.AllowsOpening submission.call.opening) ∧ bounds.AllowsEvidence
            (ReactiveApplication.ResponseMenu.knownPackets (app := app) (left.recall who)
              (left.observe app who)) submission.evidence at bound
        change (bounds.AllowsPacket submission.call.packet ∧
          bounds.AllowsOpening submission.call.opening) ∧ bounds.AllowsEvidence
            (ReactiveApplication.ResponseMenu.knownPackets (app := app) (right.recall who)
              (right.observe app who)) submission.evidence
        rw [leftKnown] at bound
        rw [rightKnown, ← known]
        exact bound
      · change (⟨some (submission.normalizeReactive who (app.observePlayer right.application who)
          (ReactiveApplication.ResponseMenu.knownPackets (right.recall who)
            (right.observe app who)))⟩ : app.Action) = ⟨some submission⟩
        rw [rightKnown, ← known, transported.1]
      · change (left.network.submit who _).2 = (right.network.submit who _).2
        rw [emitted, network]
      · intro material same
        cases Option.some.inj same
        exact emitted

/-- Omitting private material fixes the actual fresh prepared candidate to a
blocked meaning rather than retaining any owned opening certificate. -/
theorem bareBinding_submitted_unopenable
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (serial : Nat)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), none⟩, .none⟩⟩
    (execution.respond (runtime.reactiveApplication leaks) who response).application.candidates
      |>.lookup (who, .prepared serial) = .unopenable := by
  let call : Submission graph := ⟨.commitment event (who, .prepared serial), none⟩
  change (submitStep (call.register execution.application who) who call.packet).candidates.lookup
    (who, .prepared serial) = .unopenable
  rw [call.candidateAfter_eq]
  simp only [call, Submission.candidateAfter, and_self, ↓reduceIte, fresh]

/-- Immediately after the actual missing-opening commitment and its replacement,
every original effective owner response is still effective and emits the same
envelope. Its call can be arbitrary, including malformed contents and forwarding;
only semantic normal forms are copied. This is one response step, not a complete
continuation or payoff comparison. -/
theorem missingBinding_repair_response_transport [Fintype Player]
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (who : Player) (event : graph.EventId) (serial : Nat) (replacement : Raw L)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (response : (runtime.reactiveApplication leaks).Action) :
    let app := runtime.reactiveApplication leaks
    let original := execution.respond app who
      ⟨some ⟨⟨.commitment event (who, .prepared serial), none⟩, .none⟩⟩
    let repaired := execution.respond app who
      ⟨some ⟨⟨.commitment event (who, .prepared serial), some replacement⟩, .none⟩⟩
    response ∈ (bounds.menu runtime leaks).actions who (original.recall who)
        (original.observe app who) →
      response ∈ (bounds.menu runtime leaks).actions who (repaired.recall who)
          (repaired.observe app who) ∧
        (original.respond app who response).network =
          (repaired.respond app who response).network ∧
        ∀ material, response.transmission = some material →
          app.packet (app.submit original.application who material) who
              (original.network.known who) material =
            app.packet (app.submit repaired.application who material) who
              (repaired.network.known who) material := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let original := execution.respond app who
    ⟨some ⟨⟨.commitment event (who, .prepared serial), none⟩, .none⟩⟩
  let repaired := execution.respond app who
    ⟨some ⟨⟨.commitment event (who, .prepared serial), some replacement⟩, .none⟩⟩
  intro allowed
  have originalFixed := runtime.bareBinding_submitted_unopenable leaks execution who event serial
    fresh
  have repairedFixed := runtime.bareBinding_submitted_openable leaks execution who event serial
    replacement fresh
  have other (opening : Option (Raw L)) (slot : CandidateSlot graph)
      (different : slot ≠ .prepared serial) :
      ((execution.respond app who
        ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩).application.candidates
          |>.lookup (who, slot)) = execution.application.candidates.lookup (who, slot) := by
    let call : Submission graph := ⟨.commitment event (who, .prepared serial), opening⟩
    change (submitStep (call.register execution.application who) who call.packet).candidates.lookup
      (who, slot) = execution.application.candidates.lookup (who, slot)
    rw [call.candidateAfter_eq]
    simp only [call, Submission.candidateAfter, different, and_false, ↓reduceIte]
  have freshSlots : ∀ slot, original.application.candidates.lookup (who, slot) = .fresh ↔
      repaired.application.candidates.lookup (who, slot) = .fresh := by
    intro slot
    by_cases same : slot = .prepared serial
    · subst slot
      rw [originalFixed, repairedFixed]
      simp
    · rw [other none slot same, other (some replacement) slot same]
  have preserved : ∀ slot raw,
      original.application.candidates.lookup (who, slot) = .openable raw →
        repaired.application.candidates.lookup (who, slot) = .openable raw := by
    intro slot raw available
    by_cases same : slot = .prepared serial
    · subst slot
      rw [originalFixed] at available
      cases available
    · rw [other (some replacement) slot same]
      rwa [other none slot same] at available
  have physical := runtime.rawBinding_submit_hidden_congr leaks execution execution who rfl rfl
    rfl (fun _ _ => rfl) (fun _ _ => rfl) event serial none (some replacement)
  exact effectiveResponse_openable_transport runtime leaks bounds who original repaired
    (app.respond_inputRecall execution who _ recall)
    (app.respond_inputRecall execution who _ recall)
    physical.1 physical.2.2.1 freshSlots preserved response allowed

/-- An arbitrary bounded raw response can be copied after normalizing at the
original own input. This preserves its real packet even if a formerly unavailable
owned request would succeed when blindly evaluated against the replacement. -/
theorem missingBinding_repair_raw_response_transport [Fintype Player]
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (who : Player) (event : graph.EventId) (serial : Nat) (replacement : Raw L)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (response : (runtime.reactiveApplication leaks).Action) :
    let app := runtime.reactiveApplication leaks
    let original := execution.respond app who
      ⟨some ⟨⟨.commitment event (who, .prepared serial), none⟩, .none⟩⟩
    let repaired := execution.respond app who
      ⟨some ⟨⟨.commitment event (who, .prepared serial), some replacement⟩, .none⟩⟩
    let chosen := (runtime.reactiveNormalization leaks).action who (original.recall who)
      (original.observe app who) response
    response ∈ (bounds.rawMenu runtime leaks).actions who (original.recall who)
        (original.observe app who) →
      chosen ∈ (bounds.menu runtime leaks).actions who (repaired.recall who)
          (repaired.observe app who) ∧
        (original.respond app who response).network =
          (repaired.respond app who chosen).network := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let original := execution.respond app who
    ⟨some ⟨⟨.commitment event (who, .prepared serial), none⟩, .none⟩⟩
  let repaired := execution.respond app who
    ⟨some ⟨⟨.commitment event (who, .prepared serial), some replacement⟩, .none⟩⟩
  let chosen := (runtime.reactiveNormalization leaks).action who (original.recall who)
    (original.observe app who) response
  intro allowed
  have available : chosen ∈ (bounds.menu runtime leaks).actions who (original.recall who)
      (original.observe app who) := by
    exact ((runtime.reactiveNormalization leaks).menu_mem (bounds.rawMenu runtime leaks)
      who _ _ _).mpr ⟨response, allowed, rfl⟩
  have transported := runtime.missingBinding_repair_response_transport leaks bounds execution
    recall who event serial replacement fresh chosen available
  have effects := (runtime.reactiveNormalization leaks).effects original who response
    (app.respond_inputRecall execution who _ recall)
  exact ⟨transported.1, effects.2.1.symm.trans transported.2.1⟩

end Vegas.EventGraphRuntime
