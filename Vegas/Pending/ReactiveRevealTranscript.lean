/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.RevealTranscript
import Vegas.Pending.ReactiveRevealResponse

/-! # Actual response effects on the canonical reveal transcript

Successful evidence normalization preserves the emitted packet even when it
chooses a forwarding request. Published replays preserve public ledger and
sender counters. These equations connect the public transcript encoder to the
existing atomic response and at-most-once inclusion operations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The normalized response emits exactly the canonical authentic opening;
its private evidence-request representation cannot change the packet. -/
theorem normalized_opening_network (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (owned : candidate.1 = owner)
    (verified : execution.application.candidates.lookup candidate = .openable raw) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      ((runtime.reactiveNormalization leaks).action owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner)
        (runtime.canonicalRevealResponse leaks event candidate raw true))).network =
      (execution.network.submit owner
        (⟨.opening event candidate raw, some ⟨candidate, raw⟩,
          execution.application.publicView.tokenFor (.opening event candidate raw)⟩ :
            WitnessedPacket graph)).2 := by
  have same := ((runtime.reactiveNormalization leaks).effects execution owner
    (runtime.canonicalRevealResponse leaks event candidate raw true) recall).2.1
  refine same.trans ?_
  change (execution.network.submit owner
    ((disclosureSubmission (.opening event candidate raw)).emit execution.application owner
      (execution.network.known owner))).2 = _
  have certified :
      (disclosureSubmission (.opening event candidate raw)).emit execution.application owner
          (execution.network.known owner) =
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩,
          execution.application.publicView.tokenFor (.opening event candidate raw)⟩ := by
    have verifies : execution.application.candidates.verify candidate raw = true :=
      (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr verified
    simp only [disclosureSubmission, WitnessedSubmission.emit, owned, verifies, and_self,
      ↓reduceIte]
  rw [certified]

/-- Immediate inclusion of that fresh response appends exactly one canonical
ledger envelope, with the counter value that preceded submission. -/
theorem normalized_opening_included_ledger (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (owned : candidate.1 = owner)
    (verified : execution.application.candidates.lookup candidate = .openable raw)
    (serials : execution.network.SerialsBeforeNext) :
    let submitted := execution.respond (runtime.reactiveApplication leaks) owner
      ((runtime.reactiveNormalization leaks).action owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner)
        (runtime.canonicalRevealResponse leaks event candidate raw true))
    (submitted.network.includePending (owner, execution.network.nextSerial owner)).2.ledger =
      execution.network.ledger ++
        [⟨(owner, execution.network.nextSerial owner),
          ⟨.opening event candidate raw, some ⟨candidate, raw⟩,
            execution.application.publicView.tokenFor (.opening event candidate raw)⟩⟩] := by
  dsimp only
  rw [normalized_opening_network runtime leaks execution owner event candidate raw recall
    owned verified]
  simp only [MessageNetwork.includePending, serials.lookup_submit]
  rfl

theorem normalized_opening_included_serial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (owned : candidate.1 = owner)
    (verified : execution.application.candidates.lookup candidate = .openable raw)
    (serials : execution.network.SerialsBeforeNext) (observer : Player) :
    let submitted := execution.respond (runtime.reactiveApplication leaks) owner
      ((runtime.reactiveNormalization leaks).action owner (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner)
        (runtime.canonicalRevealResponse leaks event candidate raw true))
    (submitted.network.includePending (owner, execution.network.nextSerial owner)).2.nextSerial
        observer =
      execution.network.nextSerial observer + if owner = observer then 1 else 0 := by
  dsimp only
  rw [normalized_opening_network runtime leaks execution owner event candidate raw recall
    owned verified]
  simp only [MessageNetwork.includePending, serials.lookup_submit]
  simp only [MessageNetwork.submit]
  by_cases same : owner = observer
  · subst observer
    simp
  · simp [same, Ne.symm same]

/-- Silence and rebroadcasts allocate no new message id and publish no new
packet by themselves. Actual replay input and private recall are retained. -/
theorem refusing_response_public_fields (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (refuses : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
    (execution.respond (runtime.reactiveApplication leaks) owner response).network.ledger =
        execution.network.ledger ∧
      (execution.respond (runtime.reactiveApplication leaks) owner response).network.nextSerial =
        execution.network.nextSerial := by
  rcases refuses with rfl | ⟨id, rfl⟩
  · exact ⟨rfl, rfl⟩
  · change (execution.network.replay owner id).2.ledger = execution.network.ledger ∧
      (execution.network.replay owner id).2.nextSerial = execution.network.nextSerial
    unfold MessageNetwork.replay
    split <;> exact ⟨rfl, rfl⟩

/-- The actual successful response and inclusion preserve all three public
transcript equations. The caller supplies the actual completed configuration
and endpoint equations from the service suffix, rather than a second execution. -/
theorem opening_settlement_transcript (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (accepted : AcceptedHandles graph) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (ready : execution.application.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (owned : candidate.1 = owner)
    (verified : execution.application.candidates.lookup candidate = .openable raw)
    (serials : execution.network.SerialsBeforeNext)
    (ledger : execution.network.ledger =
      publicationLedger accepted (graph.publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted (graph.publicObserve execution.application.config))
    (counters : execution.network.nextSerial =
      publicationSerial accepted (graph.publicObserve execution.application.config))
    (completed : next.application.config =
      execution.application.config.complete event ready action value)
    (published : publicationPacket? accepted next.application.config.store event =
      some (owner, ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩))
    (network : next.network =
      ((execution.respond (runtime.reactiveApplication leaks) owner
        ((runtime.reactiveNormalization leaks).action owner (execution.recall owner)
          (execution.observe (runtime.reactiveApplication leaks) owner)
          (runtime.canonicalRevealResponse leaks event candidate raw true))).network.includePending
        (owner, execution.network.nextSerial owner)).2)
    (recorded : next.receipts = execution.receipts ++
      [((owner, execution.network.nextSerial owner), true)]) :
    next.network.ledger = publicationLedger accepted (graph.publicObserve next.application.config) ∧
      next.receipts = publicationReceipts accepted (graph.publicObserve next.application.config) ∧
      next.network.nextSerial =
        publicationSerial accepted (graph.publicObserve next.application.config) := by
  rw [completed] at published ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [publicationLedger_complete accepted _ event ready action value owner _ published,
      network, normalized_opening_included_ledger runtime leaks execution owner event candidate
        raw recall owned verified serials, ledger, counters,
      execution.application.publicView_tokenFor_of_ready _ event rfl ready]
  · rw [publicationReceipts_complete accepted _ event ready action value owner _ published,
      recorded, receipts, counters]
  · funext observer
    rw [publicationSerial_complete accepted _ event ready action value owner _ published,
      network, normalized_opening_included_serial runtime leaks execution owner event candidate
        raw recall owned verified serials, counters]

/-- A withholding response, including a published replay alias, preserves the
same transcript while the current publication becomes a public failure. -/
theorem refusing_settlement_transcript (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (accepted : AcceptedHandles graph) (owner : Player)
    (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (response : (runtime.reactiveApplication leaks).Action)
    (refuses : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (ledger : execution.network.ledger =
      publicationLedger accepted (graph.publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted (graph.publicObserve execution.application.config))
    (counters : execution.network.nextSerial =
      publicationSerial accepted (graph.publicObserve execution.application.config))
    (completed : next.application.config =
      execution.application.config.complete event ready action value)
    (unpublished : publicationPacket? accepted next.application.config.store event = none)
    (network : next.network =
      (execution.respond (runtime.reactiveApplication leaks) owner response).network)
    (recorded : next.receipts = execution.receipts) :
    next.network.ledger = publicationLedger accepted (graph.publicObserve next.application.config) ∧
      next.receipts = publicationReceipts accepted (graph.publicObserve next.application.config) ∧
      next.network.nextSerial =
        publicationSerial accepted (graph.publicObserve next.application.config) := by
  rw [completed] at unpublished ⊢
  obtain ⟨sameLedger, sameCounters⟩ :=
    refusing_response_public_fields runtime leaks execution owner response refuses
  rw [publicationLedger_complete_none accepted _ event ready action value unpublished,
    publicationReceipts_complete_none accepted _ event ready action value unpublished,
    publicationSerial_complete_none accepted _ event ready action value unpublished,
    network, sameLedger, sameCounters, recorded]
  exact ⟨ledger, receipts, counters⟩

end Vegas.EventGraphRuntime
