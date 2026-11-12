module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingFrameOpening
public import Vegas.Pending.ReactiveGuardedResponse

@[expose] public section

/-! # Guarded disclosures in the legal repaired continuation

A successful original disclosure has the same certificate and normalized
response after hidden binding repair. The actual retained menu admits that
response, including its once-per-event discipline. No claim is made for a
guard-rejected opening: that branch has publicly checkable departure evidence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : ((reactiveApplication timeouts) leaks).Execution}

/-- Semantic evidence normalization does not inspect unrelated hidden bindings.
Forwarded certificates use the same known envelope on the two executions. -/
theorem normalized_opening_eq (frame : Frame timeouts leaks memory owner original repaired)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftFixed : original.application.candidates.lookup candidate = .openable raw)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw) :
    (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        (((reactiveApplication timeouts) leaks).observePlayer original.application owner)
        (original.network.known owner) =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        (((reactiveApplication timeouts) leaks).observePlayer repaired.application owner)
        (repaired.network.known owner) := by
  have leftLocal : original.application.candidates.lookup (owner, candidate.2) =
      .openable raw := by simpa only [← owned, Prod.mk.eta] using leftFixed
  have rightLocal : repaired.application.candidates.lookup (owner, candidate.2) =
      .openable raw := by simpa only [← owned, Prod.mk.eta] using rightFixed
  simp only [disclosureSubmission, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, Submission.candidateAfter_opening,
    EvidenceRequest.normalize]
  change (⟨⟨.opening event candidate raw, none⟩,
    EvidenceRequest.canonical (original.network.known owner)
      ((EvidenceRequest.owned ⟨candidate, raw⟩).resolve owner
        (fun slot => original.application.candidates.lookup (owner, slot))
        (original.network.known owner))⟩ : WitnessedSubmission graph) = _
  change _ = (⟨⟨.opening event candidate raw, none⟩,
    EvidenceRequest.canonical (repaired.network.known owner)
      ((EvidenceRequest.owned ⟨candidate, raw⟩).resolve owner
        (fun slot => repaired.application.candidates.lookup (owner, slot))
        (repaired.network.known owner))⟩ : WitnessedSubmission graph)
  simp only [EvidenceRequest.resolve, owned, leftLocal, rightLocal, and_self,
    ↓reduceIte, frame.network]

/-- The finite effective menu admits the same normalized successful opening
after repair. Raw payload bounds and known forwarding references are unchanged. -/
theorem normalized_opening_available [Fintype Player]
    (frame : Frame timeouts leaks memory owner original repaired) (bounds : MessageBounds graph)
    (leftRecall : original.InputRecall ((reactiveApplication timeouts) leaks))
    (rightRecall : repaired.InputRecall ((reactiveApplication timeouts) leaks))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftFixed : original.application.candidates.lookup candidate = .openable raw)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw)
    (available : (⟨some ((disclosureSubmission (.opening event candidate raw)).normalizeReactive
      owner
        (((reactiveApplication timeouts) leaks).observePlayer original.application owner)
        (original.network.known owner))⟩ : ((reactiveApplication timeouts) leaks).Action) ∈
          (bounds.menu timeouts leaks).actions owner (original.logs owner)
            (original.observe ((reactiveApplication timeouts) leaks) owner)) :
    (⟨some ((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        (((reactiveApplication timeouts) leaks).observePlayer repaired.application owner)
        (repaired.network.known owner))⟩ : ((reactiveApplication timeouts) leaks).Action) ∈
          (bounds.menu timeouts leaks).actions owner (repaired.logs owner)
            (repaired.observe ((reactiveApplication timeouts) leaks) owner) := by
  let app := (reactiveApplication timeouts) leaks
  have leftKnown := app.known_from_recall original owner leftRecall
  have rightKnown := app.known_from_recall repaired owner rightRecall
  change original.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (original.logs owner) (original.observe app owner) at leftKnown
  change repaired.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (repaired.logs owner) (repaired.observe app owner) at rightKnown
  have sameKnown : ReactiveApplication.ResponseMenu.knownPackets
      (original.logs owner) (original.observe app owner) =
        ReactiveApplication.ResponseMenu.knownPackets
          (repaired.logs owner) (repaired.observe app owner) := by
    rw [← leftKnown, ← rightKnown, frame.network]
  have allowed := ((bounds.menu_mem timeouts leaks owner _ _ _).mp available).1
  rw [frame.normalized_opening_eq event candidate raw owned leftFixed rightFixed,
    sameKnown] at allowed
  apply (bounds.menu_mem timeouts leaks owner _ _ _).mpr
  refine ⟨allowed, ?_⟩
  change (⟨some (((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
      (app.observePlayer repaired.application owner)
      (repaired.network.known owner)).normalizeReactive
        owner (app.observePlayer repaired.application owner)
        (ReactiveApplication.ResponseMenu.knownPackets
          (repaired.logs owner) (repaired.observe app owner)))⟩ : app.Action) = _
  rw [← rightKnown, WitnessedSubmission.normalizeReactive_idempotent]

end Vegas.EventGraphRuntime.BindingMemory.Frame
