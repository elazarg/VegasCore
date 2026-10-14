/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSubmittedResponse
import Vegas.Pending.ReactiveBindingClassification

/-! # Normal forms of counted binding and opening responses -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A normalized binding response carrying no certificate has exactly the raw
private opening and no effective evidence request, regardless of slot freshness. -/
theorem normal_binding_of_absent_evidence (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (material : WitnessedSubmission graph) (event : graph.EventId) (candidate : Handle graph)
    (normal : material.normalizeReactive who view.application
      (ReactiveApplication.ResponseMenu.knownPackets past view) = material)
    (packet : material.call.packet = .commitment event candidate)
    (absent : (runtime.localEnvelope leaks who past view material).payload.evidence = none) :
    material = ⟨⟨.commitment event candidate, material.call.opening⟩, .none⟩ := by
  have evidenceNormal := congrArg WitnessedSubmission.evidence normal
  change material.evidence.normalize who
    (material.call.candidateAfter who view.application.candidates)
      (ReactiveApplication.ResponseMenu.knownPackets past view) = material.evidence
        at evidenceNormal
  change material.evidence.resolve who
    (material.call.candidateAfter who view.application.candidates)
      (ReactiveApplication.ResponseMenu.knownPackets past view) = none at absent
  rw [EvidenceRequest.normalize, absent, EvidenceRequest.canonical] at evidenceNormal
  cases material with
  | mk call evidence =>
      cases call with
      | mk submitted opening =>
          dsimp only at packet evidenceNormal ⊢
          subst submitted
          subst evidence
          rfl

/-- Every normalized certified owned opening has the compiler's authentic
opening normal form, including responses originally requesting forwarded evidence. -/
theorem normal_opening_of_owned_evidence (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (material : WitnessedSubmission graph) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (normal : material.normalizeReactive who view.application
      (ReactiveApplication.ResponseMenu.knownPackets past view) = material)
    (packet : material.call.packet = .opening event candidate raw)
    (certified : (runtime.localEnvelope leaks who past view material).payload.evidence =
      some ⟨candidate, raw⟩)
    (owned : candidate.1 = who)
    (fixed : view.application.candidates candidate.2 = .openable raw) :
    material = (disclosureSubmission (.opening event candidate raw)).normalizeReactive who
      view.application (ReactiveApplication.ResponseMenu.knownPackets past view) := by
  rw [← normal]
  cases material with
  | mk call evidence =>
      cases call with
      | mk submitted opening =>
          dsimp only at packet
          subst submitted
          change evidence.resolve who view.application.candidates
            (ReactiveApplication.ResponseMenu.knownPackets past view) = some ⟨candidate, raw⟩
            at certified
          simp only [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive,
            openingEffective, ↓reduceIte, Submission.candidateAfter_opening, disclosureSubmission]
          congr 1
          apply (EvidenceRequest.normalize_eq_iff_resolve_eq ..).mpr
          rw [certified]
          simp only [EvidenceRequest.resolve, owned, fixed, and_self, ↓reduceIte]

end Vegas.EventGraphRuntime
