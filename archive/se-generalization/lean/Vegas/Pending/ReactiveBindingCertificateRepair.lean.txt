/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRawBindingFrame
import Vegas.Pending.EvidenceNormalization

/-! # Certificate capability changed by mistyped binding repair

An actual canonical bare commitment with mistyped private material leaves an
authentic certificate capability for that material. Replacing its private
material by a typed default preserves the public packet and network but does
not preserve that capability. These operational facts identify a continuation
edge; they do not assert an equilibrium failure or a payoff comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Supplying actual raw material fixes a fresh owned prepared handle to that
material in the real response transition. Its declared source payload type is not read. -/
theorem bareBinding_submitted_openable
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (serial : Nat) (raw : Raw L)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), some raw⟩, .none⟩⟩
    (execution.respond (runtime.reactiveApplication leaks) who response).application.candidates
      |>.lookup (who, .prepared serial) = .openable raw := by
  let call : Submission graph := ⟨.commitment event (who, .prepared serial), some raw⟩
  change (submitStep (call.register execution.application who) who call.packet).candidates.lookup
    (who, .prepared serial) = .openable raw
  rw [call.candidateAfter_eq]
  simp only [call, Submission.candidateAfter, and_self, ↓reduceIte, fresh]

/-- The actual two bare submissions have identical networks, but the original
can issue the mistyped owned certificate and the typed replacement cannot.
This is a capability distinction, not proof of a profitable deviation. -/
theorem mistypedBinding_repair_certificate
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (serial : Nat) (payload : L.Ty) (raw : Raw L)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (mistyped : raw.as? payload = none) :
    let app := runtime.reactiveApplication leaks
    let original := execution.respond app who
      ⟨some ⟨⟨.commitment event (who, .prepared serial), some raw⟩, .none⟩⟩
    let repaired := execution.respond app who
      ⟨some ⟨⟨.commitment event (who, .prepared serial),
        some ⟨payload, L.someValue payload⟩⟩, .none⟩⟩
    let fact : OpeningFact graph := ⟨(who, .prepared serial), raw⟩
    original.network = repaired.network ∧
      (EvidenceRequest.owned fact).resolve who
        (fun slot => original.application.candidates.lookup (who, slot))
        (original.network.known who) = some fact ∧
      (EvidenceRequest.owned fact).resolve who
        (fun slot => repaired.application.candidates.lookup (who, slot))
        (repaired.network.known who) = none := by
  let app := runtime.reactiveApplication leaks
  let original := execution.respond app who
    ⟨some ⟨⟨.commitment event (who, .prepared serial), some raw⟩, .none⟩⟩
  let repaired := execution.respond app who
    ⟨some ⟨⟨.commitment event (who, .prepared serial),
      some ⟨payload, L.someValue payload⟩⟩, .none⟩⟩
  have different : (⟨payload, L.someValue payload⟩ : Raw L) ≠ raw := by
    intro same
    rw [← same, Raw.as?_mk] at mistyped
    cases mistyped
  have originalFixed := runtime.bareBinding_submitted_openable leaks execution who event serial raw
    fresh
  have repairedFixed := runtime.bareBinding_submitted_openable leaks execution who event serial
    ⟨payload, L.someValue payload⟩ fresh
  have physical := runtime.rawBinding_submit_hidden_congr leaks execution execution who rfl rfl
    rfl (fun _ _ => rfl) (fun _ _ => rfl) event serial (some raw)
    (some ⟨payload, L.someValue payload⟩)
  refine ⟨physical.1, ?_, ?_⟩
  · change (if who = who ∧ original.application.candidates.lookup (who, .prepared serial) =
      .openable raw then some _ else none) = _
    simp only [original, app, originalFixed, and_self, ↓reduceIte]
  · change (if who = who ∧ repaired.application.candidates.lookup (who, .prepared serial) =
      .openable raw then some _ else none) = _
    simp only [repaired, app, repairedFixed, CommitmentCandidate.openable.injEq, different,
      and_false, ↓reduceIte]

end Vegas.EventGraphRuntime
