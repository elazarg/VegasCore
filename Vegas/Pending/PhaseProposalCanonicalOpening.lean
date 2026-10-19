/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalResponseAliases
import Vegas.Pending.PhaseOpeningPolicy

/-! # Actual counted opening aliases have one effective packet class -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- Count correctness fixes the signed certificate, while unused preparation
and the choice of ownership/forwarding request remain literal private aliases.
No successful guard or timely delivery is assumed. -/
theorem responseClass_opening
    (owner : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (preparation : Option (Raw L)) (evidence : EvidenceRequest graph)
    (rawMember : (⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view)
    (canonicalMember : PhaseCount.phaseOpeningResponse runtime leaks event candidate raw ∈
      PhaseCount.onePacketActions runtime leaks bounds owner past view) :
    responseClass runtime leaks bounds owner past view
        ⟨⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩, rawMember⟩ =
      responseClass runtime leaks bounds owner past view
        ⟨PhaseCount.phaseOpeningResponse runtime leaks event candidate raw, canonicalMember⟩ := by
  have resolve (prepared : Option (Raw L)) (request : EvidenceRequest graph)
      (member : (⟨some ⟨⟨.opening event candidate raw, prepared⟩, request⟩⟩ : (app).Action) ∈
        PhaseCount.onePacketActions runtime leaks bounds owner past view) :
      request.resolve owner view.application.1.candidates
        ((ReactiveApplication.ResponseMenu.knownPackets past view).map PhaseCount.nativeMessage) =
          some ⟨candidate, raw⟩ := by
    let material : WitnessedSubmission graph :=
      ⟨⟨.opening event candidate raw, prepared⟩, request⟩
    have permitted : PhaseCount.permits ((app).outputs past)
        (PhaseCount.localEnvelope runtime leaks owner past view material) = true := by
      rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner past view _).mp member).2
          with impossible | ⟨other, transmitted, allowed⟩
      · cases impossible
      · cases Option.some.inj transmitted
        exact allowed
    have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
    have call : (PhaseCount.nativeMessage
        (PhaseCount.localEnvelope runtime leaks owner past view material)).payload.call =
          .opening event candidate raw := PhaseCount.maskPacket_call _ _
    unfold CountCallCorrect at correct
    rw [call] at correct
    have certified :
        (PhaseCount.localEnvelope runtime leaks owner past view material).payload.packet.evidence =
          some ⟨candidate, raw⟩ := by
      obtain ⟨actual, handle, value, token, emitted⟩ :=
        (certifiedOpening_iff _).mp correct.1
      have same := (congrArg WitnessedPacket.call emitted).symm.trans call
      obtain ⟨rfl, rfl, rfl⟩ := Payload.opening.inj same
      exact congrArg WitnessedPacket.evidence emitted
    change (PhaseCount.maskPacket view.application.2
      ⟨material.call.packet, _,
        view.application.1.publicView.tokenFor material.call.packet⟩).evidence = _ at certified
    unfold PhaseCount.maskPacket at certified
    split at certified <;> split at certified <;>
      simpa only [material, Submission.candidateAfter_opening] using certified
  have original := resolve preparation evidence rawMember
  have canonical := resolve none (.owned ⟨candidate, raw⟩) canonicalMember
  apply Prod.ext
  · rfl
  · change some (PhaseCount.localEnvelope runtime leaks owner past view
        ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩).payload = _
    congr 1
    unfold PhaseCount.localEnvelope
    simp only [disclosureSubmission, Submission.candidateAfter_opening]
    rw [original, canonical]

end Vegas.EventGraphRuntime.PhaseProposal
