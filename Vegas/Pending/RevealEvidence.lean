/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.RevealTranscript
import Vegas.EventGraph.ResolutionFields

/-! # Published certificates originate at completed resolution events

With injective accepted handles and one resolution per binding, the public
transcript contains no certificate for a still-unresolved commitment.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The next canonical serial is computable from the public ledger. Replaying
an envelope does not allocate a new serial or add another ledger entry. -/
theorem publicationSerial_eq_ledger_count (accepted : AcceptedHandles graph)
    (view : graph.PublicObservation) (who : Player) :
    publicationSerial accepted view who =
      (publicationLedger accepted view).countP (fun message => message.sender = who) := by
  unfold publicationSerial
  rw [← publicationLedger_decode, List.countP_map]
  rfl

omit [DecidableEq Player] in
theorem publicationPacket?_evidence_field (accepted : AcceptedHandles graph)
    (store : EventGraph.Store graph.layout) (event : graph.EventId)
    (packet : Player × WitnessedPacket graph)
    (encoded : publicationPacket? accepted store event = some packet)
    (fact : OpeningFact graph) (evidence : packet.2.evidence = some fact) :
    ∃ field, (graph.nodes event).resolutionField? = some field ∧
      accepted field = some fact.handle := by
  unfold publicationPacket? at encoded
  cases node : nodeView graph event with
  | sample => simp only [node] at encoded; cases encoded
  | bind => simp only [node] at encoded; cases encoded
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [node] at encoded
      split at encoded
      · cases encoded
      · cases encoded
      · cases found : accepted binding.field with
        | none => simp only [found, Option.map_none] at encoded; cases encoded
        | some candidate =>
            simp only [found, Option.map_some, Option.some.injEq] at encoded
            subst packet
            cases Option.some.inj evidence
            refine ⟨binding.field, ?_, found⟩
            have selected := EventCode.resolutionField?_cast outputEq (graph.nodes event)
            rw [codeEq] at selected
            exact selected.symm

theorem publicationLedger_evidence_origin (accepted : AcceptedHandles graph)
    (view : graph.PublicObservation) (message : Message Player (WitnessedPacket graph))
    (member : message ∈ publicationLedger accepted view)
    (fact : OpeningFact graph) (evidence : message.payload.evidence = some fact) :
    ∃ event ∈ view.completionOrder, ∃ field,
      (graph.nodes event).resolutionField? = some field ∧ accepted field = some fact.handle := by
  have decoded : (message.sender, message.payload) ∈ publicationPackets accepted view := by
    rw [← publicationLedger_decode]
    exact List.mem_map_of_mem member
  obtain ⟨event, completed, encoded⟩ := List.mem_filterMap.mp decoded
  exact ⟨event, completed, publicationPacket?_evidence_field accepted view.store event
    (message.sender, message.payload) encoded fact evidence⟩

/-- An unresolved binding cannot already have a certificate in the encoded
public ledger, even when distinct bindings contain equal private values. -/
theorem publicationLedger_unresolved_evidence (accepted : AcceptedHandles graph)
    (injective : ∀ left right handle, accepted left = some handle →
      accepted right = some handle → left = right)
    (unique : ∀ left right field, (graph.nodes left).resolutionField? = some field →
      (graph.nodes right).resolutionField? = some field → left = right)
    (view : graph.PublicObservation) (event : graph.EventId)
    (unfinished : event ∉ view.completionOrder) (field : graph.Field)
    (resolves : (graph.nodes event).resolutionField? = some field)
    (candidate : Handle graph) (associated : accepted field = some candidate)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ publicationLedger accepted view) (raw : Raw L) :
    message.payload.evidence ≠ some ⟨candidate, raw⟩ := by
  intro evidence
  obtain ⟨prior, completed, earlier, resolved, bound⟩ :=
    publicationLedger_evidence_origin accepted view message member ⟨candidate, raw⟩ evidence
  have sameField := injective earlier field candidate bound associated
  have sameEvent := unique prior event field (sameField ▸ resolved) resolves
  exact unfinished (sameEvent ▸ completed)

end Vegas.EventGraphRuntime
