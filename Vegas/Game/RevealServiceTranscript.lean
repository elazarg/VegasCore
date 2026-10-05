/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceBlock
import Vegas.Pending.ReactiveRevealTranscript

/-! # Public transcript preservation for actual restricted responses

This transports the actual endpoint equations of a service block. Successful
normalized openings append their authentic public packet; silence
allocates no packet or receipt. No hidden binding is inspected by
the resulting transcript encoder.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- All ordinary responses maintain the public ledger, receipt, and serial
formulas, using the actual service endpoint supplied by block settlement. -/
theorem ordinary_response_transcript (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (source : State L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution next : (application setup leaks).Execution)
    (agree : refs.Agrees source execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (recall : execution.InputRecall (application setup leaks))
    (serials : execution.network.SerialsBeforeNext)
    (accepted : AcceptedHandles (graph setup))
    (acceptedEq : execution.application.accepted = accepted)
    (event : (graph setup).EventId)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (value : L.Val payload) (bound : source.get selected = .success value)
    (ready : execution.application.config.cut.Ready event)
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner))
    (ledger : execution.network.ledger =
      publicationLedger accepted ((graph setup).publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted ((graph setup).publicObserve execution.application.config))
    (counters : execution.network.nextSerial =
      publicationSerial accepted ((graph setup).publicObserve execution.application.config))
    (completed : next.application.config = execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (sourceChoice setup leaks response))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (if sourceChoice setup leaks response then PublicationResult.success value else .failure)))
    (network : next.network = if sourceChoice setup leaks response then
      ((execution.respond (application setup leaks) owner response).network.includePending
        (owner, execution.network.nextSerial owner)).2
      else (execution.respond (application setup leaks) owner response).network)
    (recorded : next.receipts = if sourceChoice setup leaks response then
      execution.receipts ++ [((owner, execution.network.nextSerial owner), true)]
      else execution.receipts) :
    next.network.ledger =
        publicationLedger accepted ((graph setup).publicObserve next.application.config) ∧
      next.receipts =
        publicationReceipts accepted ((graph setup).publicObserve next.application.config) ∧
      next.network.nextSerial =
        publicationSerial accepted ((graph setup).publicObserve next.application.config) := by
  cases chosen : sourceChoice setup leaks response with
  | false =>
      simp only [chosen, Bool.false_eq_true, ↓reduceIte] at completed network recorded
      have refuses : response = ⟨none⟩ :=
        (ordinary_false_iff setup leaks bounds owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) response member).mp chosen
      have unpublished :
          publicationPacket? accepted next.application.config.store event = none := by
        rw [completed]
        exact publicationPacket?_complete_resolve accepted execution.application.config event ready
          owner payload (refs.get selected) [] outputEq codeEq node _ .failure
      exact refusing_settlement_transcript (runtime setup) leaks execution next accepted owner
        event ready _ _ response refuses ledger receipts counters completed unpublished network
        recorded
  | true =>
      simp only [chosen, ↓reduceIte] at completed network recorded
      obtain ⟨candidate, associated, owned, verified, opening⟩ :=
        opening_at_checkpoint setup leaks selected source refs execution agree valid event
          ownedEvent outputEq codeEq node
          (ownTurn?_of_ready setup execution.application ready ownedEvent) value bound
      have responseEq := (ordinary_true_iff setup leaks bounds owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) _ opening response member).mp chosen
      have published : publicationPacket? accepted next.application.config.store event =
          some (owner, ⟨.opening event candidate ⟨payload, value⟩,
            some ⟨candidate, ⟨payload, value⟩⟩, some ⟨event⟩⟩) := by
        rw [completed, publicationPacket?_complete_resolve accepted execution.application.config
          event ready owner payload (refs.get selected) [] outputEq codeEq node]
        rw [acceptedEq] at associated
        rw [associated]
        rfl
      rw [responseEq] at network
      exact opening_settlement_transcript (runtime setup) leaks execution next accepted owner
        event candidate ⟨payload, value⟩ ready _ _ recall owned verified serials ledger receipts
        counters completed published network recorded

end Vegas
