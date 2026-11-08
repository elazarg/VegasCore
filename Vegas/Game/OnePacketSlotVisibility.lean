/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotTrembles

/-! # What the slot tier shows, and what it hides

At a binding of the player's turn, a source choice is *covered* when it encodes
to a successful binding value the message bounds contain
(`Vegas.CoveredBinding`). A covered choice committed at a slot transmits a
packet whose local envelope is the commitment of that slot, with no evidence
and the event's readiness token (`Vegas.slotEnvelope`), whatever the value
(`Vegas.slotResponse_transmission`). So, at a slot within the candidate
capacity, the one-packet menu offers the response exactly when the count
verdict permits that envelope, which does not depend on the value
(`Vegas.slotResponse_mem_onePacket_iff`).

At fresh slots, distinct slots or distinct values give distinct responses
(`Vegas.slotResponse_injective`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The local envelope of a commitment of `who` for `event` at a prepared
slot: no evidence and the event's readiness token from the view. -/
def slotEnvelope (who : Player) (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    (slot : Nat) : Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, (application setup timeouts leaks).submissionCount past),
    ⟨.commitment event (who, .prepared slot), none,
      view.application.publicView.tokenFor (.commitment event (who, .prepared slot))⟩⟩

/-- At a binding, the slot tier is silent on omission and otherwise sends the
normalized commitment at the slot. -/
theorem slotResponse_of_bind (who : Player) (past : List (application setup timeouts
  leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action) :
    slotResponse setup timeouts leaks who past view event slot choice =
      match cast (congrArg EventGraph.EventField.Action outputEq) action with
      | none => ⟨none⟩
      | some result => ((reactiveNormalization timeouts) leaks).action who past view
          ((reactiveBinding timeouts) leaks who event payload result slot) := by
  unfold slotResponse
  rw [encoded]
  simp only [node]
  rfl

/-- **The envelope does not depend on the value.** A choice encoded at a
binding, committed at a slot, transmits a packet whose local envelope is the
slot's envelope. -/
theorem slotResponse_transmission (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action)
    (present : (cast (congrArg EventGraph.EventField.Action outputEq) action).isSome = true) :
    ∃ material, (slotResponse setup timeouts leaks who past view event slot choice).transmission =
        some material ∧
      (localEnvelope timeouts) leaks who past view material =
        slotEnvelope setup timeouts leaks who past view event slot := by
  rw [slotResponse_of_bind setup timeouts leaks who past view event node slot choice action encoded]
  cases result : cast (congrArg EventGraph.EventField.Action outputEq) action with
  | none => simp [result] at present
  | some value => exact ⟨_, rfl, rfl⟩

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- A source choice encodes, at a binding event, to a successful binding value
the message bounds contain. -/
def CoveredBinding (event : (graph setup).EventId) (choice : Option (OwnAction Player L)) :
    Prop :=
  ∃ action, choice.bind (encodeEventAction? setup.program event) = some action ∧
    ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
            Option (PublicationResult (L.Val payload))) = some (.success value) ∧
          (⟨payload, value⟩ : Raw L) ∈ bounds.values

/-- **Acceptance depends on the slot alone.** At a binding, a covered choice
committed at a slot within the candidate capacity lies in the one-packet menu
exactly when the count verdict permits the slot's envelope against the
player's earlier packets. -/
theorem slotResponse_mem_onePacket_iff (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (capacity : slot < bounds.candidateCount) (choice : Option (OwnAction Player L))
    (covered : CoveredBinding setup bounds event choice) :
    slotResponse setup timeouts leaks who past view event slot choice ∈
        bounds.onePacketActions timeouts leaks who past view ↔
      countPermits ((application setup timeouts leaks).outputs past)
        (slotEnvelope setup timeouts leaks who past view event slot) = true := by
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨value, successful, included⟩ := values owner payload outputEq codeEq node
  obtain ⟨material, transmits, envelope⟩ :=
    slotResponse_transmission setup timeouts leaks who past view event node slot choice action
      encoded (by rw [successful]; rfl)
  rw [bounds.mem_onePacketActions]
  constructor
  · rintro ⟨_, silent | ⟨other, otherTransmits, permitted⟩⟩
    · rw [transmits] at silent
      cases silent
    · rw [transmits] at otherTransmits
      cases Option.some.inj otherTransmits
      rwa [envelope] at permitted
  · intro permitted
    refine ⟨?_, Or.inr ⟨material, transmits, by rwa [envelope]⟩⟩
    rw [slotResponse_of_bind setup timeouts leaks who past view event node slot choice action
      encoded, successful]
    apply bounds.binding_normalized_available timeouts leaks who past view event payload
      _ slot capacity
    intro chosen same
    cases same
    exact included

variable (initial : PMF (application setup timeouts leaks).State) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

omit [Fintype Player] in
/-- **Distinct slots or values give distinct responses** at fresh slots. -/
theorem slotResponse_injective (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (slot other : Nat) (slotFresh : view.application.candidates (.prepared slot) = .fresh)
    (otherFresh : view.application.candidates (.prepared other) = .fresh)
    (first second : Option (OwnAction Player L))
    (firstCovered : CoveredBinding setup bounds event first)
    (secondCovered : CoveredBinding setup bounds event second)
    (same : slotResponse setup timeouts leaks who past view event slot first =
      slotResponse setup timeouts leaks who past view event other second) :
    slot = other ∧ first.bind (encodeEventAction? setup.program event) =
      second.bind (encodeEventAction? setup.program event) := by
  obtain ⟨firstAction, firstEncoded, firstValues⟩ := firstCovered
  obtain ⟨secondAction, secondEncoded, secondValues⟩ := secondCovered
  obtain ⟨firstValue, firstSuccess, _⟩ := firstValues owner payload outputEq codeEq node
  obtain ⟨secondValue, secondSuccess, _⟩ := secondValues owner payload outputEq codeEq node
  rw [slotResponse_of_bind setup timeouts leaks who past view event node slot first firstAction
      firstEncoded,
    slotResponse_of_bind setup timeouts leaks who past view event node other second secondAction
      secondEncoded, firstSuccess, secondSuccess] at same
  simp only at same
  rw [(reactiveBinding_normal_of_fresh timeouts) leaks who past view event payload _ slot
      slotFresh,
    (reactiveBinding_normal_of_fresh timeouts) leaks who past view event payload _ other
      otherFresh] at same
  have transmission := congrArg ReactiveApplication.Action.transmission same
  simp only [EventGraphRuntime.reactiveBinding, Option.some.injEq] at transmission
  have packetEq := congrArg (fun material : WitnessedSubmission (graph setup) =>
    material.call.packet) transmission
  have openingEq := congrArg (fun material : WitnessedSubmission (graph setup) =>
    material.call.opening) transmission
  simp only [Payload.commitment.injEq, Prod.mk.injEq, Slot.prepared.injEq, true_and]
    at packetEq
  simp only [Option.some.injEq, Raw.mk.injEq, heq_eq_eq, true_and] at openingEq
  refine ⟨packetEq, ?_⟩
  rw [firstEncoded, secondEncoded]
  congr 1
  have castEq : (cast (congrArg EventGraph.EventField.Action outputEq) firstAction :
      Option (PublicationResult (L.Val payload))) =
        cast (congrArg EventGraph.EventField.Action outputEq)
        secondAction := by
    rw [firstSuccess, secondSuccess, openingEq]
  exact (cast_inj _).mp castEq

end Vegas
