/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

The visible outcome of a one-packet choice is the envelope it transmits, if any
(`Vegas.visibleEnvelope`). For a covered choice at a slot within capacity it is
the slot's envelope when the count verdict permits it and nothing otherwise
(`Vegas.visibleEnvelope_slotResponse`, `Vegas.slotVisible`). Hence, when every
as-if-honest choice is covered and the capacity is at least one, the joint law
of visible outcome and source choice in the slot tier is the product of the law
of the visible outcome and the as-if-honest law
(`Vegas.slotTier_visible_value_law`): given any visible outcome, a slot or
silence, the source choice follows as-if-honest play.

At fresh slots, distinct slots or distinct values give distinct responses
(`Vegas.slotResponse_injective`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime

/-- Pushing a product law forward along the first coordinate keeps it a
product. -/
theorem bind_map_pair_map_fst {α β γ : Type} (first : PMF α) (second : PMF β) (f : α → γ) :
    (first.bind fun x => second.map (Prod.mk x)).map (fun pair => (f pair.1, pair.2)) =
      (first.map f).bind fun y => second.map (Prod.mk y) := by
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext x
  rw [PMF.map_comp]
  rfl

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The local envelope of a commitment of `who` for `event` at a prepared
slot: no evidence and the event's readiness token from the view. -/
def slotEnvelope (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (slot : Nat) : Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, (application setup leaks).submissionCount past),
    ⟨.commitment event (who, .prepared slot), none,
      view.application.publicView.tokenFor (.commitment event (who, .prepared slot))⟩⟩

/-- At a binding, the slot tier's response to an encoded choice is the
normalized commitment of its value at the slot. -/
theorem slotResponse_of_bind (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action) :
    slotResponse setup leaks who past view event slot choice =
      ((runtime setup).reactiveNormalization leaks).action who past view
        ((runtime setup).reactiveBinding leaks who event payload
          (cast (congrArg EventGraph.EventField.Action outputEq) action) slot) := by
  unfold slotResponse
  rw [encoded]
  simp only [node]

/-- **The envelope does not depend on the value.** A choice encoded at a
binding, committed at a slot, transmits a packet whose local envelope is the
slot's envelope. -/
theorem slotResponse_transmission (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action) :
    ∃ material, (slotResponse setup leaks who past view event slot choice).transmission =
        some material ∧
      (runtime setup).localEnvelope leaks who past view material =
        slotEnvelope setup leaks who past view event slot := by
  rw [slotResponse_of_bind setup leaks who past view event node slot choice action encoded]
  exact ⟨_, rfl, rfl⟩

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- A source choice encodes, at a binding event, to a successful binding value
the message bounds contain. -/
def CoveredBinding (event : (graph setup).EventId) (choice : Option (OwnAction Player L)) :
    Prop :=
  ∃ action, choice.bind (encodeEventAction? setup.program event) = some action ∧
    ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
            PublicationResult (L.Val payload)) = .success value ∧
          (⟨payload, value⟩ : Raw L) ∈ bounds.values

/-- **Acceptance depends on the slot alone.** At a binding, a covered choice
committed at a slot within the candidate capacity lies in the one-packet menu
exactly when the count verdict permits the slot's envelope against the
player's earlier packets. -/
theorem slotResponse_mem_onePacket_iff (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (capacity : slot < bounds.candidateCount) (choice : Option (OwnAction Player L))
    (covered : CoveredBinding setup bounds event choice) :
    slotResponse setup leaks who past view event slot choice ∈
        bounds.onePacketActions (runtime setup) leaks who past view ↔
      countPermits ((application setup leaks).outputs past)
        (slotEnvelope setup leaks who past view event slot) = true := by
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨value, successful, included⟩ := values owner payload outputEq codeEq node
  obtain ⟨material, transmits, envelope⟩ :=
    slotResponse_transmission setup leaks who past view event node slot choice action encoded
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
    rw [slotResponse_of_bind setup leaks who past view event node slot choice action encoded]
    apply bounds.binding_normalized_available (runtime setup) leaks who past view event payload
      _ slot capacity
    intro chosen same
    rw [successful] at same
    cases same
    exact included

/-- The envelope a one-packet choice transmits, if any. -/
def visibleEnvelope (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (choice : Option (application setup leaks).Action) :
    Option (Message Player (WitnessedPacket (graph setup))) :=
  choice.bind fun response =>
    response.transmission.map ((runtime setup).localEnvelope leaks who past view)

/-- The visible outcome of committing at a slot: its envelope when the count
verdict permits it, nothing otherwise. -/
def slotVisible (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) (slot : Nat) :
    Option (Message Player (WitnessedPacket (graph setup))) :=
  if countPermits ((application setup leaks).outputs past)
      (slotEnvelope setup leaks who past view event slot) = true then
    some (slotEnvelope setup leaks who past view event slot)
  else none

variable (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **The visible outcome of a slot-tier choice.** At a binding, the choice of
the response to a covered source choice committed at a slot within capacity
transmits the slot's visible outcome. -/
theorem visibleEnvelope_slotResponse (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) (slot : Nat)
    (capacity : slot < bounds.candidateCount) (choice : Option (OwnAction Player L))
    (covered : CoveredBinding setup bounds event choice) :
    visibleEnvelope setup leaks who past view
        (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view))
          (slotResponse setup leaks who past view event slot choice)).1 =
      slotVisible setup leaks who past view event slot := by
  classical
  have membership := slotResponse_mem_onePacket_iff setup leaks bounds who past view event node
    slot capacity choice covered
  obtain ⟨action, encoded, _⟩ := covered
  obtain ⟨material, transmits, envelope⟩ :=
    slotResponse_transmission setup leaks who past view event node slot choice action encoded
  unfold slotVisible
  by_cases permitted : countPermits ((application setup leaks).outputs past)
      (slotEnvelope setup leaks who past view event slot) = true
  · have member := membership.mpr permitted
    simp only [responseChoice, member, ↓reduceDIte, permitted, ↓reduceIte, visibleEnvelope,
      Option.bind_some, transmits, Option.map_some, envelope]
  · have notMember : slotResponse setup leaks who past view event slot choice ∉
        bounds.onePacketActions (runtime setup) leaks who past view :=
      fun member => permitted (membership.mp member)
    simp only [responseChoice, notMember, ↓reduceDIte, permitted, Bool.false_eq_true,
      ↓reduceIte, visibleEnvelope, Option.bind_some, Option.map_none]

/-- **Given what is visible, the value is as-if-honest.** At the player's turn
at a binding, when every as-if-honest choice is covered and the candidate
capacity is at least one, the joint law, in the slot tier, of the visible
outcome of the chosen response and the source choice is the law of the visible
outcome times the as-if-honest law. -/
theorem slotTier_visible_value_law (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (capacity : 1 ≤ bounds.candidateCount)
    (covered : ∀ choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (past, view))).support, CoveredBinding setup bounds event choice) :
    (slotPairs setup leaks bounds assessment who past view).map (fun pair =>
        (visibleEnvelope setup leaks who past view
          (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view))
            (slotResponse setup leaks who past view event pair.1 pair.2)).1, pair.2)) =
      ((PMF.uniformOfFinset (trembleSlots setup bounds) (trembleSlots_nonempty setup bounds)).map
          (slotVisible setup leaks who past view event)).bind fun visible =>
        (asIfHonestProfile setup leaks assessment who (some (past, view))).map
          (Prod.mk visible) := by
  rw [← bind_map_pair_map_fst]
  refine map_congr_on_support _ fun pair supported => ?_
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  obtain ⟨slot, chosen, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨value, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
  have below : slot < bounds.candidateCount := by
    have member := (PMF.mem_support_uniformOfFinset_iff _ _).mp chosen
    unfold trembleSlots at member
    rw [Finset.mem_range, max_eq_right capacity] at member
    exact member
  exact visibleEnvelope_slotResponse setup leaks bounds initial horizon scheduler who past view
    event node slot below _ (covered _ drawn)

omit [Fintype Player] in
/-- **Distinct slots or values give distinct responses** at fresh slots. -/
theorem slotResponse_injective (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
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
    (same : slotResponse setup leaks who past view event slot first =
      slotResponse setup leaks who past view event other second) :
    slot = other ∧ first.bind (encodeEventAction? setup.program event) =
      second.bind (encodeEventAction? setup.program event) := by
  obtain ⟨firstAction, firstEncoded, firstValues⟩ := firstCovered
  obtain ⟨secondAction, secondEncoded, secondValues⟩ := secondCovered
  obtain ⟨firstValue, firstSuccess, _⟩ := firstValues owner payload outputEq codeEq node
  obtain ⟨secondValue, secondSuccess, _⟩ := secondValues owner payload outputEq codeEq node
  rw [slotResponse_of_bind setup leaks who past view event node slot first firstAction
      firstEncoded,
    slotResponse_of_bind setup leaks who past view event node other second secondAction
      secondEncoded,
    (runtime setup).reactiveBinding_normal_of_fresh leaks who past view event payload _ slot
      slotFresh,
    (runtime setup).reactiveBinding_normal_of_fresh leaks who past view event payload _ other
      otherFresh, firstSuccess, secondSuccess] at same
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
      PublicationResult (L.Val payload)) = cast (congrArg EventGraph.EventField.Action outputEq)
        secondAction := by
    rw [firstSuccess, secondSuccess, openingEq]
  exact (cast_inj _).mp castEq

end Vegas
