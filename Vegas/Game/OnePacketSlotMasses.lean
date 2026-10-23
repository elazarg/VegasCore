/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotVisibility

/-! # Masses of slot-trembled laws at a realized commitment

A law pushed forward along a map that is injective on its support gives the
image of a point the point's own mass (`Vegas.map_apply_of_injOn`), and gives
zero to anything off the image of its support
(`Vegas.map_apply_eq_zero_of_forall_ne`). Source choices are determined by
their encoding at an event (`Vegas.encode_injective`).

At a binding of the player's turn, every commitment the one-packet menu offers
at a fresh prepared slot with an opening of the bound type is the slot tier's
response to the source choice decoded from that value
(`Vegas.onePacket_commitment_eq_slotResponse`): the menu holds normal forms,
and the count verdict leaves no evidence.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime

/-- **Pushforward along a map injective on the support.** -/
theorem map_apply_of_injOn {α β : Type} (law : PMF α) (f : α → β) (x : α)
    (injective : ∀ y ∈ law.support, f y = f x → y = x) : law.map f (f x) = law x := by
  classical
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y different
    by_cases supported : y ∈ law.support
    · have : f x ≠ f y := fun same => different (injective y supported same.symm)
      simp [this]
    · simp [(PMF.apply_eq_zero_iff law y).mpr supported]

/-- A pushforward gives zero to a point no supported point maps to. -/
theorem map_apply_eq_zero_of_forall_ne {α β : Type} (law : PMF α) (f : α → β) (target : β)
    (avoided : ∀ y ∈ law.support, f y ≠ target) : law.map f target = 0 := by
  rw [PMF.apply_eq_zero_iff, PMF.support_map]
  rintro ⟨y, supported, same⟩
  exact avoided y supported same

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- **Source choices are determined by their encoding at an event.** -/
theorem encode_injective (event : (graph setup).EventId)
    {first second : Option (OwnAction Player L)} {action : (graph setup).Action event}
    (firstEncoded : first.bind (encodeEventAction? setup.program event) = some action)
    (secondEncoded : second.bind (encodeEventAction? setup.program event) = some action) :
    first = second := by
  cases first with
  | none => cases firstEncoded
  | some firstAction =>
      cases second with
      | none => cases secondEncoded
      | some secondAction =>
          have firstDecoded := decodeEventAction_encodeEventAction?_eq_some setup.program event
            firstAction action firstEncoded
          have secondDecoded := decodeEventAction_encodeEventAction?_eq_some setup.program event
            secondAction action secondEncoded
          rw [firstDecoded] at secondDecoded
          exact congrArg some (Option.some.inj secondDecoded)

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source choice a successful binding value decodes to at a binding
event. -/
def sourceOfValue (event : (graph setup).EventId) {owner : Player} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (value : L.Val payload) : Option (OwnAction Player L) :=
  decodeEventAction setup.program event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) (PublicationResult.success value))

/-- The source choice decoded from a value encodes back to it. -/
theorem sourceOfValue_encoded (event : (graph setup).EventId) {owner : Player} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (value : L.Val payload) :
    (sourceOfValue setup event outputEq value).bind (encodeEventAction? setup.program event) =
      some (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.success value)) := by
  have owned := nodeView_bind_actor outputEq codeEq
  cases decoded : sourceOfValue setup event outputEq value with
  | none =>
      exfalso
      have ownerEq := decodeEventAction_owner setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.success value))
      unfold sourceOfValue at decoded
      rw [decoded, Option.map_none, eventOwner?_eq_actor] at ownerEq
      have actorNone : (graph setup).actor? event = none := ownerEq.symm
      rw [owned] at actorNone
      cases actorNone
  | some sourceAction =>
      exact encodeEventAction?_decodeEventAction_eq_some setup.program event _ sourceAction
        decoded

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **Offered commitments are slot-tier responses.** At a binding of the
player's turn, a response of the one-packet menu committing at a fresh prepared
slot with an opening of the bound type is the slot tier's response, at that
slot, to the source choice decoded from the opened value. -/
theorem onePacket_commitment_eq_slotResponse (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) (serial : Nat)
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (fresh : view.application.candidates (.prepared serial) = .fresh) (value : L.Val payload)
    (opened : material.call.opening = some ⟨payload, value⟩) :
    response = slotResponse setup leaks who past view event serial
      (sourceOfValue setup event outputEq value) := by
  obtain ⟨effective, permits⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who past view
    response).mp member
  have normal := ((runtime setup).reactiveNormalization leaks).menu_normal
    (bounds.rawMenu (runtime setup) leaks) who past view response effective
  rcases response with ⟨transmission⟩
  change transmission = some material at sends
  subst sends
  have materialNormal : material.normalizeReactive who view.application
      (ReactiveApplication.ResponseMenu.knownPackets past view) = material := by
    have := congrArg ReactiveApplication.Action.transmission normal
    exact Option.some.inj this
  have resolved : material.evidence.resolve who
      (material.call.candidateAfter who view.application.candidates)
      (ReactiveApplication.ResponseMenu.knownPackets past view) = none := by
    rcases permits with silent | ⟨other, otherSends, permitted⟩
    · cases silent
    · change some material = some other at otherSends
      cases Option.some.inj otherSends
      have verdict := ((countPermits_eq_true_iff _ _).mp permitted).2.1
      have callEq : ((runtime setup).localEnvelope leaks who past view
          material).payload.call = .commitment event (who, .prepared serial) := packet
      unfold CountCallCorrect at verdict
      simp only [callEq] at verdict
      exact verdict.2.1
  have evidenceNone : material.evidence = .none := by
    have evidence := congrArg WitnessedSubmission.evidence materialNormal
    change EvidenceRequest.canonical (ReactiveApplication.ResponseMenu.knownPackets past view)
      (material.evidence.resolve who (material.call.candidateAfter who view.application.candidates)
        (ReactiveApplication.ResponseMenu.knownPackets past view)) = material.evidence at evidence
    rw [resolved] at evidence
    exact evidence.symm
  rw [slotResponse_of_bind setup leaks who past view event node serial _ _
      (sourceOfValue_encoded setup event outputEq codeEq value),
    (runtime setup).reactiveBinding_normal_of_fresh leaks who past view event payload _ serial
      fresh]
  rcases material with ⟨⟨materialPacket, materialOpening⟩, materialEvidence⟩
  change materialPacket = _ at packet
  change materialOpening = _ at opened
  change materialEvidence = _ at evidenceNone
  subst packet opened evidenceNone
  simp [EventGraphRuntime.reactiveBinding]

end Vegas
