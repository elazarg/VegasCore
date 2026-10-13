/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotMasses

/-! # Masses of the as-if-honest, slot and silence laws at offered commitments

At a binding of the player's turn whose canonical slot is fresh, the as-if-honest
response is the slot tier's response at the canonical slot
(`Vegas.honestResponse_eq_slotResponse`). Where every source choice as-if-honest
play supports is covered and every permitted prepared slot is fresh
(`Vegas.CoveredPendingBinding`), distinct covered source choices at slots within
capacity give distinct offered choices (`Vegas.slotChoiceOf_injective`). There
an offered slot-tier choice of a supported source choice has as-if-honest mass
its source mass at the canonical slot and zero elsewhere
(`Vegas.honestChoice_slotChoiceOf_apply`), slot-tier mass the uniform slot
mass times its source mass (`Vegas.slotChoice_slotChoiceOf_apply`), and
silence mass zero (`Vegas.silence_slotChoiceOf_apply`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  [Fintype Player] (bounds : MessageBounds (graph setup))

omit [Fintype Player] in
/-- At a binding of the player's turn whose canonical slot is fresh, the
as-if-honest response is the slot tier's response at the canonical slot. -/
theorem honestResponse_eq_slotResponse (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) (serial : Nat)
    (selected : canonicalFreshSlot who view.application = some serial) :
    honestResponse setup leaks assessment who past view =
      (asIfHonestProfile setup leaks assessment who (some (past, view))).map
        (slotResponse setup leaks who past view event serial) := by
  have fresh := canonicalFreshSlot_spec who view.application serial selected
  unfold honestResponse
  rw [turn]
  refine congrArg (fun response =>
    (asIfHonestProfile setup leaks assessment who (some (past, view))).map response)
    (funext fun choice => ?_)
  cases encoded : choice.bind (encodeEventAction? setup.program event) with
  | none =>
      unfold slotResponse
      rw [encoded]
  | some action =>
      obtain ⟨result, rfl⟩ : ∃ result : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) result :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      rw [slotResponse_of_bind setup leaks who past view event node serial choice _ encoded]
      simp only [cast_cast, cast_eq]
      rw [(runtime setup).reactiveBinding_normal_of_fresh leaks who past view event payload _
        serial fresh]
      exact (runtime setup).canonicalServiceDecision_binding leaks who past view event payload
        outputEq codeEq node serial selected result

variable (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- The one-packet choice of the slot tier's response at a slot to a source
choice. -/
abbrev slotChoiceOf (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) (slot : Nat)
    (choice : Option (OwnAction Player L)) :
    (onePacketModel setup leaks bounds initial horizon scheduler).Choice who (some (past, view)) :=
  responseChoice setup leaks bounds initial horizon scheduler who (some (past, view))
    (slotResponse setup leaks who past view event slot choice)

/-- **Distinct offered slot-tier choices.** At a binding of the player's turn,
where every prepared slot the count verdict permits is fresh, an offered
slot-tier choice of a covered source choice at a slot within capacity is the
slot-tier choice of no other covered source choice or slot within capacity. -/
theorem slotChoiceOf_injective (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (freshOfPermitted : ∀ slot, countPermits ((application setup leaks).outputs past)
      (slotEnvelope setup leaks who past view event slot) = true →
        view.application.candidates (.prepared slot) = .fresh)
    {slot other : Nat} (slotCapacity : slot < bounds.candidateCount)
    (otherCapacity : other < bounds.candidateCount) {first second : Option (OwnAction Player L)}
    (firstCovered : CoveredBinding setup bounds event first)
    (secondCovered : CoveredBinding setup bounds event second)
    (offered : slotResponse setup leaks who past view event slot first ∈
      bounds.onePacketActions (runtime setup) leaks who past view)
    (same : slotChoiceOf setup leaks bounds initial horizon scheduler who past view event other
        second =
      slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot first) :
    other = slot ∧ second = first := by
  classical
  obtain ⟨firstAction, firstEncoded, _⟩ := firstCovered
  obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup leaks who past view event
    node slot first firstAction firstEncoded
  have values := congrArg Subtype.val same
  have firstValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event
      slot first).1 = some (slotResponse setup leaks who past view event slot first) := by
    simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
  rw [firstValue] at values
  by_cases otherOffered : slotResponse setup leaks who past view event other second ∈
      bounds.onePacketActions (runtime setup) leaks who past view
  · have secondValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
        event other second).1 = some (slotResponse setup leaks who past view event other second) :=
      by simp only [slotChoiceOf, responseChoice, otherOffered, ↓reduceDIte]
    rw [secondValue] at values
    have responses := Option.some.inj values
    have slotFresh := freshOfPermitted slot ((slotResponse_mem_onePacket_iff setup leaks bounds who
      past view event node slot slotCapacity first ⟨firstAction, firstEncoded, ‹_›⟩).mp offered)
    have otherFresh := freshOfPermitted other ((slotResponse_mem_onePacket_iff setup leaks bounds
      who past view event node other otherCapacity second secondCovered).mp otherOffered)
    obtain ⟨slotEq, encodedEq⟩ := slotResponse_injective setup leaks bounds who past view event
      node other slot otherFresh slotFresh second first secondCovered
      ⟨firstAction, firstEncoded, ‹_›⟩ responses
    obtain ⟨secondAction, secondEncoded, _⟩ := secondCovered
    rw [secondEncoded, firstEncoded] at encodedEq
    cases Option.some.inj encodedEq
    exact ⟨slotEq, encode_injective setup event secondEncoded firstEncoded⟩
  · have secondValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
        event other second).1 = some ⟨none⟩ := by
      simp only [slotChoiceOf, responseChoice, otherOffered, ↓reduceDIte]
    rw [secondValue] at values
    have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
    rw [transmits] at silent
    cases silent

/-- **A pending binding with covered as-if-honest play.** The player's turn is a
binding of the player; every source choice as-if-honest play supports encodes
to a covered value; the candidate capacity is at least one; and every prepared
slot the count verdict permits is fresh. -/
structure CoveredPendingBinding (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload) : Prop where
  turn : view.application.publicView.ownTurn? who = some event
  node : nodeView (graph setup) event = .bind who payload outputEq codeEq
  covered : ∀ choice ∈ (asIfHonestProfile setup leaks assessment who (some (past, view))).support,
    CoveredBinding setup bounds event choice
  capacity : 1 ≤ bounds.candidateCount
  freshOfPermitted : ∀ slot, countPermits ((application setup leaks).outputs past)
    (slotEnvelope setup leaks who past view event slot) = true →
      view.application.candidates (.prepared slot) = .fresh

omit [Fintype Player] in
/-- The tremble slots are the slots within capacity, when it is at least one. -/
theorem mem_trembleSlots_iff (capacity : 1 ≤ bounds.candidateCount) (slot : Nat) :
    slot ∈ trembleSlots setup bounds ↔ slot < bounds.candidateCount := by
  unfold trembleSlots
  rw [Finset.mem_range, max_eq_right capacity]

variable {setup leaks bounds}

/-- An offered commitment at a prepared slot is within the candidate
capacity. -/
theorem offered_commitment_capacity (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (member : response ∈ (bounds.menu (runtime setup) leaks).actions who past view)
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {owner : Player} {slot : Nat}
    (packet : material.call.packet = .commitment event (owner, .prepared slot)) :
    slot < bounds.candidateCount := by
  obtain ⟨original, rawMember, normalized⟩ :=
    (((runtime setup).reactiveNormalization leaks).menu_mem
      (bounds.rawMenu (runtime setup) leaks) who past view response).mp member
  rcases original with ⟨_ | originalMaterial⟩
  · subst normalized
    cases sends
  · subst normalized
    change some _ = some material at sends
    cases Option.some.inj sends
    have allowed := ((bounds.submissions_mem _ _).mp
      ((ReactiveApplication.ResponseMenu.fromSubmissions_mem _ who past view _).mp
        rawMember)).1.1
    change originalMaterial.call.packet = _ at packet
    rw [packet] at allowed
    exact allowed


/-- **The as-if-honest mass of an offered commitment.** At a covered pending
binding with canonical slot `serial`, the as-if-honest choice gives an offered
slot-tier choice of a supported source choice its as-if-honest mass at the
canonical slot, and nothing at another slot. -/
theorem honestChoice_slotChoiceOf_apply {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who past view event payload
      outputEq codeEq) {serial : Nat}
    (selected : canonicalFreshSlot who view.application = some serial) {slot : Nat}
    {choice : Option (OwnAction Player L)}
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (past, view))).support) (slotCapacity : slot < bounds.candidateCount)
    (offered : slotResponse setup leaks who past view event slot choice ∈
      bounds.onePacketActions (runtime setup) leaks who past view) :
    honestChoice setup leaks bounds initial horizon scheduler assessment who (some (past, view))
        (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot
          choice) =
      if slot = serial then
        asIfHonestProfile setup leaks assessment who (some (past, view)) choice
      else 0 := by
  change (honestResponse setup leaks assessment who past view).map _ _ = _
  rw [honestResponse_eq_slotResponse setup leaks assessment who past view event site.turn
    site.node serial selected, PMF.map_comp]
  split
  · rename_i same
    subst same
    exact map_apply_of_injOn _ (slotChoiceOf setup leaks bounds initial horizon scheduler who past
      view event slot) choice fun other otherSupported equal =>
        (slotChoiceOf_injective setup leaks bounds initial horizon scheduler who past view event
          site.node site.freshOfPermitted slotCapacity slotCapacity (site.covered choice supported)
          (site.covered other otherSupported) offered equal).2
  · rename_i different
    apply map_apply_eq_zero_of_forall_ne
    intro other otherSupported equal
    change slotChoiceOf setup leaks bounds initial horizon scheduler who past view event serial
      other = slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot
      choice at equal
    by_cases serialCapacity : serial < bounds.candidateCount
    · exact different (slotChoiceOf_injective setup leaks bounds initial horizon scheduler who past
        view event site.node site.freshOfPermitted slotCapacity serialCapacity
        (site.covered choice supported) (site.covered other otherSupported) offered equal).1.symm
    · exfalso
      obtain ⟨action, encoded, _⟩ := site.covered choice supported
      obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup leaks who past view
        event site.node slot choice action encoded
      have values := congrArg Subtype.val equal
      have offeredValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
          event slot choice).1 = some (slotResponse setup leaks who past view event slot choice) :=
        by simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
      rw [offeredValue] at values
      by_cases otherOffered : slotResponse setup leaks who past view event serial other ∈
          bounds.onePacketActions (runtime setup) leaks who past view
      · obtain ⟨otherAction, otherEncoded, _⟩ := site.covered other otherSupported
        obtain ⟨otherMaterial, otherTransmits, otherEnvelope⟩ := slotResponse_transmission setup
          leaks who past view event site.node serial other otherAction otherEncoded
        have effective := ((bounds.mem_onePacketActions (runtime setup) leaks who past view
          _).mp otherOffered).1
        have packetEq : otherMaterial.call.packet = .commitment event (who, .prepared serial) :=
          congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
            message.payload.call) otherEnvelope
        exact serialCapacity (offered_commitment_capacity who past view _ effective
          otherMaterial otherTransmits packetEq)
      · have otherValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
            event serial other).1 = some ⟨none⟩ := by
          simp only [slotChoiceOf, responseChoice, otherOffered, ↓reduceDIte]
        rw [otherValue] at values
        have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
        rw [transmits] at silent
        cases silent

/-- At the player's turn, the slot tier as a law over one-packet choices is the
slot-tier choice of a uniform slot and an independent as-if-honest choice. -/
theorem slotChoice_eq_map {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event) :
    slotChoice setup leaks bounds initial horizon scheduler assessment who (some (past, view)) =
      (slotPairs setup leaks bounds assessment who past view).map fun pair =>
        slotChoiceOf setup leaks bounds initial horizon scheduler who past view event pair.1
          pair.2 := by
  have tier : slotTierResponse setup leaks bounds assessment who past view =
      (slotPairs setup leaks bounds assessment who past view).map fun pair =>
        slotResponse setup leaks who past view event pair.1 pair.2 := by
    simp only [slotTierResponse, turn]
  rw [slotChoice, tier, PMF.map_comp]
  congr 1

/-- **The slot-tier mass of an offered commitment.** At a covered pending
binding, the slot tier gives an offered slot-tier choice of a supported source
choice at a tremble slot the uniform slot mass times its as-if-honest mass. -/
theorem slotChoice_slotChoiceOf_apply {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who past view event payload
      outputEq codeEq) {slot : Nat} {choice : Option (OwnAction Player L)}
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (past, view))).support) (slotCapacity : slot < bounds.candidateCount)
    (offered : slotResponse setup leaks who past view event slot choice ∈
      bounds.onePacketActions (runtime setup) leaks who past view) :
    slotChoice setup leaks bounds initial horizon scheduler assessment who (some (past, view))
        (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot
          choice) =
      PMF.uniformOfFinset (trembleSlots setup bounds) (trembleSlots_nonempty setup bounds) slot *
        asIfHonestProfile setup leaks assessment who (some (past, view)) choice := by
  rw [slotChoice_eq_map initial horizon scheduler site.turn]
  have injective : ∀ pair ∈ (slotPairs setup leaks bounds assessment who past view).support,
      slotChoiceOf setup leaks bounds initial horizon scheduler who past view event pair.1
          pair.2 =
        slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot
          choice → pair = (slot, choice) := by
    intro pair pairSupported equal
    obtain ⟨pairSlot, slotDrawn, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp pairSupported
    obtain ⟨pairChoice, choiceDrawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
    dsimp only at equal
    have pairCapacity : pairSlot < bounds.candidateCount :=
      (mem_trembleSlots_iff setup bounds site.capacity pairSlot).mp
        ((PMF.mem_support_uniformOfFinset_iff _ _).mp slotDrawn)
    obtain ⟨slotEq, choiceEq⟩ := slotChoiceOf_injective setup leaks bounds initial horizon
      scheduler who past view event site.node site.freshOfPermitted slotCapacity pairCapacity
      (site.covered choice supported) (site.covered pairChoice choiceDrawn) offered equal
    rw [slotEq, choiceEq]
  have mapped := map_apply_of_injOn _ (fun pair : Nat × Option (OwnAction Player L) =>
    slotChoiceOf setup leaks bounds initial horizon scheduler who past view event pair.1 pair.2)
    (slot, choice) injective
  dsimp only at mapped
  rw [mapped]
  exact slotPairs_apply setup leaks bounds assessment who past view slot choice

/-- An offered transmitting choice is not silence. -/
theorem silence_slotChoiceOf_apply {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who past view event payload
      outputEq codeEq) {slot : Nat} {choice : Option (OwnAction Player L)}
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (past, view))).support)
    (offered : slotResponse setup leaks who past view event slot choice ∈
      bounds.onePacketActions (runtime setup) leaks who past view) :
    PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who (some (past, view)))
        (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot
          choice) = 0 := by
  classical
  refine PMF.pure_apply_of_ne _ _ fun same => ?_
  obtain ⟨action, encoded, _⟩ := site.covered choice supported
  obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup leaks who past view event
    site.node slot choice action encoded
  have values := congrArg Subtype.val same
  have offeredValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
      event slot choice).1 = some (slotResponse setup leaks who past view event slot choice) := by
    simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
  have silenceValue : (silenceChoice setup leaks bounds initial horizon scheduler who
      (some (past, view))).1 = some ⟨none⟩ := by
    simp only [silenceChoice, responseChoice]
    split <;> rfl
  rw [offeredValue, silenceValue] at values
  have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
  rw [transmits] at silent
  cases silent

end Vegas
