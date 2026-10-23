/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSilenceMasses

/-! # Silence masses at a pending binding

Along every history of the one-packet game, at a binding of the player's turn
its recall has not submitted for, when every binding value is a bounded value
and the capacity exceeds every player's number of binding events, the count
verdict permits the commitment at the canonical slot
(`Vegas.onePacket_canonical_permitted`). So the as-if-honest choice is never
silence (`Vegas.honestChoice_silence_of_pending`), and the slot tier is silence
exactly when it draws a tremble slot the count verdict rejects: its silence mass
is the share of rejected tremble slots (`Vegas.slotChoice_silence_of_pending`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] in
/-- A product law has its first factor as its first marginal. -/
private theorem bind_map_pair_map_fst_eq {α β : Type} (first : PMF α) (second : PMF β) :
    (first.bind fun x => second.map (Prod.mk x)).map Prod.fst = first := by
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  have constant : ∀ x : α, second.map (fun _ => x) = PMF.pure x :=
    fun x => PMF.map_const second x
  change (first.bind fun x => second.map (fun _ => x)) = first
  simp only [constant, PMF.bind_pure]

/-- At a binding of the player's turn whose canonical slot is fresh, the
canonical decision of an encoded source choice is the slot tier's response at
the canonical slot. -/
theorem canonical_eq_slotResponse (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) (serial : Nat)
    (selected : canonicalFreshSlot who view.application = some serial)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action) :
    (runtime setup).canonicalServiceDecision leaks who past view event action =
      slotResponse setup leaks who past view event serial choice := by
  have fresh := canonicalFreshSlot_spec who view.application serial selected
  obtain ⟨result, rfl⟩ : ∃ result : PublicationResult (L.Val payload),
      action = cast (congrArg EventGraph.EventField.Action outputEq.symm) result :=
    ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
  rw [slotResponse_of_bind setup leaks who past view event node serial choice _ encoded]
  simp only [cast_cast, cast_eq]
  rw [(runtime setup).reactiveBinding_normal_of_fresh leaks who past view event payload _
    serial fresh]
  exact (runtime setup).canonicalServiceDecision_binding leaks who past view event payload
    outputEq codeEq node serial selected result

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The canonical slot is permitted.** Along every history of the one-packet
game, at a binding of the player's turn its recall has not submitted for, the
count verdict permits the commitment at the canonical slot. -/
theorem onePacket_canonical_permitted (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) (serial : Nat)
    (selected : canonicalFreshSlot who
      (control.execution.observe (application setup leaks) who).application = some serial) :
    countPermits ((application setup leaks).outputs (control.execution.recall who))
      (slotEnvelope setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event serial) = true := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  obtain ⟨choice, supported⟩ := (asIfHonestProfile setup leaks assessment who
    (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who))).support_nonempty
  obtain ⟨action, encoded, _⟩ :=
    onePacket_honest_covered assessment covers trace who event turn choice supported
  have decision := canonical_eq_slotResponse who (control.execution.recall who)
    (control.execution.observe (application setup leaks) who) event node serial selected choice
    action encoded
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup leaks who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who)
    event node serial choice action encoded
  rw [← decision] at transmits
  rw [← envelope]
  exact canonicalServiceDecision_countPermits rawTrace who event turn unsent action material
    transmits

/-- **No silence at a pending binding.** Along every history of the one-packet
game, at a binding of the player's turn its recall has not submitted for, the
as-if-honest choice gives silence no mass. -/
theorem honestChoice_silence_of_pending (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    honestChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who))) = 0 := by
  obtain ⟨serial, selected⟩ := onePacket_canonicalFreshSlot_exists trace who
  have serialCapacity : serial < bounds.candidateCount :=
    lt_of_le_of_lt (canonicalFreshSlot_le_bindingEvents bounds trace who selected)
      (capacity who)
  have permitted := onePacket_canonical_permitted assessment covers trace who event turn unsent
    node serial selected
  change (honestResponse setup leaks assessment who _ _).map _ _ = 0
  rw [honestResponse_eq_slotResponse setup leaks assessment who _ _ event turn node serial
    selected, PMF.map_comp]
  apply map_apply_eq_zero_of_forall_ne
  intro choice supported same
  have covered := onePacket_honest_covered assessment covers trace who event turn choice supported
  have offered := (slotResponse_mem_onePacket_iff setup leaks bounds who _ _ event node serial
    serialCapacity choice covered).mpr permitted
  obtain ⟨action, encoded, _⟩ := covered
  obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup leaks who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who)
    event node serial choice action encoded
  have values := congrArg Subtype.val same
  change (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who _
    (slotResponse setup leaks who _ _ event serial choice)).1 =
      (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who _).1 at values
  simp only [responseChoice, offered, silenceChoice,
    bounds.silence_onePacket (runtime setup) leaks who, ↓reduceDIte] at values
  have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
  rw [transmits] at silent
  cases silent

open Classical in
/-- **Silence of the slot tier at a pending binding.** Along every history of
the one-packet game, at a binding of the player's turn, the slot tier gives
silence the share of tremble slots whose commitment the count verdict rejects. -/
theorem slotChoice_silence_of_pending (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who))) =
      ((trembleSlots setup bounds).filter fun slot =>
          countPermits ((application setup leaks).outputs (control.execution.recall who))
            (slotEnvelope setup leaks who (control.execution.recall who)
              (control.execution.observe (application setup leaks) who) event slot) = false).card /
        (trembleSlots setup bounds).card := by
  have capacityOne : 1 ≤ bounds.candidateCount :=
    Nat.one_le_iff_ne_zero.mpr fun zero => by
      have := capacity who
      omega
  let rejected : Set Nat := {slot | countPermits ((application setup leaks).outputs
    (control.execution.recall who)) (slotEnvelope setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event slot) = false}
  let silence := silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
    (some (control.execution.recall who, control.execution.observe (application setup leaks) who))
  let pairs := slotPairs setup leaks bounds assessment who (control.execution.recall who)
    (control.execution.observe (application setup leaks) who)
  let tier := fun pair : Nat × Option (OwnAction Player L) =>
    slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event pair.1 pair.2
  -- On the support, the tier is silence exactly at a rejected slot.
  have agree : (tier ⁻¹' {silence}) ∩ pairs.support =
      (Prod.fst ⁻¹' rejected) ∩ pairs.support := by
    ext ⟨slot, choice⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    refine and_congr_left fun drawn => ?_
    obtain ⟨drawnSlot, slotDrawn, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp drawn
    obtain ⟨drawnChoice, choiceDrawn, pairEq⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
    cases pairEq
    have slotCapacity : slot < bounds.candidateCount :=
      (mem_trembleSlots_iff setup bounds capacityOne slot).mp
        ((PMF.mem_support_uniformOfFinset_iff _ _).mp slotDrawn)
    have covered := onePacket_honest_covered assessment covers trace who event turn choice
      choiceDrawn
    have offeredIff := slotResponse_mem_onePacket_iff setup leaks bounds who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event node slot slotCapacity choice covered
    obtain ⟨action, encoded, _⟩ := covered
    obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event node slot choice action encoded
    change slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who _ _ event slot
      choice = silence ↔ _ = false
    constructor
    · intro same
      by_contra notRejected
      have offered := offeredIff.mpr (Bool.not_eq_false _ ▸ notRejected)
      have values := congrArg Subtype.val same
      simp only [slotChoiceOf, responseChoice, offered, silence, silenceChoice,
        bounds.silence_onePacket (runtime setup) leaks who, ↓reduceDIte] at values
      have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
      rw [transmits] at silent
      cases silent
    · intro isRejected
      have absent : slotResponse setup leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event slot choice ∉
            bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
              (control.execution.observe (application setup leaks) who) := fun offered => by
        rw [offeredIff.mp offered] at isRejected
        cases isRejected
      exact responseChoice_of_not_offered who _ _ _ absent
  have mass : (pairs.map tier) silence = (pairs.map Prod.fst).toOuterMeasure rejected := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_apply_inter_support,
      agree, PMF.toOuterMeasure_apply_inter_support]
  rw [slotChoice_eq_map (initialLaw setup) horizon scheduler turn]
  change (pairs.map tier) silence = _
  rw [mass]
  have marginal : pairs.map Prod.fst = PMF.uniformOfFinset (trembleSlots setup bounds)
      (trembleSlots_nonempty setup bounds) :=
    bind_map_pair_map_fst_eq _ _
  rw [marginal, PMF.toOuterMeasure_uniformOfFinset_apply]
  congr 3
  exact Finset.filter_congr_decidable _ _ _

end Vegas
