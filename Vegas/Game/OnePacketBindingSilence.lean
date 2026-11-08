/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSilenceMasses
import GameTheoryExtensions.Math.Probability.Uniform

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
  {timeouts : EventTimeouts (graph setup)}
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

/-- At an active player's binding turn whose canonical slot is fresh, the
canonical decision of an encoded source choice is the slot tier's response at
the canonical slot. -/
private theorem canonical_eq_slotResponse (who : Player)
    (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (event : (graph setup).EventId)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) (serial : Nat)
    (active : who ∉ view.application.publicView.observation.defaulted)
    (selected : canonicalFreshSlot who view.application = some serial)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action) :
    (canonicalServiceDecision timeouts) leaks who past view event action =
      slotResponse setup timeouts leaks who past view event serial choice := by
  have fresh := canonicalFreshSlot_spec who view.application serial selected
  obtain ⟨result, rfl⟩ : ∃ result : Option (PublicationResult (L.Val payload)),
      action = cast (congrArg EventGraph.EventField.Action outputEq.symm) result :=
    ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
  rw [slotResponse_of_bind setup timeouts leaks who past view event node serial choice _ encoded]
  simp only [cast_cast, cast_eq]
  cases result with
  | none =>
      exact (canonicalServiceDecision_binding_none timeouts) leaks who past view event
        who payload outputEq codeEq node
  | some value =>
      dsimp only
      rw [(reactiveBinding_normal_of_fresh timeouts) leaks who past view event payload _
        serial fresh]
      exact (canonicalServiceDecision_binding timeouts) leaks who past view event payload
        outputEq codeEq node active serial selected value

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **The canonical slot is permitted.** Along every history of the one-packet
game, at a binding of the player's turn its recall has not submitted for, the
count verdict permits the commitment at the canonical slot. -/
theorem onePacket_canonical_permitted (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (eventRecorded timeouts) leaks (control.execution.logs who) event = false)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) (serial : Nat)
    (selected : canonicalFreshSlot who
      (control.execution.observe (application setup timeouts leaks) who).application = some
        serial) :
    countPermits ((application setup timeouts leaks).outputs (control.execution.logs who))
      (slotEnvelope setup timeouts leaks who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who) event serial) = true
          := by
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  obtain ⟨choice, supported⟩ := (asIfHonestProfile setup timeouts leaks assessment who
    (some (control.execution.logs who,
      control.execution.observe (application setup timeouts leaks) who))).support_nonempty
  obtain ⟨action, encoded, values⟩ :=
    onePacket_honest_covered (timeouts := timeouts) assessment covers trace who event turn choice
      supported
  obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq node
  have active := control.execution.application.active_of_ready_owned
    (legalFacts setup leaks horizon scheduler control rawTrace).quiescent
    ((control.execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1)
    (PublicView.ownTurn?_spec _ who event turn).2
  have decision := canonical_eq_slotResponse (timeouts := timeouts) who (control.execution.logs who)
    (control.execution.observe (application setup timeouts leaks) who) event node serial active
      selected
      choice
    action encoded
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup timeouts leaks who
    (control.execution.logs who) (control.execution.observe (application setup timeouts leaks) who)
    event node serial choice action encoded (by rw [successful]; rfl)
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
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (eventRecorded timeouts) leaks (control.execution.logs who) event = false)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))
        (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.logs who,
            control.execution.observe (application setup timeouts leaks) who))) = 0 := by
  obtain ⟨serial, selected⟩ := onePacket_canonicalFreshSlot_exists (timeouts := timeouts) trace who
  have serialCapacity : serial < bounds.candidateCount :=
    lt_of_le_of_lt (canonicalFreshSlot_le_bindingEvents (timeouts := timeouts) bounds trace who
      selected)
      (capacity who)
  have permitted := onePacket_canonical_permitted (timeouts := timeouts) assessment covers trace who
    event turn unsent
    node serial selected
  change (honestResponse setup timeouts leaks assessment who _ _).map _ _ = 0
  have site := onePacket_coveredPendingBinding (timeouts := timeouts) assessment covers
    (Nat.one_le_iff_ne_zero.mpr fun zero => by have := capacity who; omega)
    trace who event turn node
  rw [honestResponse_eq_slotResponse setup timeouts leaks assessment who _ _ event turn node serial
    site.active selected, PMF.map_comp]
  apply map_apply_eq_zero_of_forall_ne
  intro choice supported same
  have covered := onePacket_honest_covered (timeouts := timeouts) assessment covers trace who event
    turn choice supported
  have offered := (slotResponse_mem_onePacket_iff setup timeouts leaks bounds who _ _ event node
    serial
    serialCapacity choice covered).mpr permitted
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq node
  obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup timeouts leaks who
    (control.execution.logs who) (control.execution.observe (application setup timeouts leaks) who)
    event node serial choice action encoded (by rw [successful]; rfl)
  have values := congrArg Subtype.val same
  change (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who _
    (slotResponse setup timeouts leaks who _ _ event serial choice)).1 =
      (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who _).1
        at values
  simp only [responseChoice, offered, silenceChoice,
    bounds.silence_onePacket timeouts leaks who, ↓reduceDIte] at values
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
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.logs who,
          control.execution.observe (application setup timeouts leaks) who))
        (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.logs who,
            control.execution.observe (application setup timeouts leaks) who))) =
      ((trembleSlots setup bounds).filter fun slot =>
          countPermits ((application setup timeouts leaks).outputs (control.execution.logs who))
            (slotEnvelope setup timeouts leaks who (control.execution.logs who)
              (control.execution.observe (application setup timeouts leaks) who) event slot) =
                false).card /
        (trembleSlots setup bounds).card := by
  have capacityOne : 1 ≤ bounds.candidateCount :=
    Nat.one_le_iff_ne_zero.mpr fun zero => by
      have := capacity who
      omega
  let rejected : Set Nat := {slot | countPermits ((application setup timeouts leaks).outputs
    (control.execution.logs who)) (slotEnvelope setup timeouts leaks who
      (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) event slot) = false}
  let silence := silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
    (some (control.execution.logs who, control.execution.observe (application setup timeouts
      leaks) who))
  let pairs := slotPairs setup timeouts leaks bounds assessment who (control.execution.logs who)
    (control.execution.observe (application setup timeouts leaks) who)
  let tier := fun pair : Nat × Option (OwnAction Player L) =>
    slotChoiceOf setup timeouts leaks bounds (initialLaw setup) horizon scheduler who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who)
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
        ((mem_support_uniformOn_iff _ _).mp slotDrawn)
    have covered := onePacket_honest_covered (timeouts := timeouts) assessment covers trace who
      event turn choice
      choiceDrawn
    have offeredIff := slotResponse_mem_onePacket_iff setup timeouts leaks bounds who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who)
      event node slot slotCapacity choice covered
    obtain ⟨action, encoded, values⟩ := covered
    obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq node
    obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup timeouts leaks who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who)
      event node slot choice action encoded (by rw [successful]; rfl)
    change slotChoiceOf setup timeouts leaks bounds (initialLaw setup) horizon scheduler who _ _
      event slot
      choice = silence ↔ _ = false
    constructor
    · intro same
      by_contra notRejected
      have offered := offeredIff.mpr (Bool.not_eq_false _ ▸ notRejected)
      have values := congrArg Subtype.val same
      simp only [slotChoiceOf, responseChoice, offered, silence, silenceChoice,
        bounds.silence_onePacket timeouts leaks who, ↓reduceDIte] at values
      have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
      rw [transmits] at silent
      cases silent
    · intro isRejected
      have absent : slotResponse setup timeouts leaks who (control.execution.logs who)
          (control.execution.observe (application setup timeouts leaks) who) event slot choice ∉
            bounds.onePacketActions timeouts leaks who (control.execution.logs who)
              (control.execution.observe (application setup timeouts leaks) who) := fun offered
                => by
        rw [offeredIff.mp offered] at isRejected
        cases isRejected
      exact responseChoice_of_not_offered (timeouts := timeouts) who _ _ _ absent
  have mass : (pairs.map tier) silence = (pairs.map Prod.fst).toOuterMeasure rejected := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_apply_inter_support,
      agree, PMF.toOuterMeasure_apply_inter_support]
  rw [slotChoice_eq_map (timeouts := timeouts) (initialLaw setup) horizon scheduler turn]
  change (pairs.map tier) silence = _
  rw [mass]
  have marginal : pairs.map Prod.fst = uniformOn (trembleSlots setup bounds)
      (trembleSlots_nonempty setup bounds) :=
    bind_map_pair_map_fst_eq _ _
  rw [marginal, uniformOn_toOuterMeasure_apply]
  congr 3
  exact Finset.filter_congr_decidable _ _ _

end Vegas
