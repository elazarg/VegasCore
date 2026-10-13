/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketBindingSite

/-! # Component masses at realized commitments

Along every history of the one-packet game, at a binding of the player's turn,
when every binding value is a bounded value and the capacity exceeds every
player's number of binding events, a realized commitment with positive content
commits at a slot within capacity
(`Vegas.onePacket_binding_transmission_masses`). There the as-if-honest choice
gives the realized choice its content factor at the canonical slot and nothing
at another slot, the slot tier gives it the content factor over the number of
tremble slots, and silence gives it nothing.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Masses at a realized commitment.** Along every history of the one-packet
game, at a binding of the player's turn, a realized commitment with positive
content commits at a slot within capacity, and for the one-packet choice
sending it, the as-if-honest mass is the content factor at the canonical slot
and zero elsewhere, the slot-tier mass is the content factor over the number of
tremble slots, and the silence mass is zero. -/
theorem onePacket_binding_transmission_masses
    (assessment : setup.intendedModel.BehavioralAssessment)
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
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material)
    (positive : 0 < contentFactor setup leaks assessment who control.execution
      (control.execution.respond (application setup leaks) who response) response)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who)))
    (chosen : choice.1 = some response) :
    ∃ serial canonical, serial < bounds.candidateCount ∧
      canonicalFreshSlot who
        (control.execution.observe (application setup leaks) who).application = some canonical ∧
      (∃ value, response = slotResponse setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event serial
        (sourceOfValue setup event outputEq value)) ∧
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
          _ choice).toReal =
        contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response *
          (if serial = canonical then 1 else 0) ∧
      (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
          _ choice).toReal =
        contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response *
          (1 / ((trembleSlots setup bounds).card : ℝ)) ∧
      (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who _)
          choice).toReal =
        contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response * 0 := by
  have capacityOne : 1 ≤ bounds.candidateCount :=
    Nat.one_le_iff_ne_zero.mpr fun zero => by
      have := capacity who
      omega
  obtain ⟨serial, value, slotCapacity, responseEq, contentEq⟩ :=
    onePacket_commitment_realized assessment trace who event turn node response member material
      sends positive
  have site := onePacket_coveredPendingBinding assessment covers capacityOne trace who event turn
    node
  obtain ⟨canonical, selected⟩ := onePacket_canonicalFreshSlot_exists trace who
  have supported : sourceOfValue setup event outputEq value ∈ (asIfHonestProfile setup leaks
      assessment who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support := by
    rw [contentEq] at positive
    exact (PMF.mem_support_iff _ _).mpr (ENNReal.toReal_pos_iff.mp positive).1.ne'
  have offered : slotResponse setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event serial
      (sourceOfValue setup event outputEq value) ∈ bounds.onePacketActions (runtime setup) leaks
        who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) :=
    responseEq ▸ member
  have choiceEq : choice = slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler
      who (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event serial (sourceOfValue setup event outputEq value) := by
    apply Subtype.ext
    rw [chosen, responseEq]
    simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
  subst choiceEq
  refine ⟨serial, canonical, slotCapacity, selected, ⟨value, responseEq⟩, ?_, ?_, ?_⟩
  · rw [honestChoice_slotChoiceOf_apply (initialLaw setup) horizon scheduler site selected
      supported slotCapacity offered, contentEq]
    split
    · rw [mul_one]
    · rw [ENNReal.toReal_zero, mul_zero]
  · rw [slotChoice_slotChoiceOf_apply (initialLaw setup) horizon scheduler site supported
      slotCapacity offered, contentEq,
      PMF.uniformOfFinset_apply_of_mem (trembleSlots_nonempty setup bounds)
        ((mem_trembleSlots_iff setup bounds capacityOne serial).mpr slotCapacity),
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, mul_comm, one_div]
  · rw [silence_slotChoiceOf_apply (initialLaw setup) horizon scheduler site supported offered,
      ENNReal.toReal_zero, mul_zero]

end Vegas
