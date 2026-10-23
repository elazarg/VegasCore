/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketRevealStep

/-! # Masses of a response step in every case

Along every history of the one-packet game, where the responder's disclosure is
canonical, the as-if-honest law, every late option, silence and the slot tier
give a realized response with positive content its content factor times the
factors read from the responder's keys before and after the response
(`Vegas.onePacket_step_masses`): without a pending event, at a pending binding,
and at a pending reveal.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Unfold

variable {before after : LateKey setup leaks}

theorem honestFactor_of_settled (settled : before.pending = none) :
    honestFactor before after = 1 := by
  unfold honestFactor
  rw [settled]

theorem honestFactor_of_bind {event : (graph setup).EventId} (pending : before.pending = some event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    honestFactor before after = pendingBindingHonestFactor before after := by
  unfold honestFactor
  rw [pending]
  dsimp only
  rw [node]

theorem honestFactor_of_resolve {event : (graph setup).EventId}
    (pending : before.pending = some event) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    honestFactor before after = transmitFactor after := by
  unfold honestFactor
  rw [pending]
  dsimp only
  rw [node]

variable (bounds : MessageBounds (graph setup))

theorem slotTierFactor_of_settled (settled : before.pending = none) :
    slotTierFactor bounds before after = 1 := by
  unfold slotTierFactor
  rw [settled]

theorem slotTierFactor_of_bind {event : (graph setup).EventId}
    (pending : before.pending = some event) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    slotTierFactor bounds before after = pendingBindingSlotFactor bounds before after event := by
  unfold slotTierFactor
  rw [pending]
  dsimp only
  rw [node]

theorem slotTierFactor_of_resolve {event : (graph setup).EventId}
    (pending : before.pending = some event) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    slotTierFactor bounds before after = transmitFactor after := by
  unfold slotTierFactor
  rw [pending]
  dsimp only
  rw [node]

theorem lateOptionFactor_none {slots : Nat} :
    lateOptionFactor (slots := slots) bounds before after none = silenceFactor after := rfl

theorem lateOptionFactor_of_settled {slots : Nat} (settled : before.pending = none)
    (option : LateOption slots) :
    lateOptionFactor bounds before after option = silenceFactor after := by
  cases option with
  | none => rfl
  | some slot =>
      unfold lateOptionFactor
      rw [settled]

theorem lateOptionFactor_of_resolve {slots : Nat} {event : (graph setup).EventId}
    (pending : before.pending = some event) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (slot : Fin slots) :
    lateOptionFactor bounds before after (some slot) = transmitFactor after := by
  unfold lateOptionFactor
  rw [pending]
  dsimp only
  rw [node]

end Unfold

section Masses

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Masses of a response step.** Along every history of the one-packet game,
when every binding and publication value is a bounded value, the capacity
exceeds every player's number of binding events and the responder's disclosure
is canonical, the as-if-honest law, every late option, silence and the slot
tier give a realized response with positive content its content factor times
the factors read from the responder's keys before and after the response. -/
theorem onePacket_step_masses (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (canonical : DisclosureCanonical setup leaks bounds who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who))
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (positive : 0 < contentFactor setup leaks assessment who control.execution
      (control.execution.respond (application setup leaks) who response) response)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who)))
    (chosen : choice.1 = some response) :
    (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response *
        honestFactor
          (LateKey.ofView setup leaks who (control.execution.recall who)
            (control.execution.observe (application setup leaks) who))
          (LateKey.ofView setup leaks who
            ((control.execution.respond (application setup leaks) who response).recall who)
            ((control.execution.respond (application setup leaks) who response).observe
              (application setup leaks) who)) ∧
    (∀ {slots : Nat} (option : LateOption slots),
      (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who _
          option choice).toReal =
        contentFactor setup leaks assessment who control.execution
            (control.execution.respond (application setup leaks) who response) response *
          lateOptionFactor bounds
            (LateKey.ofView setup leaks who (control.execution.recall who)
              (control.execution.observe (application setup leaks) who))
            (LateKey.ofView setup leaks who
              ((control.execution.respond (application setup leaks) who response).recall who)
              ((control.execution.respond (application setup leaks) who response).observe
                (application setup leaks) who)) option) ∧
    (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who _)
        choice).toReal =
      contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response *
        silenceFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who response).recall who)
          ((control.execution.respond (application setup leaks) who response).observe
            (application setup leaks) who)) ∧
    (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response *
        slotTierFactor bounds
          (LateKey.ofView setup leaks who (control.execution.recall who)
            (control.execution.observe (application setup leaks) who))
          (LateKey.ofView setup leaks who
            ((control.execution.respond (application setup leaks) who response).recall who)
            ((control.execution.respond (application setup leaks) who response).observe
              (application setup leaks) who)) := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have keyPending := LateKey.ofView_pending rawTrace who
  cases pending : pendingEvent setup leaks who (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who)) with
  | none =>
      rw [pending] at keyPending
      have settled : ∀ event, control.execution.application.publicView.ownTurn? who =
          some event → (runtime setup).eventRecorded leaks (control.execution.recall who) event =
            true := by
        intro event turn
        by_contra unrecorded
        have := pendingEvent_of_spec (setup := setup) (leaks := leaks)
          (past := control.execution.recall who)
          (view := control.execution.observe (application setup leaks) who) turn
          (Bool.eq_false_iff.mpr unrecorded)
        rw [pending] at this
        cases this
      obtain ⟨silent, contentOne, honestOne, slotOne, silenceOne⟩ :=
        onePacket_settled_operational_masses assessment trace who settled response member
          positive choice chosen
      subst silent
      have choiceEq := choice_eq_silenceChoice who _ _ choice chosen
      subst choiceEq
      have lastNone : (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup leaks) who ⟨none⟩).observe
            (application setup leaks) who)).lastEmitted = none := by
        rw [LateKey.respond_lastEmitted]
        rfl
      have silenceOneFactor : silenceFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup leaks) who ⟨none⟩).observe
            (application setup leaks) who)) = 1 := by
        unfold silenceFactor
        rw [lastNone]
        simp
      rw [contentOne, honestFactor_of_settled keyPending,
        slotTierFactor_of_settled bounds keyPending, silenceOneFactor, honestOne, slotOne,
        silenceOne, ENNReal.toReal_one]
      refine ⟨by ring, fun option => ?_, by ring, by ring⟩
      rw [lateOptionFactor_of_settled bounds keyPending, silenceOneFactor,
        onePacket_settled_lateChoice assessment trace who pending option, ENNReal.toReal_one]
      ring
  | some event =>
      rw [pending] at keyPending
      obtain ⟨turn, _, owned, unsent⟩ := pendingEvent_spec (setup := setup) pending
      cases node : nodeView (graph setup) event with
      | sample payload law outputEq codeEq =>
          have none := nodeView_sample_actor outputEq codeEq
          rw [owned] at none
          cases none
      | bind owner payload outputEq codeEq =>
          have ownerEq : owner = who :=
            Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
          subst ownerEq
          obtain ⟨honestMass, silenceMass, slotMass⟩ :=
            onePacket_pendingBinding_operational_masses assessment covers capacity trace owner
              event turn unsent node response member positive choice chosen
          rw [honestFactor_of_bind keyPending node, slotTierFactor_of_bind bounds keyPending node]
          exact ⟨honestMass, fun option => onePacket_pendingBinding_lateChoice assessment covers
            capacity trace owner event turn unsent node response member positive choice chosen
            option, silenceMass, slotMass⟩
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨honestMass, lateMass, silenceMass, slotMass⟩ :=
            onePacket_pendingReveal_masses assessment covers trace who event turn unsent node
              canonical response member positive choice chosen
          rw [honestFactor_of_resolve keyPending node,
            slotTierFactor_of_resolve bounds keyPending node]
          refine ⟨honestMass, fun option => ?_, silenceMass, slotMass⟩
          cases option with
          | none =>
              rw [lateOptionFactor_none, lateChoice_none]
              exact silenceMass
          | some slot =>
              rw [lateOptionFactor_of_resolve bounds keyPending node]
              exact lateMass slot

end Masses

end Vegas
