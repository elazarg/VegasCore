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
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Unfold

variable {before after : LateKey setup timeouts leaks}

theorem honestFactor_of_settled (settled : before.pending = none) :
    honestFactor (timeouts := timeouts) before after = 1 := by
  unfold honestFactor
  rw [settled]

theorem honestFactor_of_bind {event : (graph setup).EventId} (pending : before.pending = some event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    honestFactor (timeouts := timeouts) before after = pendingBindingHonestFactor (timeouts :=
      timeouts) before after := by
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
    honestFactor (timeouts := timeouts) before after = transmitFactor (timeouts := timeouts)
      after := by
  unfold honestFactor
  rw [pending]
  dsimp only
  rw [node]

variable (bounds : MessageBounds (graph setup))

theorem slotTierFactor_of_settled (settled : before.pending = none) :
    slotTierFactor (timeouts := timeouts) bounds before after = 1 := by
  unfold slotTierFactor
  rw [settled]

theorem slotTierFactor_of_bind {event : (graph setup).EventId}
    (pending : before.pending = some event) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    slotTierFactor (timeouts := timeouts) bounds before after = pendingBindingSlotFactor
      (timeouts :=
      timeouts) bounds before after event := by
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
    slotTierFactor (timeouts := timeouts) bounds before after = transmitFactor (timeouts :=
      timeouts)
      after := by
  unfold slotTierFactor
  rw [pending]
  dsimp only
  rw [node]

theorem lateOptionFactor_none {slots : Nat} :
    lateOptionFactor (timeouts := timeouts) (slots := slots) bounds before after none =
      silenceFactor (timeouts := timeouts) after := rfl

theorem lateOptionFactor_of_settled {slots : Nat} (settled : before.pending =
  none)
    (option : LateOption slots) :
    lateOptionFactor (timeouts := timeouts) bounds before after option = silenceFactor (timeouts :=
      timeouts) after := by
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
    lateOptionFactor (timeouts := timeouts) bounds before after (some slot) = transmitFactor
      (timeouts := timeouts) after := by
  unfold lateOptionFactor
  rw [pending]
  dsimp only
  rw [node]

end Unfold

section Masses

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Masses of a response step.** Along every history of the one-packet game,
when every binding and publication value is a bounded value, the capacity
exceeds every player's number of binding events and the responder's disclosure
is canonical, the as-if-honest law, every late option, silence and the slot
tier give a realized response with positive content its content factor times
the factors read from the responder's keys before and after the response. -/
theorem onePacket_step_masses (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (canonical : DisclosureCanonical setup timeouts leaks bounds who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who))
    (response : (application setup timeouts leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (control.execution.logs who) (control.execution.observe (application setup timeouts leaks)
        who))
    (positive : 0 < contentFactor setup timeouts leaks assessment who control.execution
      (control.execution.respond (application setup timeouts leaks) who response) response)
    (choice : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who)))
    (chosen : choice.1 = some response) :
    (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup timeouts leaks assessment who control.execution
          (control.execution.respond (application setup timeouts leaks) who response) response *
        honestFactor (timeouts := timeouts)
          (LateKey.ofView setup timeouts leaks who (control.execution.logs who)
            (control.execution.observe (application setup timeouts leaks) who))
          (LateKey.ofView setup timeouts leaks who
            ((control.execution.respond (application setup timeouts leaks) who response).logs who)
            ((control.execution.respond (application setup timeouts leaks) who response).observe
              (application setup timeouts leaks) who)) ∧
    (∀ {slots : Nat} (option : LateOption slots),
      (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who _
          option choice).toReal =
        contentFactor setup timeouts leaks assessment who control.execution
            (control.execution.respond (application setup timeouts leaks) who response) response *
          lateOptionFactor (timeouts := timeouts) bounds
            (LateKey.ofView setup timeouts leaks who (control.execution.logs who)
              (control.execution.observe (application setup timeouts leaks) who))
            (LateKey.ofView setup timeouts leaks who
              ((control.execution.respond (application setup timeouts leaks) who response).logs
                who)
              ((control.execution.respond (application setup timeouts leaks) who response).observe
                (application setup timeouts leaks) who)) option) ∧
    (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler who _)
        choice).toReal =
      contentFactor setup timeouts leaks assessment who control.execution
          (control.execution.respond (application setup timeouts leaks) who response) response *
        silenceFactor (timeouts := timeouts) (LateKey.ofView setup timeouts leaks who
          ((control.execution.respond (application setup timeouts leaks) who response).logs who)
          ((control.execution.respond (application setup timeouts leaks) who response).observe
            (application setup timeouts leaks) who)) ∧
    (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup timeouts leaks assessment who control.execution
          (control.execution.respond (application setup timeouts leaks) who response) response *
        slotTierFactor (timeouts := timeouts) bounds
          (LateKey.ofView setup timeouts leaks who (control.execution.logs who)
            (control.execution.observe (application setup timeouts leaks) who))
          (LateKey.ofView setup timeouts leaks who
            ((control.execution.respond (application setup timeouts leaks) who response).logs who)
            ((control.execution.respond (application setup timeouts leaks) who response).observe
              (application setup timeouts leaks) who)) := by
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have keyPending := LateKey.ofView_pending rawTrace who
  cases pending : pendingEvent setup timeouts leaks who (some (control.execution.logs who,
      control.execution.observe (application setup timeouts leaks) who)) with
  | none =>
      rw [pending] at keyPending
      have settled : ∀ event, control.execution.application.publicView.ownTurn? who =
          some event → (eventRecorded timeouts) leaks (control.execution.logs who) event =
            true := by
        intro event turn
        by_contra unrecorded
        have := pendingEvent_of_spec (timeouts := timeouts) (setup := setup) (leaks := leaks)
          (past := control.execution.logs who)
          (view := control.execution.observe (application setup timeouts leaks) who) turn
          (Bool.eq_false_iff.mpr unrecorded)
        rw [pending] at this
        cases this
      obtain ⟨silent, contentOne, honestOne, slotOne, silenceOne⟩ :=
        onePacket_settled_operational_masses (timeouts := timeouts) assessment trace who settled
          response member
          positive choice chosen
      subst silent
      have choiceEq := choice_eq_silenceChoice (timeouts := timeouts) who _ _ choice chosen
      subst choiceEq
      have lastNone : (LateKey.ofView setup timeouts leaks who
          ((control.execution.respond (application setup timeouts leaks) who ⟨none⟩).logs who)
          ((control.execution.respond (application setup timeouts leaks) who ⟨none⟩).observe
            (application setup timeouts leaks) who)).lastEmitted = none := by
        rw [LateKey.respond_lastEmitted]
        rfl
      have silenceOneFactor : silenceFactor (timeouts := timeouts) (LateKey.ofView setup timeouts
        leaks who
          ((control.execution.respond (application setup timeouts leaks) who ⟨none⟩).logs who)
          ((control.execution.respond (application setup timeouts leaks) who ⟨none⟩).observe
            (application setup timeouts leaks) who)) = 1 := by
        unfold silenceFactor
        rw [lastNone]
        simp
      rw [contentOne, honestFactor_of_settled (timeouts := timeouts) keyPending,
        slotTierFactor_of_settled (timeouts := timeouts) bounds keyPending, silenceOneFactor,
          honestOne, slotOne,
        silenceOne, ENNReal.toReal_one]
      refine ⟨by ring, fun option => ?_, by ring, by ring⟩
      rw [lateOptionFactor_of_settled (timeouts := timeouts) bounds keyPending, silenceOneFactor,
        onePacket_settled_lateChoice (timeouts := timeouts) assessment trace who pending option,
          ENNReal.toReal_one]
      ring
  | some event =>
      rw [pending] at keyPending
      obtain ⟨turn, _, owned, unsent⟩ := pendingEvent_spec (timeouts := timeouts) (setup := setup)
        pending
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
            onePacket_pendingBinding_operational_masses (timeouts := timeouts) assessment covers
              capacity trace owner
              event turn unsent node response member positive choice chosen
          rw [honestFactor_of_bind (timeouts := timeouts) keyPending node, slotTierFactor_of_bind
            (timeouts := timeouts) bounds keyPending node]
          exact ⟨honestMass, fun option => onePacket_pendingBinding_lateChoice (timeouts :=
            timeouts) assessment covers
            capacity trace owner event turn unsent node response member positive choice chosen
            option, silenceMass, slotMass⟩
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨honestMass, lateMass, silenceMass, slotMass⟩ :=
            onePacket_pendingReveal_masses (timeouts := timeouts) assessment covers trace who event
              turn unsent node
              canonical response member positive choice chosen
          rw [honestFactor_of_resolve (timeouts := timeouts) keyPending node,
            slotTierFactor_of_resolve (timeouts := timeouts) bounds keyPending node]
          refine ⟨honestMass, fun option => ?_, silenceMass, slotMass⟩
          cases option with
          | none =>
              rw [lateOptionFactor_none, lateChoice_none]
              exact silenceMass
          | some slot =>
              rw [lateOptionFactor_of_resolve (timeouts := timeouts) bounds keyPending node]
              exact lateMass slot

end Masses

end Vegas
