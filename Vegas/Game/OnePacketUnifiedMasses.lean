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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Unfold

variable {before after : LateKey setup runtime leaks}

theorem honestFactor_of_settled (settled : before.pending = none) :
    honestFactor (runtime := runtime) before after = 1 := by
  unfold honestFactor
  rw [settled]

theorem honestFactor_of_bind {event : (graph setup).EventId} (pending : before.pending = some event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    honestFactor (runtime := runtime) before after = pendingBindingHonestFactor (runtime :=
      runtime) before after := by
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
    honestFactor (runtime := runtime) before after = transmitFactor (runtime := runtime) after := by
  unfold honestFactor
  rw [pending]
  dsimp only
  rw [node]

variable (bounds : MessageBounds (graph setup))

theorem slotTierFactor_of_settled (settled : before.pending = none) :
    slotTierFactor (runtime := runtime) bounds before after = 1 := by
  unfold slotTierFactor
  rw [settled]

theorem slotTierFactor_of_bind {event : (graph setup).EventId}
    (pending : before.pending = some event) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    slotTierFactor (runtime := runtime) bounds before after = pendingBindingSlotFactor (runtime :=
      runtime) bounds before after event := by
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
    slotTierFactor (runtime := runtime) bounds before after = transmitFactor (runtime := runtime)
      after := by
  unfold slotTierFactor
  rw [pending]
  dsimp only
  rw [node]

theorem lateOptionFactor_none {slots : Nat} :
    lateOptionFactor (runtime := runtime) (slots := slots) bounds before after none =
      silenceFactor (runtime := runtime) after := rfl

theorem lateOptionFactor_of_settled {slots : Nat} (settled : before.pending =
  none)
    (option : LateOption slots) :
    lateOptionFactor (runtime := runtime) bounds before after option = silenceFactor (runtime :=
      runtime) after := by
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
    lateOptionFactor (runtime := runtime) bounds before after (some slot) = transmitFactor
      (runtime := runtime) after := by
  unfold lateOptionFactor
  rw [pending]
  dsimp only
  rw [node]

end Unfold

section Masses

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Masses of a response step.** Along every history of the one-packet game,
when every binding and publication value is a bounded value, the capacity
exceeds every player's number of binding events and the responder's disclosure
is canonical, the as-if-honest law, every late option, silence and the slot
tier give a realized response with positive content its content factor times
the factors read from the responder's keys before and after the response. -/
theorem onePacket_step_masses (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (canonical : DisclosureCanonical setup runtime leaks bounds who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who))
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    (positive : 0 < contentFactor setup runtime leaks assessment who control.execution
      (control.execution.respond (application setup runtime leaks) who response) response)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)))
    (chosen : choice.1 = some response) :
    (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        honestFactor (runtime := runtime)
          (LateKey.ofView setup runtime leaks who (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who))
          (LateKey.ofView setup runtime leaks who
            ((control.execution.respond (application setup runtime leaks) who response).recall who)
            ((control.execution.respond (application setup runtime leaks) who response).observe
              (application setup runtime leaks) who)) ∧
    (∀ {slots : Nat} (option : LateOption slots),
      (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
          option choice).toReal =
        contentFactor setup runtime leaks assessment who control.execution
            (control.execution.respond (application setup runtime leaks) who response) response *
          lateOptionFactor (runtime := runtime) bounds
            (LateKey.ofView setup runtime leaks who (control.execution.recall who)
              (control.execution.observe (application setup runtime leaks) who))
            (LateKey.ofView setup runtime leaks who
              ((control.execution.respond (application setup runtime leaks) who response).recall
                who)
              ((control.execution.respond (application setup runtime leaks) who response).observe
                (application setup runtime leaks) who)) option) ∧
    (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who _)
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        silenceFactor (runtime := runtime) (LateKey.ofView setup runtime leaks who
          ((control.execution.respond (application setup runtime leaks) who response).recall who)
          ((control.execution.respond (application setup runtime leaks) who response).observe
            (application setup runtime leaks) who)) ∧
    (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        slotTierFactor (runtime := runtime) bounds
          (LateKey.ofView setup runtime leaks who (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who))
          (LateKey.ofView setup runtime leaks who
            ((control.execution.respond (application setup runtime leaks) who response).recall who)
            ((control.execution.respond (application setup runtime leaks) who response).observe
              (application setup runtime leaks) who)) := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have keyPending := LateKey.ofView_pending rawTrace who
  cases pending : pendingEvent setup runtime leaks who (some (control.execution.recall who,
      control.execution.observe (application setup runtime leaks) who)) with
  | none =>
      rw [pending] at keyPending
      have settled : ∀ event, control.execution.application.publicView.ownTurn? who =
          some event → runtime.eventRecorded leaks (control.execution.recall who) event =
            true := by
        intro event turn
        by_contra unrecorded
        have := pendingEvent_of_spec (runtime := runtime) (setup := setup) (leaks := leaks)
          (past := control.execution.recall who)
          (view := control.execution.observe (application setup runtime leaks) who) turn
          (Bool.eq_false_iff.mpr unrecorded)
        rw [pending] at this
        cases this
      obtain ⟨silent, contentOne, honestOne, slotOne, silenceOne⟩ :=
        onePacket_settled_operational_masses (runtime := runtime) assessment trace who settled
          response member
          positive choice chosen
      subst silent
      have choiceEq := choice_eq_silenceChoice (runtime := runtime) who _ _ choice chosen
      subst choiceEq
      have lastNone : (LateKey.ofView setup runtime leaks who
          ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).observe
            (application setup runtime leaks) who)).lastEmitted = none := by
        rw [LateKey.respond_lastEmitted]
        rfl
      have silenceOneFactor : silenceFactor (runtime := runtime) (LateKey.ofView setup runtime
        leaks who
          ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).observe
            (application setup runtime leaks) who)) = 1 := by
        unfold silenceFactor
        rw [lastNone]
        simp
      rw [contentOne, honestFactor_of_settled (runtime := runtime) keyPending,
        slotTierFactor_of_settled (runtime := runtime) bounds keyPending, silenceOneFactor,
          honestOne, slotOne,
        silenceOne, ENNReal.toReal_one]
      refine ⟨by ring, fun option => ?_, by ring, by ring⟩
      rw [lateOptionFactor_of_settled (runtime := runtime) bounds keyPending, silenceOneFactor,
        onePacket_settled_lateChoice (runtime := runtime) assessment trace who pending option,
          ENNReal.toReal_one]
      ring
  | some event =>
      rw [pending] at keyPending
      obtain ⟨turn, _, owned, unsent⟩ := pendingEvent_spec (runtime := runtime) (setup := setup)
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
            onePacket_pendingBinding_operational_masses (runtime := runtime) assessment covers
              capacity trace owner
              event turn unsent node response member positive choice chosen
          rw [honestFactor_of_bind (runtime := runtime) keyPending node, slotTierFactor_of_bind
            (runtime := runtime) bounds keyPending node]
          exact ⟨honestMass, fun option => onePacket_pendingBinding_lateChoice (runtime :=
            runtime) assessment covers
            capacity trace owner event turn unsent node response member positive choice chosen
            option, silenceMass, slotMass⟩
      | resolve owner payload binding checks outputEq codeEq =>
          obtain ⟨honestMass, lateMass, silenceMass, slotMass⟩ :=
            onePacket_pendingReveal_masses (runtime := runtime) assessment covers trace who event
              turn unsent node
              canonical response member positive choice chosen
          rw [honestFactor_of_resolve (runtime := runtime) keyPending node,
            slotTierFactor_of_resolve (runtime := runtime) bounds keyPending node]
          refine ⟨honestMass, fun option => ?_, silenceMass, slotMass⟩
          cases option with
          | none =>
              rw [lateOptionFactor_none, lateChoice_none]
              exact silenceMass
          | some slot =>
              rw [lateOptionFactor_of_resolve (runtime := runtime) bounds keyPending node]
              exact lateMass slot

end Masses

end Vegas
