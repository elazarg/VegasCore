/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketStepMasses

/-! # Masses of a response at a pending reveal

At a pending reveal, the canonical disclosure is canonical in the one-packet
menu when it transmits and is the only transmission naming the reveal the menu
offers (`Vegas.DisclosureCanonical`). Then, along every history of the
one-packet game, a realized response with positive content is silence or the
disclosure, with content one, and the as-if-honest law, the late options,
silence and the slot tier give it its content factor times their factors
(`Vegas.onePacket_pendingReveal_masses`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Laws pushed along maps agreeing on the support agree. -/
private theorem map_congr_support {α β : Type} (law : PMF α) {f g : α → β}
    (agree : ∀ x ∈ law.support, f x = g x) : law.map f = law.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases supported : x ∈ law.support
  · rw [agree x supported]
  · simp [(PMF.apply_eq_zero_iff law x).mpr supported]

private theorem eq_pure_of_support_subset {α : Type} (law : PMF α) (a : α)
    (only : ∀ x ∈ law.support, x = a) : law = PMF.pure a := by
  have support : law.support = {a} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, only⟩
    obtain ⟨x, member⟩ := law.support_nonempty
    exact only x member ▸ member
  ext x
  by_cases same : x = a
  · subst same
    rw [(PMF.apply_eq_one_iff _ _).mpr support, PMF.pure_apply_self]
  · rw [PMF.pure_apply_of_ne _ _ same, (PMF.apply_eq_zero_iff _ _).mpr (by
      rw [support]
      exact same)]

variable [Fintype Player] (bounds : MessageBounds (graph setup))

variable (setup leaks) in
/-- **The canonical disclosure.** At a pending reveal of a player, its
canonical disclosure transmits, and every transmission naming the reveal that
the one-packet menu offers is that disclosure. -/
def DisclosureCanonical (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Prop :=
  ∀ event, pendingEvent setup leaks who (some (past, view)) = some event →
    ∀ owner payload (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
      checks outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
      ((runtime setup).canonicalServiceDecision leaks who past view event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission ≠
        none ∧
      ∀ response ∈ bounds.onePacketActions (runtime setup) leaks who past view,
        ∀ material, response.transmission = some material →
          material.call.packet.event? (graph setup) = some event →
          response = (runtime setup).canonicalServiceDecision leaks who past view event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)

variable {bounds} {horizon : Nat} {scheduler : (application setup leaks).Scheduler}

/-- **Masses at a pending reveal.** Along every history of the one-packet game,
at a reveal of the player's turn its recall has not submitted for, where the
canonical disclosure is canonical, the as-if-honest law, the late options,
silence and the slot tier give a realized response with positive content its
content factor times their factors. -/
theorem onePacket_pendingReveal_masses (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    {owner : Player} {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout
      (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
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
        transmitFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who response).recall who)
          ((control.execution.respond (application setup leaks) who response).observe
            (application setup leaks) who)) ∧
    (∀ {slots : Nat} (slot : Fin slots),
      (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who _
          (some slot) choice).toReal =
        contentFactor setup leaks assessment who control.execution
            (control.execution.respond (application setup leaks) who response) response *
          transmitFactor (LateKey.ofView setup leaks who
            ((control.execution.respond (application setup leaks) who response).recall who)
            ((control.execution.respond (application setup leaks) who response).observe
              (application setup leaks) who))) ∧
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
        transmitFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who response).recall who)
          ((control.execution.respond (application setup leaks) who response).observe
            (application setup leaks) who)) := by
  classical
  have pendingEq : pendingEvent setup leaks who (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who)) = some event := by
    unfold pendingEvent
    change (control.execution.application.publicView.ownTurn? who).filter _ = _
    rw [turn, Option.filter_some, unsent]
    rfl
  obtain ⟨transmitsDisclosure, unique⟩ := canonical event pendingEq owner payload binding checks
    outputEq codeEq node
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp transmitsDisclosure
  have offered := onePacket_disclosure_offered covers trace who event turn unsent node disclosed
    sendsDisclosure
  have honestEq := onePacket_honestChoice_reveal (bounds := bounds) assessment trace who event
    turn outputEq
  have slotEq := onePacket_slotChoice_reveal assessment trace who event turn node
  have lateEq : ∀ {slots : Nat} (slot : Fin slots),
      lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
          (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who)) (some slot) =
        PMF.pure (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who))
          ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
            (control.execution.observe (application setup leaks) who) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) := by
    intro slots slot
    rw [lateChoice_some_eq_map assessment who _ _ event turn slot]
    rw [map_congr_support (g := fun _ => responseChoice setup leaks bounds (initialLaw setup)
        horizon scheduler who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) _
      fun other supported => by
        change responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who _
          (slotResponse setup leaks who _ _ event slot.val other) = _
        unfold slotResponse
        rw [onePacket_honest_discloses assessment trace who event turn outputEq other supported]
        simp only [node]]
    exact PMF.map_const _ _
  have disclosureValue : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler
      who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))
      ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1 =
      some ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) := by
    simp only [responseChoice, offered, ↓reduceDIte]
  have notSilence : responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))
      ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) ≠
      silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) := by
    intro same
    have values := congrArg Subtype.val same
    rw [disclosureValue] at values
    simp only [silenceChoice, responseChoice, bounds.silence_onePacket (runtime setup) leaks who,
      ↓reduceDIte] at values
    have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
    rw [sendsDisclosure] at silent
    cases silent
  rw [honestEq, slotEq]
  cases sends : response.transmission with
  | none =>
      have silent : response = ⟨none⟩ := by
        rcases response with ⟨transmission⟩
        change transmission = none at sends
        rw [sends]
      subst silent
      have choiceEq := choice_eq_silenceChoice who _ _ choice chosen
      subst choiceEq
      have contentOne : contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who ⟨none⟩) ⟨none⟩ = 1 := rfl
      have lastNone : (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup leaks) who ⟨none⟩).observe
            (application setup leaks) who)).lastEmitted = none := by
        rw [LateKey.respond_lastEmitted]
        rfl
      have silenceOne : silenceFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup leaks) who ⟨none⟩).observe
            (application setup leaks) who)) = 1 := by
        unfold silenceFactor
        rw [lastNone]
        simp
      have transmitZero : transmitFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup leaks) who ⟨none⟩).observe
            (application setup leaks) who)) = 0 := by
        unfold transmitFactor
        rw [silenceOne]
        ring
      rw [contentOne, silenceOne, transmitZero]
      refine ⟨?_, fun slot => ?_, ?_, ?_⟩
      · rw [PMF.pure_apply_of_ne _ _ notSilence.symm, ENNReal.toReal_zero, mul_zero]
      · rw [lateEq slot, PMF.pure_apply_of_ne _ _ notSilence.symm, ENNReal.toReal_zero, mul_zero]
      · rw [PMF.pure_apply_self, ENNReal.toReal_one, mul_one]
      · rw [PMF.pure_apply_of_ne _ _ notSilence.symm, ENNReal.toReal_zero, mul_zero]
  | some material =>
      obtain ⟨named, turnNamed, _, packetEvent⟩ :=
        onePacket_content_pos assessment trace who response member material sends _ positive
      rw [turn] at turnNamed
      cases Option.some.inj turnNamed
      have responseEq := unique response member material sends packetEvent
      have choiceEq : choice = responseChoice setup leaks bounds (initialLaw setup) horizon
          scheduler who (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who))
          ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
            (control.execution.observe (application setup leaks) who) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) := by
        apply Subtype.ext
        rw [chosen, disclosureValue, responseEq]
      -- Content one: as-if-honest play is the disclosure alone.
      have contentOne : contentFactor setup leaks assessment who control.execution
          (control.execution.respond (application setup leaks) who response) response = 1 := by
        have weighted : sentSourceAction setup leaks
            (control.execution.respond (application setup leaks) who response) response ∈
            (asIfHonestProfile setup leaks assessment who (some (control.execution.recall who,
              control.execution.observe (application setup leaks) who))).support := by
          unfold contentFactor at positive
          rw [sends] at positive
          exact (PMF.mem_support_iff _ _).mpr (ENNReal.toReal_pos_iff.mp positive).1.ne'
        have pure := eq_pure_of_support_subset _ _ fun other supported =>
          encode_injective setup event
            (onePacket_honest_discloses assessment trace who event turn outputEq other supported)
            (onePacket_honest_discloses assessment trace who event turn outputEq _ weighted)
        unfold contentFactor
        rw [sends]
        change ((asIfHonestProfile setup leaks assessment who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))) _).toReal = 1
        rw [pure, PMF.pure_apply_self, ENNReal.toReal_one]
      have lastSome : (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who response).recall who)
          ((control.execution.respond (application setup leaks) who response).observe
            (application setup leaks) who)).lastEmitted ≠ none := by
        rw [LateKey.respond_lastEmitted, sends]
        exact Option.some_ne_none _
      have silenceZero : silenceFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who response).recall who)
          ((control.execution.respond (application setup leaks) who response).observe
            (application setup leaks) who)) = 0 := by
        unfold silenceFactor
        simp [lastSome]
      have transmitOne : transmitFactor (LateKey.ofView setup leaks who
          ((control.execution.respond (application setup leaks) who response).recall who)
          ((control.execution.respond (application setup leaks) who response).observe
            (application setup leaks) who)) = 1 := by
        unfold transmitFactor
        rw [silenceZero]
        ring
      rw [contentOne, silenceZero, transmitOne]
      subst choiceEq
      refine ⟨?_, fun slot => ?_, ?_, ?_⟩
      · rw [PMF.pure_apply_self, ENNReal.toReal_one, mul_one]
      · rw [lateEq slot, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]
      · rw [PMF.pure_apply_of_ne _ _ notSilence, ENNReal.toReal_zero, mul_zero]
      · rw [PMF.pure_apply_self, ENNReal.toReal_one, mul_one]

end Vegas
