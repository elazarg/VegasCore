/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStepFactors

/-! # Masses of a response step

Along every history of the one-packet game, the key's pending event is the
player's pending event (`Vegas.LateKey.ofView_pending`), and the key is a late
delivery exactly when the information state is (`Vegas.LateKey.ofView_isLate`).

The late options give a realized response with positive content its content
factor times the late-option factor: without a pending event
(`Vegas.onePacket_settled_lateChoice`) and at a pending binding
(`Vegas.onePacket_pendingBinding_lateChoice`).
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

/-- Laws pushed along maps agreeing on the support agree. -/
private theorem map_congr_support {α β : Type} (law : PMF α) {f g : α → β}
    (agree : ∀ x ∈ law.support, f x = g x) : law.map f = law.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases supported : x ∈ law.support
  · rw [agree x supported]
  · simp [(PMF.apply_eq_zero_iff law x).mpr supported]

private theorem map_fun_const {α β : Type} (law : PMF α) (b : β) :
    law.map (fun _ => b) = PMF.pure b :=
  PMF.map_const law b

section Reads

variable {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
  {control : (application setup runtime leaks).Control}

/-- Along every history, the key's pending event is the player's pending
event. -/
theorem LateKey.ofView_pending
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) :
    (LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who)).pending =
      pendingEvent setup runtime leaks who (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)) := by
  classical
  unfold LateKey.pending pendingEvent
  change (control.execution.application.publicView.ownTurn? who).filter _ =
    (control.execution.application.publicView.ownTurn? who).filter _
  congr 1
  funext event
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not,
    LateKey.ofView_recorded (runtime := runtime) trace who event]
  cases runtime.eventRecorded leaks (control.execution.recall who) event <;> simp

/-- Along every history, the key is a late delivery exactly when the
information state is. -/
theorem LateKey.ofView_isLate
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) :
    (LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who)).IsLate (runtime :=
        runtime) ↔
      LateDelivery setup runtime leaks who (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)) := by
  unfold LateKey.IsLate LateDelivery
  rw [LateKey.ofView_pending trace who]
  constructor
  · rintro ⟨event, pending, entry, member, turn⟩
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨_, _, event, rfl, pending, original, originalMember, turn⟩
  · rintro ⟨past, view, event, same, pending, entry, member, turn⟩
    cases same
    exact ⟨event, pending, _, List.mem_map.mpr ⟨entry, member, rfl⟩, turn⟩

end Reads

section Late

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Late options without a pending event.** Along every history of the
one-packet game, without a pending event, every late option is silence. -/
theorem onePacket_settled_lateChoice (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (settled : pendingEvent setup runtime leaks who (some (control.execution.recall who,
      control.execution.observe (application setup runtime leaks) who)) = none)
    (option : LateOption slots) :
    lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup runtime leaks) who)) option
        (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.recall who,
            control.execution.observe (application setup runtime leaks) who))) = 1 := by
  cases option with
  | none =>
      rw [lateChoice_none]
      exact PMF.pure_apply_self _
  | some slot =>
      cases turn : control.execution.application.publicView.ownTurn? who with
      | none =>
          change (lateResponse setup runtime leaks assessment who _ _ (some slot)).map _ _ = 1
          unfold lateResponse
          rw [show (control.execution.observe (application setup runtime leaks)
            who).application.publicView.ownTurn? who = none from turn]
          dsimp only
          rw [PMF.pure_map]
          exact PMF.pure_apply_self _
      | some event =>
          have recorded : runtime.eventRecorded leaks (control.execution.recall who)
              event = true := by
            unfold pendingEvent at settled
            change (control.execution.application.publicView.ownTurn? who).filter _ = none
              at settled
            rw [turn, Option.filter_some] at settled
            by_contra unrecorded
            simp [unrecorded] at settled
          rw [lateChoice_some_eq_map (runtime := runtime) assessment who _ _ event turn slot,
            map_congr_support (g := fun _ => silenceChoice setup runtime leaks bounds (initialLaw
              setup)
              horizon scheduler who (some (control.execution.recall who,
                control.execution.observe (application setup runtime leaks) who))) _
              fun choice _ => onePacket_responseChoice_of_recorded (runtime := runtime) trace who
                event recorded _
                (slotResponse_names (runtime := runtime) who _ _ event slot.val choice),
            map_fun_const]
          exact PMF.pure_apply_self _

open Classical in
/-- **Late options at a pending binding.** Along every history of the one-packet
game, at a binding of the player's turn its recall has not submitted for, a late
option gives a realized response with positive content its content factor times
the late-option factor. -/
theorem onePacket_pendingBinding_lateChoice
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : runtime.eventRecorded leaks (control.execution.recall who) event = false)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
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
    (chosen : choice.1 = some response) {slots : Nat} (option : LateOption slots) :
    (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
      option
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        lateOptionFactor (runtime := runtime) bounds
          (LateKey.ofView setup runtime leaks who (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who))
          (LateKey.ofView setup runtime leaks who
            ((control.execution.respond (application setup runtime leaks) who response).recall who)
            ((control.execution.respond (application setup runtime leaks) who response).observe
              (application setup runtime leaks) who)) option := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have capacityOne : 1 ≤ bounds.candidateCount :=
    Nat.one_le_iff_ne_zero.mpr fun zero => by
      have := capacity who
      omega
  have pending : (LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who)).pending = some event := by
    rw [LateKey.ofView_pending rawTrace who]
    unfold pendingEvent
    change (control.execution.application.publicView.ownTurn? who).filter _ = _
    rw [turn, Option.filter_some, unsent]
    rfl
  have site := onePacket_coveredPendingBinding (runtime := runtime) assessment covers capacityOne
    trace who event turn
    node
  cases option with
  | none =>
      rw [lateChoice_none]
      exact (onePacket_pendingBinding_operational_masses (runtime := runtime) assessment covers
        capacity trace who
        event turn unsent node response member positive choice chosen).2.1
  | some slot =>
      unfold lateOptionFactor
      rw [pending]
      dsimp only
      rw [node]
      dsimp only
      rw [lateChoice_some_eq_map (runtime := runtime) assessment who _ _ event turn slot]
      cases sends : response.transmission with
      | none =>
          have silent : response = ⟨none⟩ := by
            rcases response with ⟨transmission⟩
            change transmission = none at sends
            rw [sends]
          subst silent
          have choiceEq := choice_eq_silenceChoice (runtime := runtime) who _ _ choice chosen
          subst choiceEq
          have contentOne : contentFactor setup runtime leaks assessment who control.execution
              (control.execution.respond (application setup runtime leaks) who ⟨none⟩) ⟨none⟩ = 1
                := rfl
          have lastNone : ((LateKey.ofView setup runtime leaks who
              ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).recall who)
              ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).observe
                (application setup runtime leaks) who)).lastEmitted.map fun
                  message =>
                  message.payload.call : Option (Payload (graph setup))) = none := by
            rw [LateKey.respond_lastEmitted]
            rfl
          rw [contentOne, one_mul, lastNone]
          dsimp only
          rw [LateKey.ofView_slotPermitted (runtime := runtime) rawTrace who event slot.val]
          by_cases open_ : slot.val < bounds.candidateCount ∧
              countPermits ((application setup runtime leaks).outputs (control.execution.recall
                who))
                (slotEnvelope setup runtime leaks who (control.execution.recall who)
                  (control.execution.observe (application setup runtime leaks) who) event
                    slot.val) = true
          · simp only [open_, and_self, ↓reduceIte]
            rw [map_apply_eq_zero_of_forall_ne, ENNReal.toReal_zero]
            intro other supported same
            have covered := onePacket_honest_covered (runtime := runtime) assessment covers trace
              who event turn other
              supported
            have offered := (slotResponse_mem_onePacket_iff setup runtime leaks bounds who _ _
              event node
              slot.val open_.1 other covered).mpr open_.2
            obtain ⟨action, encoded, _⟩ := covered
            obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup runtime leaks who
              (control.execution.recall who)
              (control.execution.observe (application setup runtime leaks) who) event node
                slot.val other
              action encoded
            have values := congrArg Subtype.val same
            simp only [slotChoiceOf, responseChoice, offered, silenceChoice,
              bounds.silence_onePacket runtime leaks who, ↓reduceDIte] at values
            have silent := congrArg ReactiveApplication.Action.transmission
              (Option.some.inj values)
            rw [transmits] at silent
            cases silent
          · simp only [open_, ↓reduceIte]
            rw [map_congr_support (g := fun _ => silenceChoice setup runtime leaks bounds
                (initialLaw setup) horizon scheduler who (some (control.execution.recall who,
                  control.execution.observe (application setup runtime leaks) who))) _
                fun other supported => by
                  apply responseChoice_of_not_offered (runtime := runtime)
                  intro offered
                  have covered := onePacket_honest_covered (runtime := runtime) assessment covers
                    trace who event turn
                    other supported
                  obtain ⟨action, encoded, _⟩ := covered
                  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup
                    runtime leaks
                    who (control.execution.recall who)
                    (control.execution.observe (application setup runtime leaks) who) event node
                      slot.val
                    other action encoded
                  have packetEq : material.call.packet =
                      .commitment event (who, .prepared slot.val) :=
                    congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
                      message.payload.call) envelope
                  have slotCapacity := offered_commitment_capacity (runtime := runtime) who _ _ _
                    ((bounds.mem_onePacketActions runtime leaks who _ _ _).mp offered).1
                    material transmits packetEq
                  exact open_ ⟨slotCapacity, (slotResponse_mem_onePacket_iff setup runtime leaks
                    bounds
                    who _ _ event node slot.val slotCapacity other
                    (onePacket_honest_covered (runtime := runtime) assessment covers trace who
                      event turn other
                      supported)).mp offered⟩,
              map_fun_const, PMF.pure_apply_self, ENNReal.toReal_one]
      | some material =>
          obtain ⟨serial, value, slotCapacity, responseEq, contentEq⟩ :=
            onePacket_commitment_realized (runtime := runtime) assessment trace who event turn
              node response member
              material sends positive
          have supported : sourceOfValue setup event outputEq value ∈ (asIfHonestProfile setup
            runtime
              leaks assessment who (some (control.execution.recall who,
                control.execution.observe (application setup runtime leaks) who))).support := by
            rw [contentEq] at positive
            exact (PMF.mem_support_iff _ _).mpr (ENNReal.toReal_pos_iff.mp positive).1.ne'
          have offered : slotResponse setup runtime leaks who (control.execution.recall who)
              (control.execution.observe (application setup runtime leaks) who) event serial
              (sourceOfValue setup event outputEq value) ∈ bounds.onePacketActions
                runtime leaks who (control.execution.recall who)
                (control.execution.observe (application setup runtime leaks) who) :=
            responseEq ▸ member
          have choiceEq : choice = slotChoiceOf setup runtime leaks bounds (initialLaw setup)
            horizon
              scheduler who (control.execution.recall who)
              (control.execution.observe (application setup runtime leaks) who) event serial
              (sourceOfValue setup event outputEq value) := by
            apply Subtype.ext
            rw [chosen, responseEq]
            simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
          obtain ⟨delivered, transmits, envelope⟩ := slotResponse_transmission setup runtime leaks
            who
            (control.execution.recall who) (control.execution.observe (application setup runtime
              leaks)
              who) event node serial (sourceOfValue setup event outputEq value) _
            (sourceOfValue_encoded setup event outputEq codeEq value)
          rw [← responseEq, sends] at transmits
          cases Option.some.inj transmits
          have packetEq : material.call.packet = .commitment event (who, .prepared serial) :=
            congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
              message.payload.call) envelope
          have lastCall : ((LateKey.ofView setup runtime leaks who
              ((control.execution.respond (application setup runtime leaks) who response).recall
                who)
              ((control.execution.respond (application setup runtime leaks) who response).observe
                (application setup runtime leaks) who)).lastEmitted.map fun
                  message =>
                  message.payload.call : Option (Payload (graph setup))) =
              some (.commitment event (who, .prepared serial)) := by
            rw [LateKey.respond_lastEmitted, sends]
            exact congrArg some packetEq
          rw [lastCall]
          dsimp only
          subst choiceEq
          rw [map_slotChoiceOf_apply (runtime := runtime) site slot.val supported slotCapacity
            offered, contentEq]
          split
          · rw [mul_one]
          · rw [ENNReal.toReal_zero, mul_zero]

end Late

end Vegas
