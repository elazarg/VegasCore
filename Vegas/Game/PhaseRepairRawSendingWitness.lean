/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairSendingWitness
import Vegas.Game.PhaseRawBindingContribution

/-! # A repaired actual binding retains its marked raw sending identity -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- The actual raw source binding and the explicit response image have the
same event and slot. Marking selects its raw-mixture contribution without
discarding any source-origin accepted failure or omission atom. -/
theorem phase_repair_raw_binding_pair
    (covered : bounds.CoversOutputValues) (who : Player) (remaining : Nat)
    (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
      (graph := serviceGraph setup mode)))
    (frame : PhaseBindingRepair.Frame runtime leaks memory who original repaired)
    (left : (E).Trace (some ⟨remaining, some who, original⟩))
    (right : (E).Trace (some ⟨remaining, some who, repaired⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode))
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload outputEq codeEq)
    (request : original.application.SeedRequest who ⟨original.application.attempt, event⟩)
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (original.recall who) (original.observe app who)) :
    phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      (some (original.recall who, original.observe app who),
        ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩)
      (some (repaired.recall who, repaired.observe app who),
        PhaseBindingRepair.Frame.responseImage (runtime := runtime) (leaks := leaks) who who
          ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩) := by
  have ordinary := phase_binding_sending_pair setup mode runtime leaks bounds plan horizon
    scheduler covered who remaining original repaired memory frame left right event payload
      outputEq serial preparation evidence codeEq node request member
  obtain ⟨value, responseEq⟩ := PhaseBindingRepair.Frame.responseImage_binding
    (runtime := runtime) (leaks := leaks) event payload outputEq codeEq node serial
      preparation evidence
  obtain ⟨first, second, firstTrace, secondTrace, actualEvent, actualPayload, binding,
    actualSerial, actualPreparation, actualEvidence, result, originalAction, firstActor,
      secondActor, imageRequest, unsent, values, imageClear, firstMember, secondMember,
        firstRecord, secondRecord⟩ := ordinary
  have actualView : original.observe app who = first.execution.observe app who :=
    congrArg Prod.snd (Option.some.inj (congrArg Prod.fst firstRecord))
  have firstClear : first.execution.application.current.excluded = ∅ := by
    have visible := congrArg (fun view : (app).PlayerView => view.application.2.excluded) actualView
    exact visible.symm.trans frame.clearOriginal
  have originalEq : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) = originalAction := congrArg Prod.snd firstRecord
  rw [← originalEq] at firstMember
  have packetEq := congrArg (fun response : (app).Action =>
    response.transmission.map (fun material => material.call.packet))
      (congrArg Prod.snd secondRecord)
  simp only [responseEq, phaseBindingResponse, Option.map_some] at packetEq
  obtain ⟨eventEq, slotEq⟩ := Payload.commitment.inj (Option.some.inj packetEq)
  have serialEq : serial = actualSerial := Slot.prepared.inj (congrArg Prod.snd slotEq)
  subst actualEvent
  subst actualSerial
  exact ⟨first, second, firstTrace, secondTrace, event, actualPayload, binding, serial,
    preparation, evidence, actualPreparation, actualEvidence, result, firstActor, secondActor,
    imageRequest, unsent, values, firstClear, imageClear, firstMember, secondMember,
    firstRecord.trans (by rw [← originalEq]), secondRecord⟩

/-- Genuine nonsilent legality supplies the selected binding request and type
needed for the marked witness; the source caller supplies only its raw syntax. -/
theorem phase_repair_raw_response_pair
    (covered : bounds.CoversOutputValues) (who : Player) (remaining : Nat)
    (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
      (graph := serviceGraph setup mode)))
    (frame : PhaseBindingRepair.Frame runtime leaks memory who original repaired)
    (left : (E).Trace (some ⟨remaining, some who, original⟩))
    (right : (E).Trace (some ⟨remaining, some who, repaired⟩))
    (event : (serviceGraph setup mode).EventId) (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode))
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (original.recall who) (original.observe app who)) :
    phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      (some (original.recall who, original.observe app who),
        ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩)
      (some (repaired.recall who, repaired.observe app who),
        PhaseBindingRepair.Frame.responseImage (runtime := runtime) (leaks := leaks) who who
          ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩) := by
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have typed : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact left
  let material : (app).Submission :=
    ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler remaining who original typed frame.clearOriginal material member
  have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who original
      typed coordinate request material member
  have eventEq : coordinate.event = event := Option.some.inj named.symm
  have requestEvent := request
  change original.application.SeedRequest who
    ⟨coordinate.attempt, coordinate.event⟩ at requestEvent
  rw [request.1, eventEq] at requestEvent
  have permitted : PhaseCount.permits ((app).outputs (original.recall who))
      (PhaseCount.localEnvelope runtime leaks who (original.recall who)
        (original.observe app who) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mp member).2
      with impossible | ⟨supplied, same, allowed⟩
    · cases impossible
    · cases Option.some.inj same
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks who
      (original.recall who) (original.observe app who) material)).payload.call =
        material.call.packet := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [actualCall] at correct
  change bindingOwnedBy (serviceGraph setup mode) who event = true ∧ _ at correct
  have owned := correct.1
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | bind actor payload outputEq codeEq =>
      have same : actor = who := by
        simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using owned
      subst actor
      exact phase_repair_raw_binding_pair setup mode runtime leaks bounds plan horizon scheduler
        covered who remaining original repaired memory frame left right event payload outputEq
          serial preparation evidence codeEq node requestEvent member

end Vegas
