/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnclassifiedSelection
import Vegas.Game.SourceServiceUnclassifiedSlots
import Vegas.Pending.ReactiveBindingCopiedWindow

/-! # Actual copied responses at a completed repair boundary

The full effective original policy need not follow the risk menu. Outside the
two charged response classes, an actually retained copy preserves the whole
frame and completed memory. Actual counted-registration resources apply even
after opportunity risk latches; this expansion does not assert a charge.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A real copied uncharged response preserves completed memory and the full
private frame, including at an uncharged expanded input. The real RAW trace,
uncharged constructor shape and counted slots derive freshness and packet
equality; no global private certificate capability equality is postulated. -/
theorem sourceServiceUnclassified_copied_response_frame
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, repaired⟩))
    (rightAtTurn : OwnSubmissionsAtTurn setup leaks repaired who)
    (rightSlots : CanonicalSlotsUsed setup leaks repaired who)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (original.recall who)
      (original.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (original.recall who) response)
    (retained : response ∈ bounds.riskActions (runtime setup) leaks bound who
      (repaired.recall who) (repaired.observe (application setup leaks) who)) :
    let app := application setup leaks
    let input := (repaired.recall who, repaired.observe app who)
    let selected := BindingMemory.retainedResponse (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who memory input response
    let remembered : BindingMemory (runtime setup) leaks :=
      ⟨selected.2, memory.responses ++
        [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩
    selected.1 = response ∧
      remembered.Frame (runtime setup) leaks who (original.respond app who response)
        (repaired.respond app who selected.1) ∧
      remembered.shadow.OwnBindings who ∧
      remembered.shadow.CompletedAt (original.respond app who response).application.config ∧
      OwnSubmissionsAtTurn setup leaks (repaired.respond app who selected.1) who ∧
      CanonicalSlotsUsed setup leaks (repaired.respond app who selected.1) who := by
  classical
  let app := application setup leaks
  let view := repaired.observe app who
  let changed := memory.copyResponse (runtime setup) leaks who view response
  let updated : BindingMemory (runtime setup) leaks :=
    ⟨changed.2, memory.responses ++
      [(memory.shadow.inputView (runtime setup) leaks view, response)]⟩
  have physical := sourceServiceUnclassified_response_transport bounds original repaired
    who memory frame leftTrace rightTrace response effective notPacket notRecorded
  have rightNotPacket : ¬ auditableServiceResponse setup leaks who (repaired.recall who)
      (repaired.observe app who) response := by
    rintro ⟨material, transmission, classified⟩
    apply notPacket
    refine ⟨material, transmission, ?_⟩
    rw [localServiceEnvelope_actual setup leaks leftTrace who material]
    rw [localServiceEnvelope_actual setup leaks rightTrace who material] at classified
    change AuditableServicePacket setup repaired.application.publicView who _ at classified
    change AuditableServicePacket setup original.application.publicView who _
    rwa [← frame.publicView,
      ← show original.network.nextSerial who = repaired.network.nextSerial who from
        congrArg (fun network => network.nextSerial who) frame.network,
      ← physical.2.2 material transmission] at classified
  have rightNotRecorded : ¬ recordedServiceResponse setup leaks (repaired.recall who)
      response := by
    rintro ⟨event, recorded, named⟩
    apply notRecorded
    exact ⟨event, ((runtime setup).eventRecorded_congr leaks _ _ frame.submissions event).symm
      ▸ recorded, named⟩
  have shape :
      (∀ material, response.transmission = some material →
        ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
      FreshOwnedBindingResponse (runtime setup) leaks who
        (original.observe app who).application response := by
    rcases unclassifiedResponse_registration bounds repaired who rightTrace rightAtTurn
        rightSlots response physical.1 rightNotPacket rightNotRecorded with noncommitment |
      ⟨event, payload, _layout, _turn, fresh, opening, actual⟩
    · exact Or.inl noncommitment
    · exact Or.inr ⟨event, repaired.application.publicView.bindingCount who, opening,
        (frame.slots (.prepared _)).mpr fresh, actual⟩
  have selectedEq : BindingMemory.retainedResponse (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who memory
        (repaired.recall who, view) response = changed := by
    have member : response ∈ bounds.riskActions (runtime setup) leaks bound who
        (repaired.recall who) view := retained
    simp only [BindingMemory.retainedResponse, MessageBounds.riskMenu, member, ↓reduceIte]
    rfl
  dsimp only
  rw [selectedEq]
  have same : changed.1 = response := memory.copyResponse_action (runtime setup) leaks who view
    response
  have actualSlots := sourceServiceUnclassified_response_slots bounds repaired who
    rightTrace rightAtTurn rightSlots response physical.1 rightNotPacket rightNotRecorded
  have resources : updated.Frame (runtime setup) leaks who (original.respond app who response)
      (repaired.respond app who changed.1) ∧ updated.shadow.OwnBindings who ∧
      updated.shadow.CompletedAt (original.respond app who response).application.config := by
    rcases shape with
      noncommitment | fresh
    · have changedEq := memory.copyResponse_noncommitment (runtime setup) leaks who view response
        noncommitment
      have shadow : updated.shadow = memory.shadow := congrArg Prod.snd changedEq
      have inert (execution : app.Execution) :
          (execution.respond app who response).application = execution.application := by
        rcases response with ⟨transmission⟩
        cases transmission with
        | none => rfl
        | some material =>
            exact reactiveApplication_submit_noncommitment (runtime setup) leaks
              execution.application who material (noncommitment material rfl)
      refine ⟨?_, ?_, ?_⟩
      · rw [same]
        rcases response with ⟨transmission⟩
        cases transmission with
        | none =>
            simpa only [updated, changed, changedEq, BindingMemory.record] using
              frame.transport_response (⟨none⟩ : app.Action) (by simp)
        | some material =>
            have leftInert := reactiveApplication_submit_noncommitment (runtime setup) leaks
              original.application who material (noncommitment material rfl)
            have rightInert := reactiveApplication_submit_noncommitment (runtime setup) leaks
              repaired.application who material (noncommitment material rfl)
            have packet := physical.2.2 material rfl
            rw [leftInert, rightInert] at packet
            simpa only [updated, changed, changedEq, BindingMemory.record] using
              frame.inert_submission material material leftInert rightInert packet
      · rw [shadow]
        exact onlyBindings
      · rw [shadow, inert original]
        exact past
    · obtain ⟨event, serial, opening, fresh, actual⟩ := fresh
      rw [actual]
      have rightFresh := (frame.slots (.prepared serial)).mp fresh
      have ownFresh : (memory.shadow.inputView (runtime setup) leaks view).application.candidates
          (.prepared serial) = .fresh := by
        rw [frame.observed]
        exact fresh
      have changedEq := memory.copyResponse_fresh (runtime setup) leaks who view event
        (.prepared serial) opening .none ownFresh rightFresh
      have resources := frame.copied_binding_submission onlyBindings past event serial opening
      refine ⟨?_, ?_, ?_⟩
      · simpa only [updated, changed, actual, changedEq] using resources.1
      · simpa only [updated, changed, actual, changedEq] using resources.2.1
      · simpa only [updated, changed, actual, changedEq] using resources.2.2
  refine ⟨same, resources.1, resources.2.1, resources.2.2, ?_⟩
  simpa only [same] using actualSlots

end Vegas
