/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnclassifiedSelection
import Vegas.Pending.ReactiveBindingCopiedWindow

/-! # Actual copied responses at a completed repair boundary

The full effective original policy need not follow the risk menu. Outside the
two charged response classes, an actually retained copy preserves the whole
frame and completed memory. Only current focal slot resources are used, so
foreign responses need not belong to the risk menu.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem canonical_copy_shape
    (bounds : MessageBounds (graph setup))
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.canonicalActions (runtime setup) leaks who
      (repaired.recall who) (repaired.observe (application setup leaks) who)) :
    (∀ material, response.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
      FreshOwnedBindingResponse (runtime setup) leaks who
        (original.observe (application setup leaks) who).application response := by
  classical
  let app := application setup leaks
  rcases bounds.canonicalActions_cases (runtime setup) leaks who _ _ response member with silent |
    ⟨event, choice, _turn, owned, _ready, _timely, represented, _first, same⟩
  · rw [silent]
    exact Or.inl (by intros material impossible; cases impossible)
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      simp only [MessageBounds.canonicalChoices, node, Finset.notMem_empty] at represented
  | bind actor payload outputEq codeEq =>
      have actorEq := nodeView_bind_actor outputEq codeEq
      rw [owned] at actorEq
      cases Option.some.inj actorEq
      simp only [MessageBounds.canonicalChoices, node] at represented
      obtain ⟨value, _included, rfl⟩ := Finset.mem_image.mp represented
      cases selected : canonicalFreshSlot who (repaired.observe app who).application with
      | none =>
          dsimp only [app] at selected
          have silent : response = ⟨none⟩ := by
            simpa only [canonicalServiceDecision, canonicalReactiveDecision, node, selected,
              Option.map_none, ReactiveApplication.SubmissionNormalization.action,
              reactiveNormalization] using same
          rw [silent]
          exact Or.inl (by intros material impossible; cases impossible)
      | some serial =>
          have actual := same.trans ((runtime setup).canonicalServiceDecision_binding leaks who
            _ _ event payload outputEq codeEq node serial selected (.success value))
          have rightFresh := canonicalFreshSlot_spec who _ serial selected
          exact Or.inr ⟨event, serial, some ⟨payload, value⟩,
            (frame.slots (.prepared serial)).mpr rightFresh, actual⟩
  | resolve actor payload binding checks outputEq codeEq =>
      have decision := (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks who
        (repaired.recall who) (repaired.observe app who) event choice (by
          intros actor payload outputEq codeEq impossible
          rw [node] at impossible
          cases impossible)
      have casesResolution := (runtime setup).serviceDecision_resolution_cases leaks who
        (repaired.recall who) (repaired.observe app who) event actor payload binding checks
          outputEq codeEq node (cast (congrArg EventField.Action outputEq) choice)
      simp only [cast_cast, cast_eq] at casesResolution
      have shape := same.trans decision
      left
      intro material emitted addressed candidate called
      rcases casesResolution with withheld | ⟨handle, value, evidence, _, _, _, opening⟩
      · rw [shape.trans withheld] at emitted
        cases Option.some.inj emitted
        cases called
      · rw [shape.trans opening] at emitted
        cases Option.some.inj emitted
        cases called

/-- A real copied uncharged response preserves completed memory and the full
private frame. Packet equality is derived for the selected response, rather
than postulated for every private certificate capability. -/
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
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
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
      remembered.shadow.CompletedAt (original.respond app who response).application.config := by
  classical
  let app := application setup leaks
  let view := repaired.observe app who
  let changed := memory.copyResponse (runtime setup) leaks who view response
  let updated : BindingMemory (runtime setup) leaks :=
    ⟨changed.2, memory.responses ++
      [(memory.shadow.inputView (runtime setup) leaks view, response)]⟩
  have physical := sourceServiceUnclassified_response_transport bounds bound original repaired
    who memory frame leftTrace rightTrace clear response effective notPacket notRecorded
  have canonical := retained
  rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear] at canonical
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
  refine ⟨same, ?_⟩
  rcases canonical_copy_shape bounds original repaired who memory frame response canonical with
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
    · change updated.Frame (runtime setup) leaks who (original.respond app who response)
        (repaired.respond app who changed.1)
      rw [same]
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
    · change updated.shadow.OwnBindings who
      rw [shadow]
      exact onlyBindings
    · change updated.shadow.CompletedAt (original.respond app who response).application.config
      rw [shadow, inert original]
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

end Vegas
