/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnclassifiedTransport
import Vegas.Game.SourceServiceUnusableResponseFrame

/-! # Actual uncharged copy or typed-default selection

The single retained implementation copies an uncharged effective response when
it belongs to the repaired risk menu. Otherwise the concrete private residual
is replaced by its admitted typed default. No fallback or global preservation
of private raw capabilities is required on this branch.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

open Classical in
/-- The actual uncharged implementation branch is copy or admitted typed default.
The original response follows the full effective menu; it need not follow the
risk menu before or after this input. Charged and recorded responses are outside
this conditional branch, rather than being silently copied. -/
theorem sourceServiceUnclassified_response_selection
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨rightRemaining, some who, repaired⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (original.recall who)
      (original.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (original.recall who) response) :
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let input := (repaired.recall who, repaired.observe (application setup leaks) who)
    let selected := BindingMemory.retainedResponse (runtime setup) leaks menu who memory
      input response
    (response ∈ menu.actions who input.1 input.2 ∧
      selected = memory.copyResponse (runtime setup) leaks who input.2 response ∧
      selected.1 = response) ∨
    (unusableServiceBindingResponse setup leaks who input.1 input.2 response ∧
      selected = memory.repairResponse (runtime setup) leaks who input.2 response ∧
      selected.1 ∈ menu.actions who input.1 input.2) := by
  classical
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let input := (repaired.recall who, repaired.observe app who)
  have rawRight := menu.toRawTrace (initialLaw setup) horizon scheduler rightTrace
  have physical := sourceServiceUnclassified_response_transport bounds bound original repaired
    who memory frame leftTrace rightTrace clear response effective notPacket notRecorded
  have sameEnvelope (material : app.Submission)
      (transmission : response.transmission = some material) :
      localServiceEnvelope setup leaks who (original.recall who) (original.observe app who)
          material =
        localServiceEnvelope setup leaks who (repaired.recall who) (repaired.observe app who)
          material := by
    rw [localServiceEnvelope_actual setup leaks leftTrace who material,
      localServiceEnvelope_actual setup leaks rawRight who material]
    rw [show original.network.nextSerial who = repaired.network.nextSerial who from
      congrArg (fun network => network.nextSerial who) frame.network,
      physical.2.2 material transmission]
  have rightNotPacket : ¬ auditableServiceResponse setup leaks who input.1 input.2 response := by
    rintro ⟨material, transmission, classified⟩
    apply notPacket
    refine ⟨material, transmission, ?_⟩
    change AuditableServicePacket setup repaired.application.publicView who _ at classified
    change AuditableServicePacket setup original.application.publicView who _
    rwa [← frame.publicView, ← sameEnvelope material transmission] at classified
  have rightNotRecorded : ¬ recordedServiceResponse setup leaks input.1 response := by
    rintro ⟨event, recorded, named⟩
    apply notRecorded
    exact ⟨event, ((runtime setup).eventRecorded_congr leaks _ _ frame.submissions event).symm
      ▸ recorded, named⟩
  rcases unclassifiedResponse_cases bounds bound repaired who rightTrace clear response physical.1
      rightNotPacket rightNotRecorded with retained | unusable
  · left
    refine ⟨retained, ?_, ?_⟩
    · simp only [BindingMemory.retainedResponse, MessageBounds.riskMenu, retained, ↓reduceIte]
    · simp only [BindingMemory.retainedResponse, MessageBounds.riskMenu, retained, ↓reduceIte,
        BindingMemory.copyResponse_action]
  · right
    have selected := sourceServiceMissing_unusable_default_retained bounds bound values original
      repaired who memory frame rightTrace clear response effective unusable
    exact ⟨unusable, selected.1, selected.1 ▸ selected.2.1⟩

end Vegas
