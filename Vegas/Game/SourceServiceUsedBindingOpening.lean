/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUsedBindingOpening
import Vegas.Game.SourceServiceProtectedBinding
import Vegas.Game.SourceServiceAuditableCollection

/-! # Auditable extra certificates after a protected mistyped binding

A later owned resolution proves that a recalled earlier binding has completed.
Protected inclusion and its sole owner identifier then derive the actual used
handle. Any opening claim of its mistyped material belongs to the existing
public guard or association breach class, even with an authentic certificate.
The existing committed collection theorem applies under the unchanged partial
final-record coverage contract. This does not construct a legal repair policy
or compare its continuation utility.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A real protected sole binding is already accepted before a later owned
resolution, and an opening of its wrong-typed material is an existing auditable
packet. Actual legal-history resources derive association and provenance. -/
theorem protected_mistyped_binding_opening_auditable
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (owner : Player) (bindingEvent : (graph setup).EventId) (payload : L.Ty)
    (bindingOutput : (graph setup).outputLayout bindingEvent = .binding owner payload)
    (bindingCode : cast (congrArg (EventCode (graph setup).layout) bindingOutput)
      ((graph setup).nodes bindingEvent) = .bind owner payload)
    (bindingNode : nodeView (graph setup) bindingEvent =
      .bind owner payload bindingOutput bindingCode)
    (candidate : Handle (graph setup))
    (earlier later : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (first : Message Player (WitnessedPacket (graph setup)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner bindingEvent bound entry first)
    (committed : first.payload.call = .commitment bindingEvent candidate)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other bindingEvent first.id)
    (event : (graph setup).EventId) (other : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner other))
    (checks : List (GuardCheck (graph setup).layout other))
    (outputEq : (graph setup).outputLayout event = .publication other)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner other binding checks)
    (node : nodeView (graph setup) event = .resolve owner other binding checks outputEq codeEq)
    (turn : control.execution.application.publicView.ownTurn? owner = some event)
    (message : Message Player (WitnessedPacket (graph setup)))
    (raw : Raw L) (mistyped : raw.as? payload = none)
    (opened : message.payload.call = .opening event candidate raw) :
    (first.id, true) ∈ control.execution.receipts ∧
      control.execution.application.publicView.accepted (.inr bindingEvent) = some candidate ∧
      AuditableServicePacket setup control.execution.application.publicView owner message := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  have member : entry ∈ control.execution.recall owner := by rw [split]; simp
  have currentReady := (control.execution.application.publicView_eventReady event).mp
    ((control.execution.application.publicView.ownTurn?_spec owner event turn).1)
  have completed : bindingEvent ∈ control.execution.application.config.cut.completed := by
    by_contra unfinished
    have observed := (entry_view_current setup leaks control.execution facts.stable owner entry
      member bindingEvent call.ready unfinished).1
    have readyPublic : control.execution.application.publicView.EventReady bindingEvent := by
      unfold PublicView.EventReady
      rw [← observed]
      exact call.ready
    have same := ready_unique control.execution.application.config.cut
      ((control.execution.application.publicView_eventReady bindingEvent).mp readyPublic)
        currentReady
    cases same
    rw [bindingNode] at node
    cases node
  have owned := nodeView_bind_actor bindingOutput bindingCode
  have receipt := (prescribed_packet_settles setup leaks inclusion trace bindingEvent owner owned
    earlier later entry first split call sole).2 completed
  have associated := (protected_binding_no_miss setup leaks inclusion trace bindingEvent owner
    candidate owned earlier later entry first split call committed sole).1 completed
  let original : FieldRef (graph setup).layout (.binding owner payload) :=
    ⟨.inr bindingEvent, bindingOutput⟩
  have failure := used_mistyped_opening_public_failure control.execution.application facts.binding
    original candidate associated raw mistyped event owner other binding checks outputEq codeEq
      node message.payload opened
  refine ⟨receipt, associated, Or.inr (Or.inr (Or.inr (Or.inr ⟨event, turn,
    Or.inr ⟨candidate, raw, opened, ?_⟩⟩)))⟩
  rcases failure with guard | wrongAssociation
  · exact Or.inl guard
  · right
    simp only [node]
    exact Or.inr wrongAssociation

end Vegas
