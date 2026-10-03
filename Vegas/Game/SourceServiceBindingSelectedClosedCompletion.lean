/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSelectedContinuation

/-! # The literal selected family after a closed-gate response

The family's actual selected response is silent once protection closes. Its
whole continuation agrees with the owner-silent kernel; the initialized raw
clock and activation invariants also identify this with the literal source
turn-policy continuation. Complete play then records a real public miss and
typed binding failure. This is an operational law of that literal policy,
not a claim that its late continuation is sequentially rational.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every completed continuation after the actual selected closed-gate silence
is a public miss, with no owner packet and typed failure. Foreign policies are
arbitrary raw policies, and no future miss or completion is assumed. -/
theorem sourceService_binding_selected_closed_completion
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (middle : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, middle⟩))
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (owned : (graph setup).actor? event = some owner)
    (slot : Fin (turns + 1))
    (selected : sourceServiceTurn setup leaks owner event (middle.recall owner)
      (middle.observe (application setup leaks) owner) = some slot.val)
    (unrecorded : (runtime setup).eventRecorded leaks (middle.recall owner) event = false)
    (closed : ¬ middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (middle.respond (application setup leaks) owner ⟨none⟩)).support) :
    event ∈ stopped.application.config.cut.completed ∧
      event ∈ stopped.application.missedEvents ∧
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.binding owner payload)).get? stopped.application.config.store = some .failure ∧
      (runtime setup).eventRecorded leaks (stopped.recall owner) event = false ∧
      stopped.network.Satisfies (fun message => message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) := by
  let app := application setup leaks
  let start := middle.respond app owner ⟨none⟩
  have turn : middle.application.publicView.ownTurn? owner = some event := by
    unfold sourceServiceTurn at selected
    split at selected
    · assumption
    · cases selected
  have ready : start.application.config.cut.Ready event :=
    (middle.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ owner event turn).1
  have startUnrecorded : (runtime setup).eventRecorded leaks (start.recall owner) event = false :=
    ((runtime setup).eventRecorded_respond_other leaks middle owner owner ⟨none⟩ event
      (fun _ impossible => by cases impossible)).trans unrecorded
  obtain ⟨startTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler remaining middle
    owner ⟨none⟩ trace
  have valid := (roster_trace_facts setup leaks horizon scheduler startTrace).1
  obtain ⟨inputs, valid⟩ := valid
  have originalLaw : app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon start =
      app.runUntilHorizon scheduler (Function.update players owner app.silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon start := by
    unfold ReactiveApplication.runUntilHorizon
    exact sourceServiceTurnPolicy_runUntil_owner_closed scheduler players bound turns timing profile
      owner follows _ start valid event ready owned closed
  rw [sourceService_selected_continuation_silent scheduler players bound profile owner
    event turns slot middle selected, ← originalLaw] at reached
  exact sourceService_binding_no_attempt contract players timing profile owner follows start
    startTrace event ready owned payload outputEq startUnrecorded closed stopped reached

end Vegas
