/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettledSound
import Vegas.Pending.EventOpponentFrame
import Vegas.Pending.ReactiveBindingOpeningStep

/-! # Actual packet identities while one owner call is pending

The actual recall split before the first call, its unrecorded event and the
silent later responses identify every looked-up owner packet for that event
with its actual recalled envelope by initialized packet provenance. The proof
uses recalled responses rather than a stipulated sole packet in hidden traffic.
While that binding is ready, every other identifier is rejected on both framed
executions, irrespective of its evidence or the scheduler's chosen include order.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Actual raw provenance, an initially unrecorded event and the later silent
recall determine the entire looked-up owner envelope, including its allocated ID. -/
theorem sourceService_pending_owner_packet_eq
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player)
    (event : (graph setup).EventId)
    (anchor : (application setup leaks).PlayerEntry)
    (earlier later : List (application setup leaks).PlayerEntry)
    (split : control.execution.recall who = earlier ++ anchor :: later)
    (unrecorded : (runtime setup).eventRecorded leaks earlier event = false)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (anchorMessage : Message Player (WitnessedPacket (graph setup)))
    (anchorEmitted : anchor.emitted = some anchorMessage)
    (id : MessageId Player) (packet : WitnessedPacket (graph setup))
    (found : control.execution.network.lookup id = some ⟨id, packet⟩)
    (authored : id.1 = who) (named : packet.call.event? (graph setup) = some event) :
    (⟨id, packet⟩ : Message Player (WitnessedPacket (graph setup))) = anchorMessage := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  obtain ⟨entry, member, _material, transmission, emitted, _state, _known, issued⟩ :=
    facts.provenance.lookup id ⟨id, packet⟩ found
  change entry ∈ control.execution.recall id.1 at member
  rw [authored] at member
  have submitted : (runtime setup).submittedEvent? leaks entry.action = some event :=
    (submittedEvent_of_issued transmission issued).trans named
  rw [split] at member
  rcases List.mem_append.mp member with before | current
  · have recorded : (runtime setup).eventRecorded leaks earlier event = true :=
      List.any_eq_true.mpr ⟨entry, before, decide_eq_true submitted⟩
    rw [unrecorded] at recorded
    cases recorded
  · rcases List.mem_cons.mp current with same | after
    · subst entry
      exact Option.some.inj (emitted.symm.trans anchorEmitted)
    · rw [silent entry after] at transmission
      cases transmission

/-- Any different actual identifier is rejected while the anchored owned
binding remains ready. Possible private capabilities cannot bypass public
readiness, actor authentication or the actual recalled packet identity. -/
theorem sourceService_pending_other_packet_rejected
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, original⟩))
    (event : (graph setup).EventId)
    (ready : original.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who)
    (anchor : (application setup leaks).PlayerEntry)
    (earlier later : List (application setup leaks).PlayerEntry)
    (split : original.recall who = earlier ++ anchor :: later)
    (unrecorded : (runtime setup).eventRecorded leaks earlier event = false)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (anchorMessage : Message Player (WitnessedPacket (graph setup)))
    (anchorEmitted : anchor.emitted = some anchorMessage)
    (id : MessageId Player) (packet : WitnessedPacket (graph setup))
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (different : id ≠ anchorMessage.id) :
    (application setup leaks).handle original.application ⟨id, packet⟩ = none ∧
      (application setup leaks).handle repaired.application ⟨id, packet⟩ = none := by
  have reject (state : EventGraphRuntime.State (graph setup))
      (samePublic : state.publicView = original.application.publicView) :
      (application setup leaks).handle state ⟨id, packet⟩ = none := by
    cases handled : (application setup leaks).handle state ⟨id, packet⟩ with
    | none => rfl
    | some next =>
        have accepted := reactiveHandle_call handled
        obtain ⟨addressed, named, actualReady, _action, _stepped⟩ :=
          handle_config_mem_step (runtime setup) state next ⟨id, packet.call⟩ accepted
        have originalReady : original.application.config.cut.Ready addressed := by
          rw [← State.publicView_eventReady, ← samePublic, State.publicView_eventReady]
          exact actualReady
        have sameEvent : addressed = event := ready_unique _ originalReady ready
        subst addressed
        obtain ⟨actorEvent, actorNamed, actor⟩ :=
          handle_event_actor (runtime setup) state next ⟨id, packet.call⟩ accepted
        have actorSame : actorEvent = event := Option.some.inj (actorNamed.symm.trans named)
        subst actorEvent
        have sender : id.1 = who := Option.some.inj (actor.symm.trans owned)
        have sameMessage := sourceService_pending_owner_packet_eq _ trace who event anchor
          earlier later split unrecorded silent anchorMessage anchorEmitted id packet found
            sender named
        exact False.elim (different (congrArg Message.id sameMessage))
  exact ⟨reject original.application rfl, reject repaired.application frame.publicView.symm⟩

/-- Consuming that rejected identifier records the same real false receipt
and preserves the full frame; no assumed rejection verdict is supplied. -/
theorem sourceService_pending_other_packet_frame
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, original⟩))
    (event : (graph setup).EventId)
    (ready : original.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who)
    (anchor : (application setup leaks).PlayerEntry)
    (earlier later : List (application setup leaks).PlayerEntry)
    (split : original.recall who = earlier ++ anchor :: later)
    (unrecorded : (runtime setup).eventRecorded leaks earlier event = false)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (anchorMessage : Message Player (WitnessedPacket (graph setup)))
    (anchorEmitted : anchor.emitted = some anchorMessage)
    (id : MessageId Player) (packet : WitnessedPacket (graph setup))
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (different : id ≠ anchorMessage.id) :
    let app := application setup leaks
    memory.Frame (runtime setup) leaks who
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have rejected := sourceService_pending_other_packet_rejected original repaired who memory frame
    trace event ready owned anchor earlier later split unrecorded silent anchorMessage
      anchorEmitted id packet found different
  exact frame.include_rejected id packet found rejected.1 rejected.2

end Vegas
