/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelection
import Vegas.Game.SourceServiceAsyncTimeliness

/-! # The sole actual packet of a manual first binding call

An initialized raw prefix's owner recall determines whether it has issued a
packet naming the current event. An unrecorded event has no earlier such
owner envelope anywhere in the network. After one canonical manual call,
the recorded owner is silent until completion, for any timing policy. Foreign
raw policies and every public scheduler command preserve the sole actual
signed packet, including its readiness token and identifier.

The manual call need not be supported by the protected timing policy. No
acceptance, completion or watcher observation is assumed here.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Actual envelope provenance and an unrecorded own event exclude every
earlier owner packet naming that event from the entire network. -/
theorem sourceService_unrecorded_event_packets
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId)
    (origins : execution.Provenance (application setup leaks))
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false) :
    execution.network.Satisfies (fun message => message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event) := by
  apply origins.mono
  intro message origin authored named
  obtain ⟨entry, member, material, transmission, emitted, state, known, packet⟩ := origin
  rw [authored] at member
  have selected : (runtime setup).submittedEvent? leaks entry.action = some event := by
    unfold EventGraphRuntime.submittedEvent?
    rw [transmission]
    change material.call.packet.event? (graph setup) = some event
    have call : material.call.packet = message.payload.call :=
      (WitnessedSubmission.emit_call material state message.sender known).symm.trans
        (congrArg WitnessedPacket.call packet)
    rwa [call]
  have recorded := ((runtime setup).eventRecorded_iff leaks _ event).mpr
    ⟨entry, member, selected⟩
  rw [unrecorded] at recorded
  cases recorded

private theorem environment_packets
    (app : ReactiveApplication Player) (execution next : app.Execution)
    (command : app.Command) (safe : Message Player app.Payload → Prop)
    (packets : execution.network.Satisfies safe)
    (moved : next ∈ (execution.environmentStep app command).support) :
    next.network.Satisfies safe := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact packets
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact packets.learn who selected
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      have kept := packets.includePending id
      cases found : execution.network.lookup id <;>
        simpa only [ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found] using kept
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact packets

private theorem silent_owner_packets
    (app : ReactiveApplication Player) (players : Player → app.Policy)
    (owner : Player) (safe : Message Player app.Payload → Prop)
    (foreign : ∀ message, message.sender ≠ owner → safe message) :
    app.PolicyInvariant (Function.update players owner app.silentPolicy)
      (fun execution => execution.network.Satisfies safe) where
  respond execution who response valid supported := by
    by_cases own : who = owner
    · subst who
      rw [Function.update_self] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact valid
    · rcases response with ⟨transmission⟩
      cases transmission with
      | none => exact valid
      | some material =>
          apply valid.submit who
          exact foreign _ own
  environment execution next command valid moved :=
    environment_packets app execution next command safe valid moved

private theorem first_binding_packets
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (payload : L.Ty)
    (value : PublicationResult (L.Val payload)) (serial : Nat)
    (absent : execution.network.Satisfies (fun message => message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)) :
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none,
          execution.application.publicView.tokenFor
            (.commitment event (owner, .prepared serial))⟩⟩
    (execution.respond (application setup leaks) owner
      ((runtime setup).reactiveBinding leaks owner event payload value serial)).network.Satisfies
      (fun packet => packet.sender = owner →
        packet.payload.call.event? (graph setup) = some event → packet = message) := by
  let app := application setup leaks
  have prior : execution.network.Satisfies (fun packet => packet.sender = owner →
      packet.payload.call.event? (graph setup) = some event →
        packet = ⟨(owner, execution.network.nextSerial owner),
          ⟨.commitment event (owner, .prepared serial), none,
            execution.application.publicView.tokenFor
              (.commitment event (owner, .prepared serial))⟩⟩) := by
    apply absent.mono
    intro packet safe author named
    exact (safe author named).elim
  change (execution.network.submit owner _).2.Satisfies _
  apply prior.submit owner
  intro _ _
  apply congrArg (fun content : WitnessedPacket (graph setup) =>
    (⟨(owner, execution.network.nextSerial owner), content⟩ :
      Message Player (WitnessedPacket (graph setup))))
  exact reactiveApplication_packet_none (runtime setup) leaks execution.application owner
    (execution.network.known owner) _

/-- Every retained owner packet for this binding is the exact original manual
call. Its identifier and full envelope persist jointly through the actual
completion-stopped continuation, with arbitrary foreign raw policies. -/
theorem sourceService_binding_first_packet
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (horizon remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (payload : L.Ty) (value : PublicationResult (L.Val payload)) (serial : Nat) :
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none,
          execution.application.publicView.tokenFor
            (.commitment event (owner, .prepared serial))⟩⟩
    ∀ final ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun current => event ∈ current.application.config.cut.completed) horizon
      (execution.respond (application setup leaks) owner
        ((runtime setup).reactiveBinding leaks owner event payload value serial))).support,
      final.network.Satisfies (fun packet => packet.sender = owner →
        packet.payload.call.event? (graph setup) = some event → packet = message) := by
  let app := application setup leaks
  let response := (runtime setup).reactiveBinding leaks owner event payload value serial
  let submitted := execution.respond app owner response
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, execution.network.nextSerial owner),
      ⟨.commitment event (owner, .prepared serial), none,
        execution.application.publicView.tokenFor
          (.commitment event (owner, .prepared serial))⟩⟩
  let safe := fun packet : Message Player (WitnessedPacket (graph setup)) =>
    packet.sender = owner → packet.payload.call.event? (graph setup) = some event →
      packet = message
  have packets : submitted.network.Satisfies safe := first_binding_packets setup leaks execution
    owner event payload value serial
      (sourceService_unrecorded_event_packets setup leaks execution owner event
      (legalFacts setup leaks horizon scheduler _ trace).provenance unrecorded)
  have afterReady : submitted.application.config.cut.Ready event := by
    rw [((runtime setup).reactive_respond_application leaks execution owner response).1]
    exact ready
  have recorded : (runtime setup).eventRecorded leaks (submitted.recall owner) event = true :=
    (runtime setup).eventRecorded_respond leaks execution owner response event rfl
  change ∀ final ∈ (app.runUntilHorizon scheduler players
    (fun current => event ∈ current.application.config.cut.completed) horizon submitted).support,
      final.network.Satisfies safe
  intro final reached
  change final ∈ (app.runUntilHorizon scheduler players
    (fun current => event ∈ current.application.config.cut.completed) horizon submitted).support
    at reached
  unfold ReactiveApplication.runUntilHorizon at reached
  rw [sourceServiceTurnPolicy_runUntil_owner_silent setup leaks scheduler players bound turns
    timing profile owner follows _ submitted event afterReady owned recorded] at reached
  obtain ⟨used, _budget, rounds, _length⟩ := app.runUntil_runRounds scheduler _ _ _ submitted
    final reached
  exact (silent_owner_packets app players owner safe (fun packet foreign authored _named =>
    (foreign authored).elim)).runRounds scheduler used submitted final packets rounds

end Vegas
