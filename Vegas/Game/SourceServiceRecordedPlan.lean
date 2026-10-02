/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedPolicy
import Vegas.Pending.ReactiveSilentApplication

/-! # Physical settlement of already recorded source decisions

A recorded owner packet remains pending as the sole unpublished packet. Later
player turns wait, and reserved inclusion applies that actual packet before the
calendar's clock padding. These are physical plan laws, without an equilibrium
or information-likelihood premise.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Once an event is recorded, later timed responses are transport-only as
long as the event stays the sole ready one and own recall is retained. -/
theorem sourceServiceTimedPolicy_recorded_transport
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (initial : (application setup leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (recorded : (runtime setup).eventRecorded leaks (initial.recall owner) event = true)
    (current : (application setup leaks).Execution)
    (same : current.application = initial.application)
    (retained : initial.recall owner ⊆ current.recall owner)
    (actor : Player) (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile actor
      (current.recall actor) (current.observe (application setup leaks) actor)).support) :
    response = ⟨none⟩ := by
  have currentSole :
      (current.observe (application setup leaks) actor).application.publicView.SoleReady event := by
    change current.application.publicView.SoleReady event
    rw [same]
    exact sole
  by_cases isOwner : actor = owner
  · subst actor
    obtain ⟨entry, present, submitted⟩ := ((runtime setup).eventRecorded_iff leaks _ event).mp
      recorded
    have still := ((runtime setup).eventRecorded_iff leaks _ event).mpr
      ⟨entry, retained present, submitted⟩
    rw [sourceServiceTimedPolicy_recorded setup leaks rosters timing profile owner _ _ event
      (PublicView.ownTurn?_of_ownTurn _ owner event (currentSole.ownTurn owned)) still]
      at supported
    exact (application setup leaks).silentPolicy_cases _ _ response supported
  · have different : (graph setup).actor? event ≠ some actor := by
      rw [owned]
      exact fun same => isOwner (Option.some.inj same).symm
    simp only [sourceServiceTimedPolicy,
      PublicView.ownTurn?_eq_none _ actor (currentSole.idle different)] at supported
    exact (application setup leaks).silentPolicy_cases _ _ response supported

/-- From any execution after the owner's recorded submission, whose envelope
is pending and the only unpublished one, the rest of the phase has the exact
application settlement law: the envelope's handling, followed by the clock
commands. -/
theorem sourceService_recorded_plan_application_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? (graph setup) = some event)
    (packets : execution.network.Satisfies fun candidate =>
      candidate.id ∈ execution.network.ledger.map Message.id ∨ candidate = message)
    (pending : message ∈ execution.network.pending)
    (unpublished : message.id ∉ execution.network.ledger.map Message.id)
    (visits : List Player) (ticks : Nat) :
    let app := application setup leaks
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let ending := List.replicate ticks .tick ++ [.expire event]
    ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner] ++ ending)
      execution).map ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks players network ending
        { execution with
          application := (app.handle execution.application message).getD
            execution.application }).map ReactiveApplication.Execution.application := by
  intro app players ending
  have settled := (runtime setup).silent_window_settlement leaks players network owner execution
    (fun current actor action same recalled supported =>
      sourceServiceTimedPolicy_recorded_transport setup leaks rosters timing profile event owner
        owned execution sole recorded current same recalled actor action supported)
    event message authored addressed packets pending unpublished visits
  have applicationLaw := congrArg (PMF.map Prod.fst) settled
  simp only [PMF.map_comp, Function.comp_def, PMF.pure_map] at applicationLaw
  have passive : ∀ instruction ∈ ending, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [ending, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  rw [runInteractionPlan_append, PMF.map_bind]
  calc
    _ = ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution).bind
          (fun _ => ((runtime setup).runInteractionPlan leaks players network ending
            { execution with
              application := (app.handle execution.application message).getD
                execution.application }).map ReactiveApplication.Execution.application) := by
      apply bind_congr_on_support _
      intro final reached
      have present : final.application ∈ (((runtime setup).runInteractionPlan leaks players
          network (visits.map ServiceInstruction.player ++ [.includeLatest event owner])
          execution).map ReactiveApplication.Execution.application).support :=
        PMF.support_map .. ▸ ⟨final, reached, rfl⟩
      rw [applicationLaw, PMF.mem_support_pure_iff _ _] at present
      exact (runtime setup).application_service_law leaks players network ending passive _ _
        present
    _ = _ := PMF.bind_const _ _

/-- Any transport response after a known current submission leaves the exact
application settlement law unchanged, including all later clock commands. -/
theorem sourceService_recorded_response_application_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? (graph setup) = some event)
    (packets : execution.network.Satisfies fun candidate =>
      candidate.id ∈ execution.network.ledger.map Message.id ∨ candidate = message)
    (pending : message ∈ execution.network.pending)
    (unpublished : message.id ∉ execution.network.ledger.map Message.id)
    (who : Player) (response : (application setup leaks).Action)
    (transport : response = ⟨none⟩)
    (visits : List Player) (ticks : Nat) :
    let app := application setup leaks
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let ending := List.replicate ticks .tick ++ [.expire event]
    ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner] ++ ending)
      (execution.respond app who response)).map ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks players network ending
        { execution with
          application := (app.handle execution.application message).getD
            execution.application }).map ReactiveApplication.Execution.application := by
  intro app players ending
  let after := execution.respond app who response
  have unchanged := (runtime setup).silent_response_preserves leaks _ execution packets who
    response transport
  have respondApplication : after.application = execution.application := unchanged.1
  have afterSole : after.application.publicView.SoleReady event := by
    rw [unchanged.1]
    exact sole
  have still : (runtime setup).eventRecorded leaks (after.recall owner) event = true :=
    (runtime setup).eventRecorded_respond_of_recorded leaks execution who owner response event
      recorded
  have safe : after.network.Satisfies fun candidate =>
      candidate.id ∈ after.network.ledger.map Message.id ∨ candidate = message := by
    rw [unchanged.2.1]
    exact unchanged.2.2.2.2.1
  have remains : message ∈ after.network.pending := unchanged.2.2.2.2.2 pending
  have unspent : message.id ∉ after.network.ledger.map Message.id := by
    rw [unchanged.2.1]
    exact unpublished
  have law := sourceService_recorded_plan_application_law setup leaks rosters timing profile
    network event owner owned after afterSole still message authored addressed safe remains unspent
    visits ticks
  dsimp only at law
  rw [law]
  have passive : ∀ instruction ∈ ending, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [ending, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  exact (runtime setup).application_service_law leaks players network ending passive _ _
    (by simp only [respondApplication]; rfl)

end Vegas
