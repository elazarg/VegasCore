/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceHarmlessContinuation
import Vegas.Game.SourceServiceSubmittedBinding

/-! # Harmless continuations after an already submitted binding

The authentic pending binding remains selected through every replay choice.
Once the binding has been recorded, the timed compiler uses replay-only laws
at all remaining visits. Its application endpoint and full typed source
continuation are independent of the current retained transport response.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Once an event is recorded, later timed responses are transport-only as
long as the application grant is unchanged and own recall is retained. -/
theorem sourceServiceTimedPolicy_recorded_transport
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (initial : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (recorded : (runtime setup).eventRecorded leaks (initial.recall owner) event = true)
    (current : (application setup leaks).Execution)
    (same : current.application = initial.application)
    (recall : initial.recall owner ⊆ current.recall owner)
    (actor : Player) (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile actor
      (current.recall actor) (current.observe (application setup leaks) actor)).support) :
    response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
  have grant : PublicView.serviceGrant
      (current.observe (application setup leaks) actor).application.publicView = some event := by
    change current.application.serviceGrant = _
    rw [same, granted]
  by_cases isOwner : actor = owner
  · subst actor
    obtain ⟨entry, present, submitted⟩ := ((runtime setup).eventRecorded_iff leaks _ event).mp
      recorded
    have still := ((runtime setup).eventRecorded_iff leaks _ event).mpr
      ⟨entry, recall present, submitted⟩
    rw [sourceServiceTimedPolicy_recorded setup leaks rosters timing profile owner _ _ event
      grant still] at supported
    exact (application setup leaks).replayPolicy_cases _ _ response supported
  · have different : (graph setup).actor? event ≠ some actor := by
      rw [owned]
      exact fun same => isOwner (Option.some.inj same).symm
    simp only [sourceServiceTimedPolicy, grant, dite_eq_right different] at supported
    exact (application setup leaks).replayPolicy_cases _ _ response supported

/-- Any transport response after a known current submission leaves the exact
application settlement law unchanged, including all later clock commands. -/
theorem sourceService_recorded_response_application_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? (graph setup) = some event)
    (packets : execution.network.Satisfies fun candidate =>
      candidate.id ∈ execution.network.ledger.map Message.id ∨ candidate = message)
    (pending : message ∈ execution.network.pending)
    (unpublished : message.id ∉ execution.network.ledger.map Message.id)
    (who : Player) (response : (application setup leaks).Action)
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (visits : List Player) (ticks : Nat) :
    let app := application setup leaks
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let ending := List.replicate ticks .tick ++ [.expire event]
    ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner] ++ ending)
      (execution.respond app who response)).map ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks players network ending
        { execution with application := (app.handle execution.application message).getD
          execution.application }).map ReactiveApplication.Execution.application := by
  intro app players ending
  let after := execution.respond app who response
  have unchanged := (runtime setup).replay_response_preserves leaks _ execution packets who
    response transport
  have grant : after.application.serviceGrant = some event := by
    rw [unchanged.1]
    exact granted
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
  have settled := (runtime setup).replay_window_settlement leaks players network owner after
    (fun current actor action same recalled supported =>
      sourceServiceTimedPolicy_recorded_transport setup leaks rosters timing profile event owner
        owned after grant still current same recalled actor action supported)
    event message authored addressed safe remains unspent visits
  have applicationLaw := congrArg (FinDist.map Prod.fst) settled
  simp only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] at applicationLaw
  have passive : ∀ instruction ∈ ending, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [ending, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  rw [runInteractionPlan_append, FinDist.map_bind]
  calc
    _ = ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) after).bind
          (fun _ => ((runtime setup).runInteractionPlan leaks players network ending
            { execution with application := (app.handle execution.application message).getD
              execution.application }).map ReactiveApplication.Execution.application) := by
      apply FinDist.bind_congr
      intro final reached
      have present : final.application ∈ (((runtime setup).runInteractionPlan leaks players
          network (visits.map ServiceInstruction.player ++ [.includeLatest event owner])
          after).map ReactiveApplication.Execution.application).support :=
        FinDist.support_map .. ▸ ⟨final, reached, rfl⟩
      rw [applicationLaw, FinDist.mem_support_pure] at present
      exact (runtime setup).application_service_law leaks players network ending passive _ _
        (by simpa only [unchanged.1] using present)
    _ = _ := FinDist.bind_const _ _

variable [Fintype Player]

/-- At any actual retained decision after the owner has submitted its binding,
all legal current responses have the same full source terminal law. This also
covers a foreign player's visit during the remaining binding roster. -/
theorem sourceService_recorded_binding_response_source_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing profile who))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (assessment : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : assessment.strategy = fun who =>
      (sourceServiceMenu setup leaks bounds rosters).restrictPolicy (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
          (sourceServiceTimedPolicy setup leaks rosters timing profile who))
    (mixed : assessment.IsFullyMixed)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (granted : execution.application.serviceGrant = some event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (before : List (ServiceInstruction (graph setup))) (visits : List Player)
    (split : rosterPlanPrefix setup rosters (event.val + 1) = before ++ .player who ::
      (visits.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])))
    (position : execution.environmentRecall.length = before.length + 1)
    (first second : (application setup leaks).Action)
    (firstAllowed : first ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (secondAllowed : second ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who)) :
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let tail := visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]) ++
      ((List.finRange (graph setup).order.eventCount).drop (event.val + 1)).flatMap
        (rosterBlock setup rosters)
    ((runtime setup).runInteractionPlan leaks players network tail
      (execution.respond (application setup leaks) who first)).map
        (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      ((runtime setup).runInteractionPlan leaks players network tail
        (execution.respond (application setup leaks) who second)).map
          (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) := by
  intro players tail
  let app := application setup leaks
  let id : MessageId Player :=
    (owner, execution.network.ledger.countP (fun message => message.sender = owner))
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨id, ⟨.commitment event (owner, .prepared
      (execution.application.publicView.bindingCount owner)), none⟩⟩
  obtain ⟨value, _, _, _, _, _, pending, packets, _, selected⟩ :=
    sourceService_recorded_binding_resources setup leaks bounds values capacity rosters
      opportunities network profile who ⟨remaining, some who, execution⟩ trace rfl event granted
      owner payload outputEq codeEq node owned recorded
  have unpublished : message.id ∉ execution.network.ledger.map Message.id := by
    unfold reactiveLatest at selected
    split at selected
    · cases selected
    · rename_i packet found
      have good : packet.sender = owner ∧
          packet.payload.call.event? (graph setup) = some event ∧
          (execution.observeEnvironment app).Unpublished app packet.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have same : packet.id = message.id := ReactiveApplication.Command.include.inj selected
      exact same ▸ good.2.2
  have transport (response : app.Action)
      (allowed : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
        (execution.recall who) (execution.observe app who)) :
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
    have supported := roster_fullyMixed_response_support setup leaks rosters network
      (sourceServiceMenu setup leaks bounds rosters) players covered assessment strategy mixed
      who remaining execution trace response allowed
    exact sourceServiceTimedPolicy_recorded_transport setup leaks rosters timing profile event
      owner owned execution granted recorded execution rfl (List.Subset.refl _) who response
      supported
  have law (response : app.Action)
      (allowed : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
        (execution.recall who) (execution.observe app who)) :=
    sourceService_recorded_response_application_law setup leaks rosters timing profile network
      event owner owned execution granted recorded message rfl rfl packets pending unpublished
      who response (transport response allowed) visits (event.val + 1)
  apply sourceService_response_continuation_congr setup leaks bounds values capacity rosters
    opportunities timing network profile covered effective assessment strategy mixed
    who remaining execution trace (event.val + 1) event.isLt _ _ split position first second
    firstAllowed secondAllowed
  simpa only [List.append_assoc, List.singleton_append] using
    (law first firstAllowed).trans (law second secondAllowed).symm

end Vegas.SourceProgram.RevealService
