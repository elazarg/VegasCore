/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLocalComparison
import Vegas.Pending.ReactiveReplayApplication
import Vegas.Game.SourceServiceSubmittedBinding

/-! # Owner visits after an already submitted binding

The authentic pending binding remains selected through every replay choice.
Once the binding has been recorded, the timed compiler uses replay-only laws
at all remaining visits. The application law at the next event boundary is
therefore independent of the owner's current legal response, and the generic
local comparison gives zero gain at every such owner site.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Once an event is recorded, later timed responses are transport-only as
long as the application grant is unchanged and own recall is retained. -/
theorem sourceServiceTimedPolicy_recorded_transport
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (initial : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (recorded : (runtime setup).eventRecorded leaks (initial.recall owner) event = true)
    (current : (application setup leaks).Execution)
    (same : current.application = initial.application)
    (retained : initial.recall owner ⊆ current.recall owner)
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
      ⟨entry, retained present, submitted⟩
    rw [sourceServiceTimedPolicy_recorded setup leaks rosters timing profile owner _ _ event
      grant still] at supported
    exact (application setup leaks).replayPolicy_cases _ _ response supported
  · have different : (graph setup).actor? event ≠ some actor := by
      rw [owned]
      exact fun same => isOwner (Option.some.inj same).symm
    simp only [sourceServiceTimedPolicy, grant, dite_eq_right different] at supported
    exact (application setup leaks).replayPolicy_cases _ _ response supported

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
    (granted : execution.application.serviceGrant = some event)
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
  have settled := (runtime setup).replay_window_settlement leaks players network owner execution
    (fun current actor action same recalled supported =>
      sourceServiceTimedPolicy_recorded_transport setup leaks rosters timing profile event owner
        owned execution granted recorded current same recalled actor action supported)
    event message authored addressed packets pending unpublished visits
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
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution).bind
          (fun _ => ((runtime setup).runInteractionPlan leaks players network ending
            { execution with
              application := (app.handle execution.application message).getD
                execution.application }).map ReactiveApplication.Execution.application) := by
      apply FinDist.bind_congr
      intro final reached
      have present : final.application ∈ (((runtime setup).runInteractionPlan leaks players
          network (visits.map ServiceInstruction.player ++ [.includeLatest event owner])
          execution).map ReactiveApplication.Execution.application).support :=
        FinDist.support_map .. ▸ ⟨final, reached, rfl⟩
      rw [applicationLaw, FinDist.mem_support_pure] at present
      exact (runtime setup).application_service_law leaks players network ending passive _ _
        present
    _ = _ := FinDist.bind_const _ _

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
        { execution with
          application := (app.handle execution.application message).getD
            execution.application }).map ReactiveApplication.Execution.application := by
  intro app players ending
  let after := execution.respond app who response
  have unchanged := (runtime setup).replay_response_preserves leaks _ execution packets who
    response transport
  have respondApplication : after.application = execution.application := unchanged.1
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
  have law := sourceService_recorded_plan_application_law setup leaks rosters timing profile
    network event owner owned after grant still message authored addressed safe remains unspent
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

/-- A binding output has the binding node code. -/
theorem binding_nodeView (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload) :
    ∃ codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind owner payload,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
  cases viewed : nodeView (graph setup) event with
  | sample other law kind code => cases kind.symm.trans outputEq
  | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
  | bind other otherPayload kind code =>
      obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
      exact ⟨code, rfl⟩

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

include approx in
/-- At an actual decision after the event's binding is recorded, every legal
current response of any player leaves the same configuration law at the next
event boundary. -/
theorem recorded_phase_invariant {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph service.setup).outputLayout phase.event = .binding owner payload)
    (recorded : (runtime service.setup).eventRecorded service.leaks (execution.recall owner)
      phase.event = true)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second := by
  have owned := binding_actor service.setup phase.event owner payload outputEq
  obtain ⟨codeEq, node⟩ := binding_nodeView service.setup phase.event owner payload outputEq
  let id : MessageId Player :=
    (owner, execution.network.ledger.countP (fun message => message.sender = owner))
  let message : Message Player (WitnessedPacket (graph service.setup)) :=
    ⟨id, ⟨.commitment phase.event (owner, .prepared
      (execution.application.publicView.bindingCount owner)), none⟩⟩
  obtain ⟨value, _, _, _, _, _, pending, packets, _, selected⟩ :=
    sourceService_recorded_binding_resources service.setup service.leaks service.bounds
      service.values service.capacity service.rosters service.opportunities.binding
      service.network who ⟨remaining, some who, execution⟩ trace rfl phase.event phase.granted
      owner payload outputEq codeEq node owned recorded
  have unpublished : message.id ∉ execution.network.ledger.map Message.id := by
    unfold reactiveLatest at selected
    split at selected
    · cases selected
    · rename_i packet found
      have good : packet.sender = owner ∧
          packet.payload.call.event? (graph service.setup) = some phase.event ∧
          (execution.observeEnvironment (application service.setup service.leaks)).Unpublished
            (application service.setup service.leaks) packet.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have same : packet.id = message.id := ReactiveApplication.Command.include.inj selected
      exact same ▸ good.2.2
  have transport (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
    have supported := roster_fullyMixed_response_support service.setup service.leaks service.rosters
      service.network service.menu approx.players approx.covered approx.assessment
      approx.strategy approx.mixed who remaining execution trace response allowed
    exact sourceServiceTimedPolicy_recorded_transport service.setup service.leaks service.rosters
      approx.timing approx.profile phase.event owner owned execution phase.granted recorded
      execution rfl (List.Subset.refl _) who response supported
  have ending : rosterPhaseEnding service.setup phase.event =
      [.includeLatest phase.event owner] ++
        (List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]) := by
    simp only [rosterPhaseEnding, owned, List.append_assoc]
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :=
    sourceService_recorded_response_application_law service.setup service.leaks service.rosters
      approx.timing approx.profile service.network phase.event owner owned execution phase.granted
      recorded message rfl rfl packets pending unpublished who response (transport response allowed)
      phase.visits (phase.event.val + 1)
  have applications := (law first firstAllowed).trans (law second secondAllowed).symm
  simp only [phaseConfigLaw, phaseLaw, DecisionPhase.tail, ending]
  simpa only [List.append_assoc, FinDist.map_comp, Function.comp_def] using
    congrArg (FinDist.map EventGraphRuntime.State.config) applications

open Classical in
/-- At an owner's information site after its binding is recorded, every local
lottery has the prescribed continuation law, for every belief over the site. -/
theorem recorded_comparison_eq (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .binding who payload)
    (granted : view.application.publicView.serviceGrant = some event)
    (recorded : (runtime service.setup).eventRecorded service.leaks past event = true)
    (law : FinDist (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparison service.readout service.fuel
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  apply approx.comparison_eq_of_phase_invariant who site
  intro history remaining execution current info phase first second firstAllowed secondAllowed
  have input := Option.some.inj
    ((service.infoOf_decision history current).symm.trans (info.trans observed))
  have grant : execution.application.serviceGrant = some event :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.serviceGrant) input).trans granted
  have same : phase.event = event := Option.some.inj (phase.granted.symm.trans grant)
  subst same
  have ownRecall : execution.recall who = past := congrArg Prod.fst input
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  exact approx.recorded_phase_invariant trace phase who payload outputEq
    (ownRecall ▸ recorded) first second firstAllowed secondAllowed

end TimedApproximant

end Vegas
