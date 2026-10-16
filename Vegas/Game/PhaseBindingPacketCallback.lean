/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseContinuingBinding
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.ReactiveEmissionTokens

/-! # Original canonical callback of every actual owned binding packet -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (assessment.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)

local notation "P" => phaseApplication runtime leaks
local notation "A" => phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)

include continuing maximal ordered

/-- Every actual owned packet for a binding retains its genuine unsent
canonical callback. Its original request, full prior word and supported source
response are derived; accepted unusable typed results are retained. -/
theorem phase_binding_packet_callback (horizon : Nat) (scheduler : (P).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol start horizon
      scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅) (owner : Player)
    (consistent : (A owner).Consistent (current.execution.recall owner))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup mode)))
    (output : message ∈ (P).outputs (current.execution.recall owner))
    (named : PhaseCount.event? message.payload =
      some ⟨current.execution.application.attempt, event⟩) :
    ∃ (entry : (P).PlayerEntry) (before : (P).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol start horizon
        scheduler).Trace
        (some before)),
      entry ∈ current.execution.recall owner ∧ entry.emitted = some message ∧
      TracePrefix prior trace ∧ before.actor = some owner ∧
      before.execution.application.attempt = current.execution.application.attempt ∧
      before.execution.application.SeedRequest owner
        ⟨before.execution.application.attempt, event⟩ ∧
      entry.beforeView = before.execution.observe P owner ∧
      entry.action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (before.execution.recall owner) (before.execution.observe P owner) ∧
      (∃ serial result, entry.action =
        phaseBindingResponse runtime leaks owner event payload result serial) ∧
      ∃ after, current.execution.recall owner =
        before.execution.recall owner ++ entry :: after := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs := setup.initialLaw.map encodeInputs
  obtain ⟨entry, recorded, emitted⟩ := List.mem_filterMap.mp output
  have nested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace
      (some current) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have raw := menu.toRawTrace start horizon scheduler trace
  have nativePrior := PhaseNativeProjection.nativeTrace runtime leaks plan bounds ordered maximal
    inputs horizon scheduler nested (fun _ same => by cases same; exact clear)
  let nativeEntry := PhaseNativeProjection.playerEntry runtime leaks plan entry
  have nativeRecorded : nativeEntry ∈
      (PhaseNativeProjection.execution runtime leaks plan current.execution).recall owner :=
    List.mem_map.mpr ⟨entry, recorded, rfl⟩
  have nativeEmitted : nativeEntry.emitted =
      some (Message.mapPayload CommitAttemptPacket.packet message) := by
    change entry.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = _
    rw [emitted]
    rfl
  have emission := reactiveEmission_history runtime
    (PhaseNativeProjection.nativeLeaks leaks plan) (inputs.map State.initial) horizon
      (PhaseNativeProjection.nativeScheduler runtime leaks plan scheduler)
        (PhaseNativeProjection.control runtime leaks plan current) nativePrior owner
  obtain ⟨material, transmitted⟩ : ∃ material, entry.action.transmission = some material := by
    cases sent : entry.action.transmission with
    | none =>
        have absent := emission.1 nativeEntry nativeRecorded sent
        rw [nativeEmitted] at absent
        cases absent
    | some material => exact ⟨material, rfl⟩
  obtain ⟨nativeMessage, nativeSent, call⟩ :=
    emission.2 nativeEntry nativeRecorded material transmitted
  have sameMessage : nativeMessage = Message.mapPayload CommitAttemptPacket.packet message :=
    Option.some.inj (nativeSent.symm.trans nativeEmitted)
  have materialNamed : material.call.packet.event? (serviceGraph setup mode) = some event := by
    unfold PhaseCount.event? at named
    obtain ⟨actual, addressed, same⟩ := Option.map_eq_some_iff.mp named
    have sameEvent : actual = event := congrArg CommitAttemptEvent.event same
    subst actual
    rw [sameMessage] at call
    exact call.symm ▸ addressed
  obtain ⟨before, prior, retained, acting, viewed, supported, after, recalled⟩ :=
    menu.recorded_response_supported start horizon scheduler current trace owner (A owner)
      consistent entry recorded
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu start horizon
    scheduler before current prior trace retained clear).1
  have offered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment
    owner _ _ entry.action supported
  have sentMember : (⟨some material⟩ : (P).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds
      owner (before.execution.recall owner) (before.execution.observe P owner) := by
    have same : entry.action = (⟨some material⟩ : (P).Action) := by
      cases action : entry.action with
      | mk transmission =>
          rw [action] at transmitted
          exact congrArg ReactiveApplication.Action.mk transmitted
    rwa [same] at offered
  have beforeNested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact prior
  rcases before with ⟨remaining, actor, physical⟩
  cases acting
  obtain ⟨coordinate, request⟩ :=
    PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds plan
    inputs horizon scheduler remaining owner physical beforeNested material sentMember
  have addressed := PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
    horizon scheduler remaining owner physical beforeNested coordinate request material sentMember
  have sameEvent : coordinate.event = event :=
    Option.some.inj (addressed.symm.trans materialNamed)
  have sameCoordinate : coordinate = ⟨physical.application.attempt, event⟩ := by
    rcases coordinate with ⟨attempt, actual⟩
    dsimp only at request sameEvent
    cases sameEvent
    cases request.1
    rfl
  rw [sameCoordinate] at request
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner physical beforeNested _ request material sentMember
  obtain ⟨serial, result, _bounded, response⟩ := phaseSourcePolicy_binding_emits_of_continuing
    setup mode runtime leaks bounds wellFormed assessment continuing plan maximal horizon scheduler
      capacity ⟨remaining, some owner, physical⟩ prior owner rfl event payload binding request
        unsent
        values beforeClear entry.action supported
  have tag := phase_recalled_emission_attempt runtime leaks start horizon scheduler raw owner
    entry
    recorded message emitted
  rw [viewed] at tag
  have messageAttempt : message.payload.attempt = current.execution.application.attempt := by
    unfold PhaseCount.event? at named
    obtain ⟨actual, _addressed, same⟩ := Option.map_eq_some_iff.mp named
    exact congrArg CommitAttemptEvent.attempt same
  exact ⟨entry, ⟨remaining, some owner, physical⟩, prior, recorded, emitted, retained, rfl,
    tag.symm.trans messageAttempt, request, viewed, offered, ⟨serial, result, response⟩, after,
    recalled⟩

end Vegas
