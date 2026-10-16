/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCanonicalFreshness
import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.ReactiveEmissionTokens
import Vegas.Pending.ReactiveOwnerOpportunity
import Vegas.Pending.PhaseActivationResponse
import Vegas.Pending.PhaseAttemptCheckpoint

/-! # Original opportunity protects every canonical unsent opening callback -/

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
  (source : ∀ owner, setup.intendedModel.BehavioralPolicy owner)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (delay bound : (serviceGraph setup mode).EventId → Nat)

local notation "P" => phaseApplication runtime leaks
local notation "start" =>
  PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs)
local notation "NL" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "N" => runtime.reactiveApplication NL

include copies maximal

/-- Before its first canonical opening packet, a genuine clear callback is
still in the original protected inclusion window. A later first callback
would contradict opportunity and the actual non-silent earlier response. -/
theorem phaseSourcePolicy_unsent_opening_protected
    (opportunity : PhaseService.Opportunity runtime leaks start horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol start horizon
      scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (owner : Player)
    (consistent : ∀ player, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      player).Consistent (current.execution.recall player))
    (event : (serviceGraph setup mode).EventId)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (P).outputs (current.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨current.execution.application.attempt, event⟩)
    (values : ∀ payload, (serviceGraph setup mode).outputLayout event = .publication payload →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    current.execution.application.current.native.publicView.InclusionFitsDeadline runtime bound
      event := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : inputs.map (PhaseRuntimeState.initial plan) = start := rfl
  have nested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some current) := initialEq.symm ▸ trace
  have raw := menu.toRawTrace start horizon scheduler trace
  have rawNested := menu.toRawTrace _ horizon scheduler nested
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler rawNested
  have owned := request.2.2.2.1
  have ready := request.2.2.1
  obtain ⟨entered, stamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor event ready
    (by simp only [owned, Option.isSome_some])
  by_cases clock : current.execution.application.current.native.clock ≤ entered + delay event
  · exact PublicView.inclusionFitsDeadline_of_response_delay runtime delay bound timely
      current.execution.application.current.native.publicView event entered
      (by simp only [owned, Option.isSome_some]) stamp clock
  have activated := opportunity current raw event owner entered owned
    ((current.execution.application.current.native.publicView_eventReady event).mpr ready) stamp
      (by omega)
  obtain ⟨activation, recorded, chosen, sameAttempt, wasReady, _wasStamp, earlyClock⟩ :=
    PhaseService.recorded_activation_within_delay runtime leaks start horizon scheduler delay
      opportunity current raw ⟨current.execution.application.attempt, event⟩ owner entered owned
        activated
  change activation.beforeView.application.native.clock ≤ entered + delay event at earlyClock
  rcases PhaseService.activation_response_or_current runtime leaks start horizon scheduler current
      raw activation recorded owner chosen with recalled | waiting
  · obtain ⟨response, retained, publicEq⟩ := recalled
    obtain ⟨before, prior, isPrefix, active, viewed, supported, _after, _word⟩ :=
      menu.recorded_response_supported start horizon scheduler current trace owner
        (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment owner)
          (consistent owner) response retained
    have beforePublic : before.execution.application.publicView =
        activation.beforeView.application :=
      (congrArg (fun view => view.application.2) viewed).symm.trans publicEq
    rw [← beforePublic] at sameAttempt wasReady
    change before.execution.application.attempt = current.execution.application.attempt
      at sameAttempt
    have beforeReady := (before.execution.application.current.native.publicView_eventReady
      event).mp wasReady
    have beforeNested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some before) := initialEq.symm ▸ prior
    have rawBefore := menu.toRawTrace _ horizon scheduler beforeNested
    have live := (phaseApplication_live runtime leaks).history _ horizon scheduler
      (fun initial member => by
        obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ member
        exact ⟨PhaseRuntimeState.initial_frontier plan draw,
          PhaseRuntimeState.initial_live plan draw⟩) rawBefore
    have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
      rawBefore
    have inside := before.execution.application.ready_current_phase
      (serviceGraph_revealRelaxedOrdered setup mode) live.1 live.2 geometry.2.2 event beforeReady
    have beforeRequest : before.execution.application.SeedRequest owner
        ⟨before.execution.application.attempt, event⟩ :=
      ⟨rfl, inside, beforeReady, owned, by
        have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu start horizon
          scheduler before current prior trace isPrefix clear).1
        simp only [beforeClear]; simp⟩
    obtain ⟨_beforeDraw, beforeValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs
      horizon scheduler rawBefore
    have publicRequest := (PhaseRuntimeState.requests_publicView before.execution.application
      beforeValid owner ⟨before.execution.application.attempt, event⟩).mpr beforeRequest
    rw [sameAttempt] at publicRequest
    have requested : PhaseRuntimeState.requests response.beforeView.application.2 owner
        ⟨current.execution.application.attempt, event⟩ := by
      rw [viewed]
      exact publicRequest
    have nonSilent := phaseSourcePolicy_no_silent_opening_recall setup mode runtime leaks bounds
      wellFormed source assessment copies plan maximal horizon scheduler trace clear consistent
        owner event publication unsent values response retained requested
    obtain ⟨material, transmitted⟩ := Option.isSome_iff_exists.mp nonSilent
    have responseEq : response.action = ⟨some material⟩ := by
      cases actionEq : response.action with
      | mk transmission =>
          rw [actionEq] at transmitted
          exact congrArg ReactiveApplication.Action.mk transmitted
    have offered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment
      owner _ _ response.action supported
    rw [responseEq] at offered
    have priorActing : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some ⟨before.remaining, some owner, before.execution⟩) := by
      cases before with
      | mk remaining actor execution =>
          change actor = some owner at active
          subst actor
          exact beforeNested
    have materialEvent := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining owner
        before.execution priorActing ⟨before.execution.application.attempt, event⟩ beforeRequest
          material offered
    let nativeEntry := PhaseNativeProjection.playerEntry runtime leaks plan response
    have nativeTransmitted : nativeEntry.action.transmission = some material := transmitted
    have nativePrior := PhaseNativeProjection.nativeTrace runtime leaks plan bounds
      (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler nested
        (fun _ same => by cases same; exact clear)
    have nativeRecorded : nativeEntry ∈
        (PhaseNativeProjection.execution runtime leaks plan current.execution).recall owner :=
      List.mem_map.mpr ⟨response, retained, rfl⟩
    obtain ⟨message, emitted, call⟩ :=
      (reactiveEmission_history runtime NL (inputs.map State.initial) horizon
        (PhaseNativeProjection.nativeScheduler runtime leaks plan scheduler)
        (PhaseNativeProjection.control runtime leaks plan current) nativePrior owner).2
          nativeEntry nativeRecorded material nativeTransmitted
    change response.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = some message
      at emitted
    obtain ⟨physical, physicalEmitted, projected⟩ := Option.map_eq_some_iff.mp emitted
    have physicalCall : physical.payload.packet.call = material.call.packet := by
      rw [← projected] at call
      exact call
    have attempt := phase_recalled_emission_attempt runtime leaks start horizon scheduler raw
      owner response retained physical physicalEmitted
    rw [viewed] at attempt
    change physical.payload.attempt = before.execution.application.attempt at attempt
    have named : PhaseCount.event? physical.payload =
        some ⟨current.execution.application.attempt, event⟩ := by
      simp only [PhaseCount.event?, physicalCall, materialEvent, Option.map_some]
      rw [attempt, sameAttempt]
    exact (unsent physical (List.mem_filterMap.mpr ⟨response, retained, physicalEmitted⟩)
      named).elim
  · have clocks := congrArg (fun view => view.native.clock) waiting.2
    change current.execution.application.current.native.clock =
      activation.beforeView.application.native.clock at clocks
    omega

end Vegas
