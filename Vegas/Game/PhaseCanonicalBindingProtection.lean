/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingDeadline
import Vegas.Pending.PhaseActivationResponse
import Vegas.Pending.PhaseAttemptCheckpoint

/-! # Original opportunity protects every canonical unsent binding callback -/

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
  (continuing : ∀ owner (site : setup.commitRecoveryModel.InformationSite owner),
    ∀ choice ∈ (assessment.strategy owner site.1).support,
      setup.CommitRecoveryContinues owner site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (delay bound : (serviceGraph setup mode).EventId → Nat)

local notation "P" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "NL" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "N" => runtime.reactiveApplication NL

include continuing maximal capacity

/-- Before its first canonical binding packet, a genuine clear callback is
still in the original protected inclusion window. A later first callback
would contradict opportunity and the actual non-silent earlier response. -/
theorem phaseSourcePolicy_unsent_binding_protected
    (opportunity : PhaseService.Opportunity runtime leaks start horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol start horizon
      scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (owner : Player)
    (consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (P).outputs (current.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨current.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    current.execution.application.current.native.publicView.InclusionFitsDeadline runtime bound
      event := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : inputs.map (PhaseRuntimeState.initial plan) = start := by
    exact PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
  have nested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some current) := initialEq.symm ▸ trace
  have raw := menu.toRawTrace start horizon scheduler trace
  have rawNested := menu.toRawTrace _ horizon scheduler nested
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler rawNested
  have owned := EventGraph.actor?_of_outputLayout_binding (serviceGraph setup mode) binding
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
    obtain ⟨before, prior, isPrefix, active, viewed, supported, _after, word⟩ :=
      menu.recorded_response_supported start horizon scheduler current trace owner
        (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment owner)
          consistent response retained
    have beforePublic : before.execution.application.publicView =
        activation.beforeView.application :=
      (congrArg (fun view => view.application.2) viewed).symm.trans publicEq
    rw [← beforePublic] at sameAttempt wasReady
    change before.execution.application.attempt = current.execution.application.attempt
      at sameAttempt
    have beforeReady := (before.execution.application.current.native.publicView_eventReady
      event).mp wasReady
    have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu start horizon
      scheduler before current prior trace isPrefix clear).1
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
      ⟨rfl, inside, beforeReady, owned, by simp only [beforeClear]; simp⟩
    have beforeUnsent : ∀ message ∈ (P).outputs (before.execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩ := by
      intro message member named
      apply unsent message
        (by rw [word, ReactiveApplication.outputs, List.filterMap_append]
            exact List.mem_append_left _ member)
      rw [← sameAttempt]
      exact named
    obtain ⟨serial, result, _bounded, responseEq⟩ :=
      phaseSourcePolicy_binding_emits_of_continuing setup mode runtime leaks bounds wellFormed
        assessment continuing plan maximal horizon scheduler capacity before prior owner active
          event payload binding beforeRequest beforeUnsent values beforeClear response.action
            supported
    let nativeEntry := PhaseNativeProjection.playerEntry runtime leaks plan response
    let material : WitnessedSubmission (serviceGraph setup mode) :=
      ⟨⟨.commitment event (owner, .prepared serial), match result with
        | .failure => none
        | .success value => some ⟨payload, value⟩⟩, .none⟩
    have transmitted : nativeEntry.action.transmission = some material := by
      change response.action.transmission = some material
      rw [responseEq]
      cases result <;> rfl
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
          nativeEntry nativeRecorded material transmitted
    change response.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = some message
      at emitted
    obtain ⟨physical, physicalEmitted, projected⟩ := Option.map_eq_some_iff.mp emitted
    have physicalCall : physical.payload.packet.call =
        .commitment event (owner, .prepared serial) := by
      rw [← projected] at call
      exact call
    have attempt := phase_recalled_emission_attempt runtime leaks start horizon scheduler raw
      owner response retained physical physicalEmitted
    rw [viewed] at attempt
    change physical.payload.attempt = before.execution.application.attempt at attempt
    have named : PhaseCount.event? physical.payload =
        some ⟨current.execution.application.attempt, event⟩ := by
      simp only [PhaseCount.event?, physicalCall, Payload.event?, Option.map_some]
      rw [attempt, sameAttempt]
    exact (unsent physical (List.mem_filterMap.mpr ⟨response, retained, physicalEmitted⟩)
      named).elim
  · have clocks := congrArg (fun view => view.native.clock) waiting.2
    change current.execution.application.current.native.clock =
      activation.beforeView.application.native.clock at clocks
    omega

end Vegas
