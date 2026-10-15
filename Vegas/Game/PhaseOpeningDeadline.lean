/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseOpeningRecallConformance
import Vegas.Game.PhaseBindingDeadline
import Vegas.Pending.PhasePacketCallback

/-! # Actual copied openings cannot remain ready at physical expiry -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "R" => serviceRuntime setup mode deadline
local notation "P" => phaseApplication R leaks
local notation "NL" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "N" => serviceApplication setup mode deadline NL
local notation "I" => setup.initialLaw.map encodeInputs
local notation "start" =>
  PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs)

/-- Original physical service and actual copied source play exclude a due
ready opening. The retained packet may precede the timely callback; its real
supported first callback, original guarded success and emission window are
recovered from that same full history. -/
theorem phase_due_opening_impossible
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (P).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : PhaseService.Opportunity R leaks start horizon scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion R leaks start horizon scheduler bound)
    (timely : (R).AsyncTimely delay bound)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅) (idle : current.actor = none)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner))
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (values : ∀ payload, (serviceGraph setup mode).outputLayout event = .publication payload →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (entered : Nat)
    (stamp : current.execution.application.current.native.activatedAt event = some entered)
    (due : deadline event ≤ current.execution.application.current.native.clock - entered) :
    False := by
  classical
  let menu := PhaseCount.onePacketMenu R leaks bounds
  have raw := menu.toRawTrace start horizon scheduler trace
  obtain ⟨response, recorded, attempt, wasReady, wasStamp, clock⟩ :=
    PhaseService.due_recalled_response R leaks start horizon scheduler delay bound opportunity
      timely current raw idle event owner entered owned ready stamp due
  obtain ⟨before, prior, retained, active, viewed, supported, after, recalled⟩ :=
    menu.recorded_response_supported start horizon scheduler current trace owner
      (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment owner) (consistent owner)
        response recorded
  have beforeClear := (phase_clear_nativeProgress_of_prefix R leaks menu start horizon scheduler
    before current prior trace retained clear).1
  rw [viewed] at attempt wasReady wasStamp clock
  change before.execution.application.attempt = current.execution.application.attempt at attempt
  change before.execution.application.current.native.publicView.EventReady event at wasReady
  change before.execution.application.current.native.activatedAt event = some entered at wasStamp
  change before.execution.application.current.native.clock ≤ entered + delay event at clock
  have beforeReady := (before.execution.application.current.native.publicView_eventReady event).mp
    wasReady
  have rawBefore := menu.toRawTrace start horizon scheduler prior
  have live := (phaseApplication_live R leaks).history start horizon scheduler
    (fun initial supported => by
      obtain ⟨draw, _support, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩) rawBefore
  have geometry := phasePlanGeometry_history R leaks plan maximal I horizon scheduler rawBefore
  have inside := before.execution.application.ready_current_phase ordered live.1 live.2 geometry.2.2
    event beforeReady
  have request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩ :=
    ⟨rfl, inside, beforeReady, owned, by simp only [beforeClear]; simp⟩
  have chosenCall : ∃ (entry : (N).PlayerEntry) (message : Message Player (WitnessedPacket
      (serviceGraph setup mode))),
      entry ∈ (PhaseNativeProjection.execution R leaks plan current.execution).recall owner ∧
      FreshCall setup NL owner event bound entry message := by
    by_cases unsent : ∀ message ∈ (P).outputs (before.execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩
    · have fitting := PublicView.inclusionFitsDeadline_of_response_delay R delay bound timely
        before.execution.application.current.native.publicView event entered
        (by simp only [owned, Option.isSome_some]) wasStamp clock
      obtain ⟨message, call⟩ := phase_recalled_opening_freshCall setup mode deadline leaks source
        bounds wellFormed assessment copies plan maximal horizon scheduler trace prior retained
          clear consistent owner response recorded viewed event publication request unsent supported
            bound fitting values
      exact ⟨_, message, List.mem_map.mpr ⟨response, recorded, rfl⟩, call⟩
    · push Not at unsent
      obtain ⟨packet, output, named⟩ := unsent
      have beforeConsistent : (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
          owner).Consistent (before.execution.recall owner) :=
        ReactiveApplication.Policy.Consistent.of_append (recalled ▸ consistent owner)
      obtain ⟨entry, first, firstTrace, _material, member, emitted, isPrefix, acting, firstRequest,
        firstViewed, _transmitted, _named, _permitted, chosen, firstUnsent, _suffix, _word⟩ :=
          PhaseNativeProjection.packet_callback R leaks plan bounds ordered maximal I horizon
            scheduler before prior beforeClear owner
              (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment owner)
                beforeConsistent ⟨before.execution.application.attempt, event⟩ packet output named
      have firstAttempt : first.execution.application.attempt =
          before.execution.application.attempt := firstRequest.1.symm
      have actualRequest : first.execution.application.SeedRequest owner
          ⟨first.execution.application.attempt, event⟩ := by
        rw [firstAttempt]
        exact firstRequest
      have actualUnsent : ∀ packet ∈ (P).outputs (first.execution.recall owner),
          PhaseCount.event? packet.payload ≠ some ⟨first.execution.application.attempt, event⟩ := by
        rw [firstAttempt]
        exact firstUnsent
      have fitting := phase_recalled_inclusion_window setup mode deadline leaks plan bounds ordered
        maximal I horizon scheduler before first prior firstTrace beforeClear owner event owned
          beforeReady entered wasStamp delay bound timely clock entry member firstViewed
            actualRequest.2.2.1
      have finalMember : entry ∈ current.execution.recall owner := by
        rw [recalled]
        exact List.mem_append_left _ member
      obtain ⟨message, call⟩ := phase_recalled_opening_freshCall setup mode deadline leaks source
        bounds wellFormed assessment copies plan maximal horizon scheduler trace firstTrace
          (isPrefix.trans retained) clear consistent owner entry finalMember firstViewed event
            publication actualRequest actualUnsent chosen bound fitting values
      exact ⟨_, message, List.mem_map.mpr ⟨entry, finalMember, rfl⟩, call⟩
  obtain ⟨entry, message, member, call⟩ := chosenCall
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
  have sole := PhaseNativeProjection.recall_sole_of_clear R leaks plan bounds I horizon scheduler
    trace clear owner earlier later entry message split call.emitted event call.addressed
  have within := phase_freshCall_within_deadline_of_ready setup mode deadline leaks plan bounds
    ordered maximal horizon scheduler current trace clear owner event owned bound inclusion earlier
      later entry message split call sole ready
  simp only [State.WithinDeadline, stamp] at within
  change current.execution.application.current.native.clock - entered < deadline event at within
  omega

end Vegas
