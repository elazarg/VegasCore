/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingPacketCallback
import Vegas.Game.PhaseBindingRecallConformance
import Vegas.Game.PhaseFreshCallSettlement
import Vegas.Pending.PhaseActivationResponse
import Vegas.Pending.ReactiveOwnerOpportunity
import Vegas.Pending.PhaseSolePacket

/-! # Canonical binding responses cannot remain ready at physical expiry -/

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
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)

private theorem recalled_binding_window
    (bounds : MessageBounds (serviceGraph setup mode))
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (current before : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (prior : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (clear : current.execution.application.current.excluded = ∅)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (entered : Nat)
    (stamp : current.execution.application.current.native.activatedAt event = some entered)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (timely : (R).AsyncTimely delay bound)
    (clock : current.execution.application.current.native.clock ≤ entered + delay event)
    (entry : (P).PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (viewed : entry.beforeView = before.execution.observe P owner)
    (beforeReady : before.execution.application.current.native.config.cut.Ready event) :
    before.execution.application.current.native.publicView.InclusionFitsDeadline R bound event := by
  have raw := (PhaseCount.onePacketMenu R leaks bounds).toRawTrace _ horizon scheduler trace
  have rawBefore := (PhaseCount.onePacketMenu R leaks bounds).toRawTrace _ horizon scheduler prior
  obtain ⟨draw, valid⟩ :=
    phaseNativeInvariant_history R leaks plan inputs horizon scheduler rawBefore
  obtain ⟨oldEntered, oldStamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor event beforeReady
    (by simp only [owned, Option.isSome_some])
  have nativePrior := PhaseNativeProjection.nativeTrace R leaks plan bounds ordered maximal inputs
    horizon scheduler trace (fun _ same => by cases same; exact clear)
  let nativeEntry := PhaseNativeProjection.playerEntry R leaks plan entry
  have nativeRecorded : nativeEntry ∈
      (PhaseNativeProjection.execution R leaks plan current.execution).recall owner :=
    List.mem_map.mpr ⟨entry, recorded, rfl⟩
  have oldView : nativeEntry.beforeView.application.publicView =
      before.execution.application.current.native.publicView := by
    change entry.beforeView.application.1.publicView = _
    rw [viewed]
    rfl
  obtain ⟨_extra, _order, _together, kept, _accepted⟩ :=
    (entryEventStable_history R NL (inputs.map State.initial) horizon
      (PhaseNativeProjection.nativeScheduler R leaks plan scheduler) nativePrior) owner
        nativeEntry nativeRecorded event
        (oldView.symm ▸
          (before.execution.application.current.native.publicView_eventReady event).mpr beforeReady)
        ready.1
  have remains := kept owner owned oldEntered (oldView.symm ▸ oldStamp)
  change current.execution.application.current.native.activatedAt event = some oldEntered at remains
  have same : oldEntered = entered := Option.some.inj (remains.symm.trans stamp)
  subst oldEntered
  have clocks := (P).recallBound_history
    (fun observed => observed.1.publicView.clock) (fun state => state.current.native.clock)
    (by intro state who; rfl)
    (fun lower => {
      submit := fun state who material bounded => bounded.trans
        ((phaseApplication_clock_monotone R leaks).submit state who material)
      handle := fun state message next bounded accepted => bounded.trans
        ((phaseApplication_clock_monotone R leaks).handle state message next accepted)
      environment := fun state command next bounded reached => bounded.trans
        ((phaseApplication_clock_monotone R leaks).environment state command next reached) })
    _ horizon scheduler current raw owner entry recorded
  rw [viewed] at clocks
  exact PublicView.inclusionFitsDeadline_of_response_delay R delay bound timely
    before.execution.application.current.native.publicView event entered
    (by simp only [owned, Option.isSome_some]) oldStamp (clocks.trans clock)

/-- Under the original physical opportunity/inclusion contract, a canonical
continuing source binding cannot still be ready at its actual deadline. The
proof recovers its real earliest packet, even if that packet precedes the
within-delay callback selected by opportunity. -/
theorem phase_due_binding_impossible
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
      ∀ choice ∈ (assessment.strategy who site.1).support,
        setup.CommitRecoveryContinues who site.1 choice.1)
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (P).Scheduler) (capacity : horizon ≤ bounds.candidateCount)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : PhaseService.Opportunity R leaks start horizon scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion R leaks start horizon scheduler bound)
    (timely : (R).AsyncTimely delay bound)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅) (idle : current.actor = none)
    (owner : Player)
    (consistent : (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent
      (current.execution.recall owner))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (entered : Nat)
    (stamp : current.execution.application.current.native.activatedAt event = some entered)
    (due : deadline event ≤ current.execution.application.current.native.clock - entered) :
    False := by
  classical
  let menu := PhaseCount.onePacketMenu R leaks bounds
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : inputs.map (PhaseRuntimeState.initial plan) = start := by
    simp only [inputs, PMF.map_comp, Function.comp_def]
  have nested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace
      (some current) := initialEq.symm ▸ trace
  have raw := menu.toRawTrace start horizon scheduler trace
  have owned := EventGraph.actor?_of_outputLayout_binding (serviceGraph setup mode) binding
  obtain ⟨response, recorded, attempt, wasReady, wasStamp, clock⟩ :=
    PhaseService.due_recalled_response R leaks start horizon scheduler delay bound opportunity
      timely current raw idle event owner entered owned ready stamp due
  obtain ⟨before, prior, retained, active, viewed, supported, after, recalled⟩ :=
    menu.recorded_response_supported start horizon scheduler current trace owner
      (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment owner) consistent response
        recorded
  have beforeClear := (phase_clear_nativeProgress_of_prefix R leaks menu start horizon scheduler
    before current prior trace retained clear).1
  rw [viewed] at attempt wasReady wasStamp clock
  change before.execution.application.attempt = current.execution.application.attempt at attempt
  change before.execution.application.current.native.publicView.EventReady event at wasReady
  change before.execution.application.current.native.activatedAt event = some entered at wasStamp
  change before.execution.application.current.native.clock ≤ entered + delay event at clock
  have beforeReady := (before.execution.application.current.native.publicView_eventReady event).mp
    wasReady
  have beforeNested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before) := initialEq.symm ▸ prior
  have rawBefore := menu.toRawTrace _ horizon scheduler beforeNested
  have live := (phaseApplication_live R leaks).history _ horizon scheduler
    (fun initial supported => by
      obtain ⟨draw, _support, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩)
    rawBefore
  have geometry := phasePlanGeometry_history R leaks plan maximal inputs horizon scheduler rawBefore
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
    · obtain ⟨serial, result, _bounded, responseEq⟩ := phaseSourcePolicy_binding_emits_of_continuing
        setup mode R leaks bounds wellFormed assessment continuing plan maximal horizon scheduler
          capacity before prior owner active event payload binding request unsent values beforeClear
            response.action supported
      have fitting := PublicView.inclusionFitsDeadline_of_response_delay R delay bound timely
        before.execution.application.current.native.publicView event entered
        (by simp only [owned, Option.isSome_some]) wasStamp clock
      have permitted := phaseSourcePolicy_covered setup mode R leaks bounds wellFormed assessment
        owner _ _ response.action supported
      obtain ⟨message, call⟩ :=
        phase_recalled_binding_freshCall setup mode deadline leaks plan bounds
        ordered maximal inputs horizon scheduler current before nested beforeNested clear owner
          response recorded viewed event payload binding request bound fitting result serial
            responseEq
            permitted
      exact ⟨_, message, List.mem_map.mpr ⟨response, recorded, rfl⟩, call⟩
    · push Not at unsent
      obtain ⟨packet, output, named⟩ := unsent
      have beforeConsistent : (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
          owner).Consistent (before.execution.recall owner) :=
        ReactiveApplication.Policy.Consistent.of_append (recalled ▸ consistent)
      obtain ⟨entry, first, firstTrace, member, emitted, isPrefix, acting, _firstAttempt,
        firstRequest,
        firstViewed, permitted, ⟨serial, result, responseEq⟩, _suffix, _word⟩ :=
          phase_binding_packet_callback setup mode R leaks bounds wellFormed assessment continuing
            plan maximal ordered horizon scheduler capacity before prior beforeClear owner
              beforeConsistent event payload binding values packet output named
      have firstNested : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
          scheduler).Trace (some first) := initialEq.symm ▸ firstTrace
      have fitting := recalled_binding_window setup mode deadline leaks plan bounds ordered maximal
        inputs horizon scheduler before first beforeNested firstNested beforeClear owner event owned
          beforeReady entered wasStamp delay bound timely clock entry member firstViewed
            firstRequest.2.2.1
      have finalMember : entry ∈ current.execution.recall owner := by
        rw [recalled]
        exact List.mem_append_left _ member
      obtain ⟨message, call⟩ :=
        phase_recalled_binding_freshCall setup mode deadline leaks plan bounds
        ordered maximal inputs horizon scheduler current first nested firstNested clear owner entry
          finalMember firstViewed event payload binding firstRequest bound fitting result serial
            responseEq permitted
      exact ⟨_, message, List.mem_map.mpr ⟨entry, finalMember, rfl⟩, call⟩
  obtain ⟨entry, message, member, call⟩ := chosenCall
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
  have sole := PhaseNativeProjection.recall_sole_of_clear R leaks plan bounds inputs horizon
    scheduler nested clear owner earlier later entry message split call.emitted event call.addressed
  have physicalInclusion : PhaseService.ProtectedInclusion R leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler bound :=
    initialEq.symm ▸ inclusion
  have within := phase_freshCall_within_deadline_of_ready setup mode deadline leaks plan bounds
    ordered maximal horizon scheduler current nested clear owner event owned bound physicalInclusion
      earlier later entry message split call sole ready
  simp only [State.WithinDeadline, stamp] at within
  change current.execution.application.current.native.clock - entered < deadline event at within
  omega

end Vegas
