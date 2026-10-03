/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingFirstPacket
import Vegas.Game.SourceServiceLateDecisionCompletion
import Vegas.Game.SourceServiceCompatibleImmediateAudit
import Vegas.Game.SourceServiceResidualSites
import Vegas.Game.SourceServiceProtectedDecisionLaw

/-! # Actual protected canonical decisions through completion

One initialized unrecorded input emits its actual acceptable canonical packet.
The owner is silent afterward, while foreign raw policies remain arbitrary.
Protected inclusion supplies the receipt for that same identifier and excludes
expiry; the actual completed configuration makes the selected effective step.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Protected completion of the actual canonical packet, with its exact
accepting identifier and selected graph step. No source draw or endpoint is
assumed; effectiveness is the operational meaning of the supplied action. -/
theorem sourceServiceCanonicalDecision_protected_completion
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (owner : Player) (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (action : (graph setup).Action event)
    (effective : EffectiveAction execution.application.config event action)
    (players : Player → (application setup leaks).Policy)
    (follows : players owner = (application setup leaks).silentPolicy)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution.respond (application setup leaks) owner
        ((runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) event action))).support) :
    event ∈ stopped.application.config.cut.completed ∧
      ((owner, execution.network.nextSerial owner), true) ∈ stopped.receipts ∧
      event ∉ stopped.application.missedEvents ∧
      stopped.application.config ∈ (execution.application.config.step event ready action).support :=
    by
  let app := application setup leaks
  let response := (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
    (execution.observe app owner) event action
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have accounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler trace
  change execution.environmentRecall.length + remaining = horizon at accounted
  obtain ⟨entered, activated⟩ : ∃ entered,
      execution.application.activatedAt event = some entered := by
    cases activated : execution.application.activatedAt event with
    | none => simp only [PublicView.InclusionFitsDeadline, State.publicView, activated] at fits
    | some entered => exact ⟨entered, rfl⟩
  let localDelay : (graph setup).EventId → Nat := fun other =>
    if other = event then execution.application.clock - entered else 0
  let localBound : (graph setup).EventId → Nat := fun other =>
    if other = event then bound event else 0
  have localTimely : AsyncTimely (runtime setup) localDelay localBound := by
    intro other _owned
    by_cases same : other = event
    · subst other
      simpa only [localDelay, localBound, ↓reduceIte, PublicView.InclusionFitsDeadline,
        State.publicView, activated] using fits
    · simp only [localDelay, localBound, same, ↓reduceIte, Nat.zero_add]
      exact runtime_deadline_pos setup other
  obtain ⟨material, responseEq, localCall, _realized⟩ := firstTurn_freshCall localTimely trace
    event owned ready entered activated (by simp only [localDelay, ↓reduceIte]; omega)
      action effective
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, execution.network.nextSerial owner), app.packet
      (app.submit execution.application owner material) owner (execution.network.known owner)
        material⟩
  let entry : app.PlayerEntry := ⟨execution.observe app owner, response, some message⟩
  let start := execution.respond app owner response
  have call : FreshCall setup leaks owner event bound entry message := {
    fresh := localCall.fresh
    emitted := localCall.emitted
    authored := localCall.authored
    addressed := localCall.addressed
    ready := localCall.ready
    fits := fits
    conforming := localCall.conforming }
  have noPacket := sourceService_unrecorded_event_packets setup leaks execution owner event
    facts.provenance unrecorded
  let safe := fun packet : Message Player (WitnessedPacket (graph setup)) =>
    packet.sender = owner → packet.payload.call.event? (graph setup) = some event → packet = message
  have packets : start.network.Satisfies safe := by
    have prior : execution.network.Satisfies safe := noPacket.mono
      (fun packet absent authored named => (absent authored named).elim)
    change response = ⟨some material⟩ at responseEq
    change (execution.respond app owner response).network.Satisfies safe
    rw [responseEq]
    change (execution.network.submit owner _).2.Satisfies safe
    apply prior.submit owner
    intro _author _named
    rfl
  have recalled : start.recall owner = execution.recall owner ++ [entry] := by
    change (execution.respond app owner response).recall owner = _
    change response = ⟨some material⟩ at responseEq
    simpa only [entry, message, responseEq, app] using
      respond_submit_recall execution owner material
  obtain ⟨startTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler remaining
    execution owner response trace
  obtain ⟨used, budget, rounds, _length⟩ := app.runUntil_runRounds scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - start.environmentRecall.length) start stopped reached
  have startLength : start.environmentRecall.length = execution.environmentRecall.length :=
    congrArg List.length (app.respond_environmentRecall execution owner response)
  have within : used ≤ remaining := by omega
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
    (remaining - used) used start stopped
    (by simpa only [Nat.sub_add_cancel within] using startTrace) rounds
  have silentRounds : stopped ∈ (app.runRounds scheduler
      (Function.update players owner app.silentPolicy) used start).support := by
    have equal : Function.update players owner app.silentPolicy = players := by
      rw [← follows, Function.update_eq_self]
    rwa [equal]
  have sole := (sourceService_silent_owner_packets app players owner safe
    (fun packet foreign authored _named => (foreign authored).elim)).runRounds scheduler used
      start stopped packets silentRounds
  have retained : app.PolicyInvariant players (fun current => start.recall owner <+:
      current.recall owner) := {
    respond := fun current actor chosen holds _ =>
      holds.trans (app.respond_recall_prefix current actor owner chosen)
    environment := fun current next command holds moved => by
      rw [app.environmentStep_recall current next command moved]
      exact holds }
  obtain ⟨later, prefixEq⟩ := retained.runRounds scheduler used start stopped (by rfl) rounds
  have split : stopped.recall owner = execution.recall owner ++ entry :: later := by
    rw [← prefixEq, recalled, List.append_assoc]
    rfl
  have finalFacts := legalFacts setup leaks horizon scheduler _ finalTrace
  have excludes : ∀ other ∈ execution.recall owner ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
    intro other member ⟨packet, emitted, authored, named, different⟩
    have memberFinal : other ∈ stopped.recall owner := by
      rw [split]
      rcases List.mem_append.mp member with earlier | after
      · exact List.mem_append_left _ earlier
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    have output : packet ∈ app.outputs (stopped.recall owner) :=
      List.mem_filterMap.mpr ⟨other, memberFinal, emitted⟩
    rw [← finalFacts.inputs owner] at output
    have equal := sole.inputs packet (List.mem_filter.mp output).1 authored named
    exact different (congrArg Message.id equal)
  have settled := settlesFreshCalls_history setup leaks contract.inclusion owner event owned
    finalTrace (execution.recall owner) entry later message split call excludes
  have actual := sourceServiceCanonicalDecision_include_or_miss contract owner execution trace
    event owned ready fits.withinDeadline unrecorded action effective players follows stopped
      reached
  refine ⟨actual.1, settled.1 actual.1, settled.2.2.2, ?_⟩
  exact actual.2.resolve_left settled.2.2.2

end Vegas

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.menu (runtime service.setup) service.leaks

omit [Fintype Player] in
private theorem immediate_input_of_recorded
    (profile : BehavioralProfile service.setup.program)
    (execution : (app).Execution) (who : Player) (event : (graph service.setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph service.setup).actor? event = some who)
    (recorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall who) event = true) :
    sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        (execution.recall who) (execution.observe (app) who) =
      (app).silentPolicy (execution.recall who) (execution.observe (app) who) := by
  have turn := ownTurn?_of_ready service.setup execution.application ready owned
  change (execution.observe (app) who).application.publicView.ownTurn? who = some event at turn
  unfold sourceServiceImmediatePolicy
  split
  · simp only [turn, sourceServiceCanonicalOpportunity, recorded, ↓reduceIte]
  · rfl

/-- A real immediate draw at compatible full-menu information is accepted with
its original packet identifier and makes its selected typed graph successor.
The actual source residual and owner resources are derived from the legal
prefix. Foreign prefix and suffix policies need not be source-supported. -/
theorem sourceCompatibleInfo_immediate_protected_completion
    (profile : BehavioralProfile service.setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    {remaining : Nat} (execution : (app).Execution) (who : Player)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (event : (graph service.setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall who) event = false)
    (response : (app).Action)
    (chosen : response ∈ (sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who (execution.recall who) (execution.observe (app) who)).support)
    (players : Player → (app).Policy)
    (follows : players who = sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who)
    (stopped : (app).Execution)
    (reached : stopped ∈ ((app).runUntilHorizon service.scheduler players
      (fun final => event ∈ final.application.config.cut.completed) service.horizon
      (execution.respond (app) who response)).support) :
    ∃ action : (graph service.setup).Action event,
      response = (runtime service.setup).canonicalServiceDecision service.leaks who
        (execution.recall who) (execution.observe (app) who) event action ∧
      EffectiveAction execution.application.config event action ∧
      event ∈ stopped.application.config.cut.completed ∧
      ((who, execution.network.nextSerial who), true) ∈ stopped.receipts ∧
      event ∉ stopped.application.missedEvents ∧
      stopped.application.config ∈ (execution.application.config.step event
        ((execution.application.publicView_eventReady event).mp
          (PublicView.ownTurn?_spec _ who event turn).1) action).support := by
  have rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    trace
  obtain ⟨clear, atTurn, slots, _calls, _conform, _once, _good⟩ :=
    service.sourceCompatibleInfo_raw_prefixFacts ⟨remaining, some who, execution⟩ rawTrace who
      compatible
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have fits := (runtime service.setup).serviceRisk_clear_protected_opportunity service.leaks
    service.bound who (execution.recall who) (execution.observe (app) who) event rfl turn
      unrecorded clear
  obtain ⟨residual⟩ := menu_ready_sourceResidual service.setup service.leaks profile (menu)
    service.horizon service.scheduler trace ⟨remaining, some who, execution⟩ rfl event ready
  obtain ⟨law, _prefixLaw, canonical, operational⟩ := SourceResidual.head_step service.leaks
    residual event rfl ready
  have actualChosen := chosen
  rw [sourceServiceImmediatePolicy_at_event clear turn,
    sourceServiceCanonicalOpportunity_protected service.bound profile who event
      (execution.recall who) (execution.observe (app) who) unrecorded fits,
    canonical who owned execution rfl, PMF.support_map] at chosen
  obtain ⟨action, selected, rfl⟩ := chosen
  have effectiveAction := operational effective action selected
  let response := (runtime service.setup).canonicalServiceDecision service.leaks who
    (execution.recall who) (execution.observe (app) who) event action
  let start := execution.respond (app) who response
  obtain ⟨_material, _responseEq, _freshCall, recorded⟩ := sourceServiceImmediatePolicy_call
    rawTrace atTurn slots clear event turn unrecorded response actualChosen
  have afterReady : start.application.config.cut.Ready event := by
    rw [((runtime service.setup).reactive_respond_application service.leaks execution who
      response).1]
    exact ready
  have stoppedLaw :
      (app).runUntilHorizon service.scheduler players
        (fun final => event ∈ final.application.config.cut.completed) service.horizon start =
      (app).runUntilHorizon service.scheduler (Function.update players who (app).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) service.horizon start := by
    unfold ReactiveApplication.runUntilHorizon
    apply sourceServicePolicy_runUntil_owner_silent service.setup service.leaks service.scheduler
      players who _ start event afterReady recorded
    intro current currentReady currentRecorded
    rw [follows]
    exact service.immediate_input_of_recorded profile current who event currentReady owned
      currentRecorded
  have actual := sourceServiceCanonicalDecision_protected_completion service.contract who
    execution rawTrace event owned ready unrecorded fits action effectiveAction
    (Function.update players who (app).silentPolicy) (Function.update_self ..) stopped
      (stoppedLaw ▸ reached)
  exact ⟨action, rfl, effectiveAction, actual⟩

end Vegas.AsyncServiceSpec
