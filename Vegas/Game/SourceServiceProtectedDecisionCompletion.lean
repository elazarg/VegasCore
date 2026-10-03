/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingFirstPacket
import Vegas.Game.SourceServiceLateDecisionCompletion

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
