/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixSupport

/-! # Public audit soundness for the full source service

Every retained source behavior produces permitted authentic traffic. The proof
uses the operational boundary at each event and the actual sampled responses;
the checker does not compare a run with a selected equilibrium profile. Records
keep the public phase and ledger at transmission, including after settlement.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
  {Γ : SourceCtx Player L} {source : Config Player L Γ}
  {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
  {execution : (application setup leaks).Execution}

/-- Chance windows admit only silence and transport, so their actual records
remain permitted under arbitrary passive observation and repeated visits. -/
theorem sourceService_sample_window_conformance
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (chance : (graph setup).actor? event = none)
    (sole : execution.application.publicView.SoleReady event)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (traffic : ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true)
    (visits : List Player) (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) execution).support) :
    current.network.Satisfies (fun message => (runtime setup).permittedServiceEnvelope
      current.application.publicView current.network.ledger message = true) ∧
    (∀ record ∈ (application setup leaks).executionTraffic current,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true) := by
  let app := application setup leaks
  induction visits using List.reverseRecOn generalizing current with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨(runtime setup).service_published_conformance leaks execution published, traffic⟩
  | append_singleton visits actor ih =>
      rw [List.map_append, (runtime setup).runInteractionPlan_append] at reached
      obtain ⟨before, reachedBefore, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have prior := ih before reachedBefore
      have same := (sourceService_sample_window setup leaks bounds rosters players lawful network
        event chance execution before sole published visits reachedBefore).1
      simp only [List.map_cons, List.map_nil, runInteractionPlan, PMF.bind_pure,
        interactionStep, interactionInstruction, PMF.pure_bind] at reached
      change current ∈ ((before.environmentStep app (.activate actor)).bind
        (app.invoke players actor)).support at reached
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at reached
      obtain ⟨sample, selected, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ reached
      let activated := before.sampledActivation app actor sample
      have activation : activated ∈ (before.environmentStep app (.activate actor)).support := by
        rw [ReactiveApplication.Execution.activation_samples]
        exact PMF.support_map .. ▸ ⟨sample, selected, rfl⟩
      have sampled := (runtime setup).service_sampled_conformance leaks before actor sample prior.1
      have member := sourceServiceMenu_in_compiled setup leaks bounds rosters actor
        (activated.recall actor) (activated.observe app actor) (lawful actor _ _ response chosen)
      have issued := bounds.compiled_foreign_traffic (runtime setup) leaks activated 0 actor
        (by
          change before.application.publicView.Idle actor
          rw [same]
          exact sole.idle (by rw [chance]; simp))
        response member
      refine ⟨(runtime setup).service_response_conformance leaks activated 0 actor response
        sampled issued, ?_⟩
      intro record included
      rw [app.executionTraffic_activated_response before activated actor response 0 activation,
        List.mem_append] at included
      exact included.elim (prior.2 record) (issued record)

/-- A complete binding phase retains the checker verdict of every record,
including transmissions before inclusion. -/
theorem ServiceBoundary.binding_block_conformance
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (traffic : ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∀ record ∈ (application setup leaks).executionTraffic final,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true := by
  rw [rosterBlock_of_owner setup rosters event owner owned] at reached
  simp only [List.append_assoc] at reached
  rw [(runtime setup).runInteractionPlan_append] at reached
  obtain ⟨visited, window, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have visitedTraffic := (boundary.binding_prefix_conformance bounds players lawful network
    event atRank owner payload outputEq codeEq node owned
      traffic (rosters event) visited window).2
  have exactTraffic := (runtime setup).executionTraffic_passive_plan leaks players network
    ([.includeLatest event owner] ++ List.replicate (event.val + 1) .tick ++ [.expire event])
    (by
      intro instruction member
      simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at member
      rcases member with (rfl | ⟨_, rfl⟩) | rfl <;> simp)
    visited final (by simpa only [List.append_assoc] using tail)
  rw [exactTraffic]
  exact visitedTraffic

/-- Public sampling and settlement issue no player traffic; the chance roster
can only carry records already permitted by the public checker. -/
theorem ServiceBoundary.sample_block_conformance
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (chance : (graph setup).actor? event = none)
    (traffic : ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∀ record ∈ (application setup leaks).executionTraffic final,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true := by
  simp only [rosterBlock, chance, List.append_assoc] at reached
  rw [(runtime setup).runInteractionPlan_append] at reached
  obtain ⟨visited, window, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have visitedTraffic := (sourceService_sample_window_conformance bounds players lawful network
    event chance (soleReady_of_ready setup execution.application (boundary.ready event atRank))
    boundary.published traffic
      (rosters event) visited window).2
  have exactTraffic := (runtime setup).executionTraffic_passive_plan leaks players network
    ([.sample event] ++ List.replicate (event.val + 1) .tick ++ [.expire event])
    (by
      intro instruction member
      simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at member
      rcases member with (rfl | ⟨_, rfl⟩) | rfl <;> simp)
    visited final (by simpa only [List.append_assoc] using tail)
  rw [exactTraffic]
  exact visitedTraffic

/-- Soundness of the public traffic checker for every event kind. Its premises
are the actual source boundary and menu membership, independently of utilities. -/
theorem ServiceBoundary.roster_block_conformance
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (traffic : ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∀ record ∈ (application setup leaks).executionTraffic final,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true := by
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have chance : (graph setup).actor? event = none := by
        have actor := congrArg EventGraph.EventCode.actor codeEq
        rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
        exact actor
      exact boundary.sample_block_conformance bounds players lawful network event atRank chance
        traffic final reached
  | bind owner payload outputEq codeEq =>
      have owned : (graph setup).actor? event = some owner := by
        have actor := congrArg EventGraph.EventCode.actor codeEq
        rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
        exact actor
      exact boundary.binding_block_conformance bounds players lawful network event atRank
        owner payload outputEq codeEq node owned traffic final reached
  | resolve owner payload binding checks outputEq codeEq =>
      have owned : (graph setup).actor? event = some owner := by
        have actor := congrArg EventGraph.EventCode.actor codeEq
        rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
        exact actor
      exact boundary.reveal_block_conformance bounds players lawful network event atRank
        owner payload binding checks outputEq codeEq node owned traffic final reached

/-- Every initialized retained prefix passes the traffic checker. The actual
policies are arbitrary laws supported by the entire retained menu. -/
theorem initialized_sourceService_prefix_conformance
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (opportunities : ActorOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (count : Nat) (within : count ≤ eventCount setup.program)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∀ record ∈ (application setup leaks).executionTraffic final,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true := by
  induction count generalizing final with
  | zero =>
      simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, runInteractionPlan] at reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      simp [ReactiveApplication.executionTraffic, ReactiveApplication.Execution.initial,
        ReactiveApplication.trafficViews]
  | succ count ih =>
      let event : (graph setup).EventId := ⟨count, by exact Nat.lt_of_succ_le within⟩
      rw [rosterPlanPrefix_succ setup rosters event] at reached
      simp only [(runtime setup).runInteractionPlan_append, ← PMF.bind_bind] at reached
      obtain ⟨before, prior, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have traffic := ih (by omega) before prior
      obtain ⟨_, _, _, _, _, Δ, names, remaining, remainingProfile, current, currentRefs,
          embedding, refsBefore, _, _, _, _, _, _, _, _, boundary⟩ :=
        initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
          opportunities players lawful network (failureProfile setup.program) count (by omega)
          before prior
      exact boundary.roster_block_conformance bounds players lawful network event rfl
        traffic final rest

/-- A complete retained execution produces no rejected traffic evidence.
Public chance, fresh bindings and arbitrary guarded disclosures are included. -/
theorem initialized_sourceService_conformance
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (opportunities : ActorOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network (rosterPlan setup rosters)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∀ record ∈ (application setup leaks).executionTraffic final,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.envelope = true := by
  apply initialized_sourceService_prefix_conformance bounds values capacity opportunities players
    lawful network (eventCount setup.program) le_rfl final
  have complete : rosterPlanPrefix setup rosters (eventCount setup.program) =
      rosterPlan setup rosters := by
    unfold rosterPlanPrefix rosterPlan
    rw [List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)]
  simpa only [complete] using reached

end Vegas
