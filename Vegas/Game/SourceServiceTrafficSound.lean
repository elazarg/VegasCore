/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceConformance
import Vegas.Game.ServiceRosterClock
import Vegas.Game.RevealServiceSignedTraffic

/-! # Authentic partial audits accept every retained source history

The complete-execution conformance theorem also covers intermediate protocol
histories. Every permitted finite prefix extends to a complete permitted run,
and authentic transmission records persist. The resulting audit statement
authenticates the signed author, phase and ledger, without authenticating the
rebroadcaster or requiring observation of every pending envelope.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player}

/-- Traffic soundness at any service-instruction prefix, including the cuts
inside a source event. Every prefix has an actual permitted completion. -/
theorem initialized_sourceService_partial_conformance
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (opportunities : BindingOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (count : Nat) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        ((rosterPlan setup rosters).take count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  obtain ⟨initial, supported, reachedPrefix⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨final, continued⟩ := ((runtime setup).runInteractionPlan leaks players network
    ((rosterPlan setup rosters).drop count) execution).support_nonempty
  have complete : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterPlan setup rosters)
      (ReactiveApplication.Execution.initial (application setup leaks) initial)).support := by
    rw [← List.take_append_drop count (rosterPlan setup rosters),
      (runtime setup).runInteractionPlan_append, FinDist.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, reachedPrefix, continued⟩
  have traffic := initialized_sourceService_conformance bounds values capacity opportunities
    players lawful network final (by
      rw [FinDist.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨initial, supported, complete⟩)
  have included := (runtime setup).executionTraffic_runInteractionPlan leaks players network
    ((rosterPlan setup rosters).drop count) execution final continued
  exact fun record present => traffic record (included.subset present)

/-- The full historical traffic passes the checker at every legal retained
history, including off-path decisions and partially observed pending traffic. -/
theorem sourceService_history_traffic
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History) :
    ∀ record ∈ (application setup leaks).stateTraffic history.state,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  have lawful : ∀ who past view response, response ∈ (menu.uniformResponses who past view).support →
      response ∈ menu.actions who past view :=
    fun who past view response => (menu.uniformResponses_support who past view response).mp
  obtain ⟨state, trace⟩ := history
  cases state with
  | none => simp [ReactiveApplication.stateTraffic]
  | some control =>
      have supported := menu.roundSupported_uniform (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace
      rcases control with ⟨remaining, actor, execution⟩
      change ∀ record ∈ app.executionTraffic execution, _
      cases actor with
      | none =>
          obtain ⟨accounted, reached⟩ := supported
          dsimp only at accounted
          have within : execution.environmentRecall.length ≤ (rosterPlan setup rosters).length :=
            by omega
          rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses _ within]
            at reached
          exact initialized_sourceService_partial_conformance bounds values capacity opportunities
            menu.uniformResponses lawful network _ execution reached
      | some who =>
          obtain ⟨accounted, count, prior, command, position, reached, _, _, observed⟩ := supported
          have within : count ≤ (rosterPlan setup rosters).length := by omega
          rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses count within]
            at reached
          rw [app.executionTraffic_environment prior execution command observed]
          exact initialized_sourceService_partial_conformance bounds values capacity opportunities
            menu.uniformResponses lawful network count prior reached

/-- Any authentic partial sample of signed phase evidence collects zero
traffic penalties on a retained history. No sampling coverage is needed for
this soundness direction. -/
theorem sourceService_history_traffic_audit_clear
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (sample : List (EnvelopeEvidence setup leaks) →
      FinDist (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed,
      observed ∈ (sample actual).support → observed ⊆ actual)
    (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).History)
    (who : Player) :
    (((application setup leaks).sampledTrafficAudit (envelopeEvidence setup leaks)
      (fun evidence => evidence.2.2.sender)
      (fun evidence => (runtime setup).permittedServiceEnvelope
        evidence.1 evidence.2.1 evidence.2.2)
      sample ((application setup leaks).stateTraffic history.state)).map
        (fun verdict => verdict who)).prob true = 0 := by
  apply (application setup leaks).sampledTrafficAudit_sound
  · exact authentic _
  · intro record member _
    exact sourceService_history_traffic bounds values capacity opportunities network
      history record member

end Vegas
