/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRestrictionExtension
import Vegas.Pending.ReactiveAliasEquilibrium

/-! # Audited full-source retained equilibrium in the bounded raw runtime

The effective-game equilibrium lifts through the existing private response
normalization. Base utility and the full audit observation are invariant by
construction. The observed result may be any readout invariant under this
normalization, including the typed source readout and initial private types.
No raw action is removed, and the conclusion retains the actual joint sampled
settlement vector. Original source-language SE preservation is a separate edge.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_audited_raw_equilibrium_extends {Parameter Observation : Type}
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    [network.FiniteSupport]
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (SettledEvidence setup) →
      PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (source : ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((sourceServiceMenu setup leaks bounds rosters).decisionInformationAntichain
        (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network))
      (fun who site => source.truncatedContinuationContext site (fun history =>
        baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
          history.state who) (2 * (rosterPlan setup rosters).length + 1))) :
    let menu := sourceServiceMenu setup leaks bounds rosters
    let raw := bounds.rawMenu (runtime setup) leaks
    let count := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let base := baseUtility setup leaks
      (fun state => utility (setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base
      (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    let settle := TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    ∃ target : (raw.information (initialLaw setup) count scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw setup) count scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * count + 1)) ∧
      (∀ final ∈ ((raw.information (initialLaw setup) count scheduler).runBehavioral
          target.strategy (2 * count + 1)).support, ∀ who,
        TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample) final.state who = 0) ∧
      ((raw.information (initialLaw setup) count scheduler).runBehavioral target.strategy
        (2 * count + 1)).bind (fun final =>
          (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        ((menu.information (initialLaw setup) count scheduler).runBehavioral source.strategy
          (2 * count + 1)).map (fun final => (observe final.state, base final.state)) := by
  classical
  intro menu raw count scheduler base deposit payoff settle
  obtain ⟨effective, equilibrium, _agrees, histories, settled⟩ :=
    sourceService_audited_equilibrium_extends setup leaks bounds values capacity rosters
      opportunities network parameter utility sample authentic probability positive coverage
      observe source equilibrium
  obtain ⟨target, _strategy, targetSE, _beliefs, stateLaw⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium (runtime setup) leaks (initialLaw setup)
      count scheduler effective (fun who state => payoff state who) equilibrium
  have baseInvariant (state : (application setup leaks).ProtocolState) :
      base (((runtime setup).reactiveNormalization leaks).state state) = base state :=
    baseUtility_normalization setup leaks
      (fun source => utility (setup.parameterOutcome parameter source)) state
  have observation (state : (application setup leaks).ProtocolState) :=
    (runtime setup).serviceAuditObservation_normalization leaks
      ((runtime setup).reactiveNormalization leaks) state
  have payoffInvariant (state : (application setup leaks).ProtocolState) :
      payoff (((runtime setup).reactiveNormalization leaks).state state) = payoff state := by
    funext who
    simp only [payoff, TerminalAudit.utility, TerminalAudit.charge, baseInvariant, observation]
  have settlementInvariant (state : (application setup leaks).ProtocolState) :
      settle (((runtime setup).reactiveNormalization leaks).state state) = settle state := by
    simp only [settle, TerminalAudit.settlement, baseInvariant, observation]
  refine ⟨target, ?_, ?_, ?_⟩
  · simpa only [payoffInvariant] using targetSE
  · intro final reached who
    have normalized : ((runtime setup).reactiveNormalization leaks).state final.state ∈
        ((((bounds.menu (runtime setup) leaks).information (initialLaw setup) count
          scheduler).runBehavioral effective.strategy (2 * count + 1)).map
            GameTheory.Protocol.ExecutionProtocol.History.state).support := by
      rw [← stateLaw, PMF.support_map]
      exact ⟨final, reached, rfl⟩
    rw [PMF.support_map, ← histories, PMF.support_map] at normalized
    obtain ⟨_, ⟨permitted, _, rfl⟩, sameState⟩ := normalized
    have clear := sourceService_history_audit_clear setup leaks bounds values capacity rosters
      opportunities network sample authentic permitted who
    have invariant : TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks sample)
          (((runtime setup).reactiveNormalization leaks).state final.state) who =
        TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample) final.state who := by
      simp only [TerminalAudit.charge, observation]
    rw [← invariant, ← sameState]
    exact clear
  · have joint := congrArg (fun law => law.bind fun state =>
      (settle state).map (fun payoffs => (observe state, payoffs))) stateLaw
    simp only [PMF.bind_map, Function.comp_def, settlementInvariant, observationInvariant] at joint
    exact joint.trans settled

end Vegas
