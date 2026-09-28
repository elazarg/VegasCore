/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationComparison
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential equilibrium under the full-source service audit

Every retained sequential equilibrium extends to the effective native menu.
The comparison uses the concrete private binding repair and the actual sampled
settlement. All deposits and audit rates are fixed before the equilibrium.
The initialized law preserves the full joint realized payoff vector.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_audited_equilibrium_extends {Parameter Observation : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (EnvelopeEvidence setup leaks) →
      FinDist (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.2.sender = who →
      (runtime setup).permittedServiceEnvelope record.1 record.2.1 record.2.2 = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    (observe : (application setup leaks).ProtocolState → Observation)
    (source : ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((sourceServiceMenu setup leaks bounds rosters).decisionInformationAntichain
        (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network))
      (fun who site => source.continuationContext site (fun history =>
        baseUtility setup leaks (fun state => utility (setup.parameterOutcome parameter state))
          history.state who) (2 * (rosterPlan setup rosters).length + 1))) :
    let menu := sourceServiceMenu setup leaks bounds rosters
    let effective := bounds.menu (runtime setup) leaks
    let count := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let restriction := (sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) count scheduler
    let base := baseUtility setup leaks
      (fun state => utility (setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base
      (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    let settle := TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    ∃ target : (effective.information (initialLaw setup) count scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (effective.decisionInformationAntichain (initialLaw setup) count scheduler)
        (fun who site => target.continuationContext site
          (fun history => payoff history.state who) (2 * count + 1)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      ((menu.information (initialLaw setup) count scheduler).runBehavioral source.strategy
        (2 * count + 1)).map restriction.history =
          (effective.information (initialLaw setup) count scheduler).runBehavioral target.strategy
            (2 * count + 1) ∧
      ((effective.information (initialLaw setup) count scheduler).runBehavioral target.strategy
        (2 * count + 1)).bind (fun final =>
          (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        ((menu.information (initialLaw setup) count scheduler).runBehavioral source.strategy
          (2 * count + 1)).map (fun final => (observe final.state, base final.state)) := by
  classical
  intro menu effective count scheduler restriction base deposit payoff settle
  choose depth clock using roster_menu_common_depth setup leaks rosters network effective
  have sourceClock (who : Player)
      (site : (menu.information (initialLaw setup) count scheduler).InformationSite who) :
      InformationModel.InformationSite.CommonDepth
        (menu.information (initialLaw setup) count scheduler) site
        (depth who (restriction.site who site)) := by
    intro history
    have same := clock who (restriction.site who site)
      (restriction.informationHistory who site history)
    simpa only [InformationModel.ActionRestriction.informationHistory_val,
      restriction.length] using same
  have sourceRemaining := (source.sequentialEquilibrium_remaining_iff
    (menu.information (initialLaw setup) count scheduler)
    (menu.decisionInformationAntichain (initialLaw setup) count scheduler) (2 * count + 1)
    (menu.bounded (initialLaw setup) count scheduler)
    (fun who site => depth who (restriction.site who site)) sourceClock
    (fun who history => base history.state who)).mpr equilibrium
  have matching (history : (menu.protocol (initialLaw setup) count scheduler).History)
      (who : Player) : payoff (restriction.history history).state who = base history.state who := by
    have clean := sourceService_history_audit_clear setup leaks bounds values capacity rosters
      opportunities network sample authentic history who
    change base history.state who - TerminalAudit.charge
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
        history.state who * deposit who = base history.state who
    rw [clean, zero_mul, sub_zero]
  obtain ⟨target, remaining, agrees, _beliefs, historyLaw, _joint, _terminal⟩ :=
    restriction.sequential_equilibrium_extends_of_continuation
      (menu.decisionInformationAntichain (initialLaw setup) count scheduler)
      (effective.uniformAssessment (initialLaw setup) count scheduler)
      (effective.uniform_fullyMixed (initialLaw setup) count scheduler)
      (effective.decisionRecall (initialLaw setup) count scheduler) (2 * count + 1)
      (effective.bounded (initialLaw setup) count scheduler) depth clock
      (fun history who => base history.state who)
      (fun history who => payoff history.state who) matching
      (fun first second paired who site action _extra belief => by
        obtain ⟨repair, dominates⟩ := sourceService_continuation_settlement_comparison setup leaks
          bounds values capacity rosters opportunities network parameter utility sample
          authentic probability positive coverage first second paired who site
          (depth who (restriction.site who site)) (sourceClock who site)
          ((second who).commit (restriction.site who site).1 action)
        exact ⟨repair, dominates belief⟩)
      source sourceRemaining
  have full := (target.sequentialEquilibrium_remaining_iff
    (effective.information (initialLaw setup) count scheduler)
    (effective.decisionRecall (initialLaw setup) count scheduler).antichain (2 * count + 1)
    (effective.bounded (initialLaw setup) count scheduler) depth clock
    (fun who history => payoff history.state who)).mp remaining
  refine ⟨target, full, agrees, historyLaw, ?_⟩
  rw [← historyLaw, FinDist.bind_map]
  calc
    _ = ((menu.information (initialLaw setup) count scheduler).runBehavioral source.strategy
        (2 * count + 1)).bind (fun final =>
          FinDist.pure (observe final.state, base final.state)) := by
      apply FinDist.bind_congr
      intro final _
      have clean := sourceService_history_settlement setup leaks bounds values capacity rosters
        opportunities network sample authentic base deposit final
      change settle final.state = FinDist.pure (base final.state) at clean
      change (settle final.state).map (fun payoffs => (observe final.state, payoffs)) =
        FinDist.pure (observe final.state, base final.state)
      rw [clean, FinDist.map_pure]
    _ = _ := (FinDist.map_eq_bind ..).symm

end Vegas
