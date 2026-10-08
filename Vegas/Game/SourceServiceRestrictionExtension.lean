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
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
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
        (fun who site => target.truncatedContinuationContext site
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
  have sourceBounded := menu.bounded (initialLaw setup) count scheduler
  have targetBounded := effective.bounded (initialLaw setup) count scheduler
  have sourceCertificate := sourceBounded.wellFoundedHistories
  have targetCertificate := targetBounded.wellFoundedHistories
  have sourceTerminal := (source.isSequentialEquilibrium_iff_truncated_of_bounded
    (menu.information (initialLaw setup) count scheduler)
    (menu.decisionInformationAntichain (initialLaw setup) count scheduler) sourceCertificate
    sourceBounded (fun who history => base history.state who)).mpr equilibrium
  have matching (history : (menu.protocol (initialLaw setup) count scheduler).History)
      (who : Player) : payoff (restriction.history history).state who = base history.state who := by
    have clean := sourceService_history_audit_clear setup leaks bounds values capacity rosters
      opportunities network sample authentic history who
    change base history.state who - TerminalAudit.charge
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
        history.state who * deposit who = base history.state who
    rw [clean, zero_mul, sub_zero]
  let _ := Fintype.ofFinite (effective.protocol (initialLaw setup) count scheduler).History
  obtain ⟨target, terminal, agrees, _beliefs, historyLaw, _joint⟩ :=
    restriction.sequentialEquilibrium_extends_of_continuation
      (menu.decisionInformationAntichain (initialLaw setup) count scheduler)
      sourceCertificate targetCertificate
      (effective.uniformAssessment (initialLaw setup) count scheduler)
      (effective.uniform_fullyMixed (initialLaw setup) count scheduler)
      (effective.decisionRecall (initialLaw setup) count scheduler)
      (fun who site => depth who (restriction.site who site))
      (fun who site => clock who (restriction.site who site))
      (fun who history => base history.state who)
      (fun who history => payoff history.state who) (fun who history => matching history who)
      (fun first second paired who site action _extra belief => by
        obtain ⟨repair, dominates⟩ := sourceService_continuation_settlement_comparison setup leaks
          bounds values capacity rosters opportunities network parameter utility sample
          authentic probability positive coverage first second paired who site
          (depth who (restriction.site who site)) (sourceClock who site)
          ((second who).commit (restriction.site who site).1 action)
        refine ⟨repair, ?_⟩
        simp only [restriction.runBehavioralTerminalFrom_history_eq_remaining targetCertificate
            targetBounded _ (clock who (restriction.site who site)),
          restriction.runBehavioralTerminalFrom_eq_remaining sourceCertificate targetBounded _
            (clock who (restriction.site who site))]
        exact dominates belief)
      source sourceTerminal
  rw [InformationModel.runBehavioralTerminalFrom_initHistory _
      sourceCertificate _ sourceBounded,
    InformationModel.runBehavioralTerminalFrom_initHistory _
      targetCertificate _ targetBounded] at historyLaw
  have full := (target.isSequentialEquilibrium_iff_truncated_of_bounded
    (effective.information (initialLaw setup) count scheduler)
    (effective.decisionRecall (initialLaw setup) count scheduler).decisionInformationAntichain
    targetCertificate targetBounded (fun who history => payoff history.state who)).mp terminal
  refine ⟨target, full, agrees, historyLaw, ?_⟩
  rw [← historyLaw, PMF.bind_map]
  calc
    _ = ((menu.information (initialLaw setup) count scheduler).runBehavioral source.strategy
        (2 * count + 1)).bind (fun final =>
          PMF.pure (observe final.state, base final.state)) := by
      apply bind_congr_on_support _
      intro final _
      have clean := sourceService_history_settlement setup leaks bounds values capacity rosters
        opportunities network sample authentic base deposit final
      change settle final.state = PMF.pure (base final.state) at clean
      change (settle final.state).map (fun payoffs => (observe final.state, payoffs)) =
        PMF.pure (observe final.state, base final.state)
      rw [clean, PMF.pure_map]
    _ = _ := pmf_bind_pure_eq_map _ _

end Vegas
