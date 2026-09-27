/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceWatcher
import Interaction.ReactiveTrafficState

/-! # Extending the revelation service through a terminal traffic audit

The audit samples authentic traffic only after strategic play. Its conformance
and first-departure certificates concern actual executions, not equilibrium
behavior. Conditional coverage and collectible deposits restore every effective
response; private normalization then restores the complete bounded raw menu.
No strategic reporter or zero-utility premise is used by this enforcement edge.

The source correspondence and concrete traffic classifier are separate inputs.
The service calendar is unchanged. This theorem therefore does not by itself
justify extra activation opportunities or fresh source commitments.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)

/-- Both menus use exactly the same application, scheduler and observations. -/
def effectiveRestriction :
    (information setup leaks bounds watcher).ActionRestriction
      (effectiveInformation setup leaks bounds watcher) :=
  (menu_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)

variable (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)

include reveals observer in
open Classical in
/-- Operational trace certificates suffice for standard SE with the actual
randomized settlement law. Audit randomness and player verdicts may be correlated. -/
theorem audited_raw_of_traffic
    (permitted : (application setup leaks).TrafficRecord → Bool)
    (sample : List (application setup leaks).TrafficRecord →
      FinDist (List (application setup leaks).TrafficRecord))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (conforming : ∀ (history : (protocol setup leaks bounds watcher).History) record,
      record ∈ (application setup leaks).stateTraffic history.state → permitted record = true)
    (evidence : ∀ (profile : Profile
        (effectiveInformation setup leaks bounds watcher).behavioralSignature) who
      (site : (information setup leaks bounds watcher).InformationSite who)
      (action : (effectiveInformation setup leaks bounds watcher).Choice who
        ((effectiveRestriction setup leaks bounds watcher).site who site).1),
      action ∉ Set.range ((effectiveRestriction setup leaks bounds watcher).choice who site.1) →
      ∀ history : (information setup leaks bounds watcher).InformationHistory who site.1,
      ∀ next ∈ ((effectiveInformation setup leaks bounds watcher).runBehavioralFrom
        (Profile.update profile who ((profile who).commit
          ((effectiveRestriction setup leaks bounds watcher).site who site).1 action))
        1 ((effectiveRestriction setup leaks bounds watcher).history history.1)).support,
      ∃ record ∈ (application setup leaks).stateTraffic next.state,
        record.input.broadcaster = who ∧ permitted record = false)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (baseInvariant : ∀ state,
      base (((runtime setup).reactiveNormalization leaks).state state) = base state)
    (lower upper probability deposit : Player → ℝ)
    (nonnegative : ∀ who, 0 ≤ deposit who)
    (below : ∀ (history : (protocol setup leaks bounds watcher).History) who,
      lower who ≤ base history.state who)
    (above : ∀ (history : ((bounds.menu (runtime setup) leaks).protocol
        (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History) who,
      base history.state who ≤ upper who)
    (sufficient : ∀ who, upper who - probability who * deposit who ≤ lower who)
    (coverage : ∀ who actual record, record ∈ actual →
      record.input.broadcaster = who → permitted record = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    {Observation : Type} (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (source : (information setup leaks bounds watcher).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((menu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher))
      (fun who site => source.continuationContext site (fun final => base final.state who)
        (2 * horizon setup watcher + 1))) :
    let audit := (application setup leaks).sampledTrafficAudit permitted sample
    let utility := TerminalAudit.utility base (application setup leaks).stateTraffic audit deposit
    let settle := TerminalAudit.settlement base (application setup leaks).stateTraffic audit deposit
    ∃ target : (rawInformation setup leaks bounds watcher).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu (runtime setup) leaks).decisionInformationAntichain (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.continuationContext site
          (fun final => utility final.state who) (2 * horizon setup watcher + 1)) ∧
      ((rawInformation setup leaks bounds watcher).runBehavioral target.strategy
        (2 * horizon setup watcher + 1)).bind
          (fun final => (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        ((information setup leaks bounds watcher).runBehavioral source.strategy
          (2 * horizon setup watcher + 1)).map
            (fun final => (observe final.state, base final.state)) := by
  classical
  intro audit utility settle
  let app := application setup leaks
  let initial := initialLaw setup
  let count := horizon setup watcher
  let service := scheduler setup leaks watcher
  let retained := menu setup leaks bounds watcher
  let effective := bounds.menu (runtime setup) leaks
  let restriction := effectiveRestriction setup leaks bounds watcher
  let depth (who : Player)
      (site : (effectiveInformation setup leaks bounds watcher).InformationSite who) :=
    decisionDepth setup leaks watcher who site.1
  have clock := menu_common_decision_depth setup leaks effective watcher reveals observer
  have sourceClock := menu_common_decision_depth setup leaks retained watcher reveals observer
  have sourceRemaining := (source.sequentialEquilibrium_remaining_iff
    (information setup leaks bounds watcher)
    (retained.decisionInformationAntichain initial count service) (2 * count + 1)
    (retained.bounded initial count service)
    (fun who site => decisionDepth setup leaks watcher who site.1) sourceClock
    (fun who final => base final.state who)).mpr equilibrium
  have sound (history : (protocol setup leaks bounds watcher).History) (who : Player) :
      TerminalAudit.charge (fun final => app.stateTraffic final.state) audit
        (restriction.history history) who = 0 :=
    app.sampledTrafficAudit_sound permitted sample (app.stateTraffic history.state) who
      (authentic _) (fun record present _ => conforming history record present)
  have collection (profile : Profile
      (effectiveInformation setup leaks bounds watcher).behavioralSignature) who
      (site : (information setup leaks bounds watcher).InformationSite who)
      (action : (effectiveInformation setup leaks bounds watcher).Choice who
        (restriction.site who site).1)
      (extra : action ∉ Set.range (restriction.choice who site.1))
      (history : (information setup leaks bounds watcher).InformationHistory who site.1) :
      probability who ≤ (((((effectiveInformation setup leaks bounds watcher).runBehavioralFrom
        (Profile.update profile who ((profile who).commit (restriction.site who site).1 action))
        (2 * count + 1 - depth who (restriction.site who site))
        (restriction.history history.1)).map (fun final => app.stateTraffic final.state)).bind
          audit).map (fun verdict => verdict who)).prob true := by
    have within : depth who (restriction.site who site) < 2 * count + 1 := by
      obtain ⟨reference, running, _action⟩ := site.2
      have sameDepth := sourceClock who site reference
      by_contra late
      exact running (retained.bounded initial count service reference.1.state reference.1.trace
        (by
          change ¬ decisionDepth setup leaks watcher who site.1 < 2 * count + 1 at late
          omega))
    have bound := effective.trafficAudit_collection_after_step initial count service permitted
      sample who (probability who) (coverage who)
      (Profile.update profile who ((profile who).commit (restriction.site who site).1 action))
      (2 * count + 1 - depth who (restriction.site who site) - 1)
      (restriction.history history.1)
      (by simpa only [ReactiveApplication.ResponseMenu.trafficAudit_eq_stateTraffic] using
        evidence profile who site action extra history)
    have fuel : 1 + (2 * count + 1 - depth who (restriction.site who site) - 1) =
        2 * count + 1 - depth who (restriction.site who site) := by omega
    have readout : effective.trafficAudit initial count service =
        fun final => app.stateTraffic final.state :=
      funext (effective.trafficAudit_eq_stateTraffic initial count service)
    simpa only [readout, fuel] using bound
  obtain ⟨effectiveTarget, targetRemaining, _agrees, _beliefs, _historyLaw, joint,
      _clean, _terminal⟩ := restriction.sequential_equilibrium_extends_of_terminal_audit
    (retained.decisionInformationAntichain initial count service)
    (effective.uniformAssessment initial count service)
    (effective.uniform_fullyMixed initial count service)
    (effective.decisionRecall initial count service) (2 * count + 1)
    (effective.bounded initial count service) depth clock
    (fun final who => base final.state who) (fun final who => base final.state who)
    (fun final => app.stateTraffic final.state) audit (fun _ _ => rfl) sound
    lower upper probability deposit nonnegative below above sufficient collection source
      sourceRemaining
  have targetFull := (effectiveTarget.sequentialEquilibrium_remaining_iff
    (effectiveInformation setup leaks bounds watcher)
    (effective.decisionRecall initial count service).antichain (2 * count + 1)
    (effective.bounded initial count service) depth clock
    (fun who final => utility final.state who)).mp targetRemaining
  obtain ⟨target, _strategy, targetSE, _beliefs, stateLaw⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium (runtime setup) leaks initial count service
      effectiveTarget (fun who state => utility state who) targetFull
  have utilityInvariant (state : app.ProtocolState) :
      utility (((runtime setup).reactiveNormalization leaks).state state) = utility state := by
    funext who
    simp only [utility, TerminalAudit.utility, TerminalAudit.charge, baseInvariant,
      ReactiveApplication.stateTraffic_normalization]
  have settlementInvariant (state : app.ProtocolState) :
      settle (((runtime setup).reactiveNormalization leaks).state state) = settle state := by
    simp only [settle, TerminalAudit.settlement, ReactiveApplication.stateTraffic_normalization,
      baseInvariant]
  refine ⟨target, ?_, ?_⟩
  · simpa only [utilityInvariant] using targetSE
  · have rawJoint := congrArg (fun law => law.bind fun state =>
        (settle state).map (fun payoffs => (observe state, payoffs))) stateLaw
    simp only [FinDist.bind_map, settlementInvariant, observationInvariant] at rawJoint
    rw [rawJoint]
    have projected := congrArg (fun law => law.map fun result =>
      (observe result.1.state, result.2)) joint
    have sameState (history : (protocol setup leaks bounds watcher).History) :
        (restriction.history history).state = history.state := rfl
    simpa only [FinDist.map_comp, FinDist.map_bind, Function.comp_def, sameState,
      settle, TerminalAudit.settlement] using projected.symm

end Vegas.SourceProgram.RevealService
