/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAliasEquilibrium
import Interaction.ReactiveTrafficState
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveMenuRestriction
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Terminal traffic auditing in the bounded native runtime

Any retained response menu with the stated traffic certificates and decision
clock extends to the full bounded raw game. The scheduler, initial law and
application graph are arbitrary. This is an enforcement and private-alias edge;
source correspondence is a separate compiler obligation.

Authentic partial audit records and a fixed collectible deposit vector preserve
the exact joint observation and realized settlement law. No strategic reporter,
source syntax restriction or particular transmission calendar is assumed here.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : FinDist (State graph)) (count : Nat)
  (service : (runtime.reactiveApplication leaks).Scheduler)
  (retained : (runtime.reactiveApplication leaks).ResponseMenu)
  (included : retained.IncludedIn (bounds.menu runtime leaks))

open Classical in
/-- Operational trace certificates suffice for standard SE with the actual
randomized settlement law. Audit randomness and player verdicts may be correlated. -/
theorem audited_raw_sequential_equilibrium
    (depth : ∀ who,
      ((bounds.menu runtime leaks).information initial count service).InformationSite who → Nat)
    (clock : ∀ who site, InformationModel.InformationSite.CommonDepth
      ((bounds.menu runtime leaks).information initial count service) site (depth who site))
    (permitted : (runtime.reactiveApplication leaks).TrafficRecord → Bool)
    (sample : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (List (runtime.reactiveApplication leaks).TrafficRecord))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (conforming : ∀ (history : (retained.protocol initial count service).History) record,
      record ∈ (runtime.reactiveApplication leaks).stateTraffic history.state →
        permitted record = true)
    (evidence : ∀ (profile : Profile
        ((bounds.menu runtime leaks).information initial count service).behavioralSignature) who
      (site : (retained.information initial count service).InformationSite who)
      (action : ((bounds.menu runtime leaks).information initial count service).Choice who
        ((included.actionRestriction initial count service).site who site).1),
      action ∉ Set.range ((included.actionRestriction initial count service).choice who site.1) →
      ∀ history : (retained.information initial count service).InformationHistory who site.1,
      ∀ next ∈ (((bounds.menu runtime leaks).information initial count service).runBehavioralFrom
        (Profile.update profile who ((profile who).commit
          ((included.actionRestriction initial count service).site who site).1 action))
        1 ((included.actionRestriction initial count service).history history.1)).support,
      ∃ record ∈ (runtime.reactiveApplication leaks).stateTraffic next.state,
        record.input.broadcaster = who ∧ permitted record = false)
    (base : (runtime.reactiveApplication leaks).ProtocolState → Player → ℝ)
    (baseInvariant : ∀ state,
      base ((runtime.reactiveNormalization leaks).state state) = base state)
    (lower upper probability deposit : Player → ℝ)
    (nonnegative : ∀ who, 0 ≤ deposit who)
    (below : ∀ (history : (retained.protocol initial count service).History) who,
      lower who ≤ base history.state who)
    (above : ∀ (history : ((bounds.menu runtime leaks).protocol
        initial count service).History) who,
      base history.state who ≤ upper who)
    (sufficient : ∀ who, upper who - probability who * deposit who ≤ lower who)
    (coverage : ∀ who actual record, record ∈ actual →
      record.input.broadcaster = who → permitted record = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    {Observation : Type}
    (observe : (runtime.reactiveApplication leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe ((runtime.reactiveNormalization leaks).state state) = observe state)
    (source : (retained.information initial count service).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      (retained.decisionInformationAntichain initial
        count service)
      (fun who site => source.continuationContext site (fun final => base final.state who)
        (2 * count + 1))) :
    let audit := (runtime.reactiveApplication leaks).sampledTrafficAudit permitted sample
    let utility := TerminalAudit.utility base
      (runtime.reactiveApplication leaks).stateTraffic audit deposit
    let settle := TerminalAudit.settlement base
      (runtime.reactiveApplication leaks).stateTraffic audit deposit
    ∃ target :
        ((bounds.rawMenu runtime leaks).information initial count service).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain initial
          count service)
        (fun who site => target.continuationContext site
          (fun final => utility final.state who) (2 * count + 1)) ∧
      (((bounds.rawMenu runtime leaks).information initial count service).runBehavioral
        target.strategy (2 * count + 1)).bind
          (fun final => (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        ((retained.information initial count service).runBehavioral source.strategy
          (2 * count + 1)).map
            (fun final => (observe final.state, base final.state)) := by
  classical
  intro audit utility settle
  let app := runtime.reactiveApplication leaks
  let effective := bounds.menu runtime leaks
  let restriction := included.actionRestriction initial count service
  have sourceClock (who : Player)
      (site : (retained.information initial count service).InformationSite who) :
      InformationModel.InformationSite.CommonDepth
        (retained.information initial count service) site
        (depth who (restriction.site who site)) := by
    intro history
    have same := clock who (restriction.site who site)
      (restriction.informationHistory who site history)
    simpa only [InformationModel.ActionRestriction.informationHistory_val,
      restriction.length] using same
  have sourceRemaining := (source.sequentialEquilibrium_remaining_iff
    (retained.information initial count service)
    (retained.decisionInformationAntichain initial count service) (2 * count + 1)
    (retained.bounded initial count service)
    (fun who site => depth who (restriction.site who site)) sourceClock
    (fun who final => base final.state who)).mpr equilibrium
  have sound (history : (retained.protocol initial count service).History) (who : Player) :
      TerminalAudit.charge (fun final => app.stateTraffic final.state) audit
        (restriction.history history) who = 0 :=
    app.sampledTrafficAudit_sound permitted sample (app.stateTraffic history.state) who
      (authentic _) (fun record present _ => conforming history record present)
  have collection (profile : Profile
      ((bounds.menu runtime leaks).information initial count service).behavioralSignature) who
      (site : (retained.information initial count service).InformationSite who)
      (action : ((bounds.menu runtime leaks).information initial count service).Choice who
        (restriction.site who site).1)
      (extra : action ∉ Set.range (restriction.choice who site.1))
      (history : (retained.information initial count service).InformationHistory who site.1) :
      probability who ≤
        ((((((bounds.menu runtime leaks).information initial count service).runBehavioralFrom
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
          change ¬ depth who (restriction.site who site) < 2 * count + 1 at late
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
    ((bounds.menu runtime leaks).information initial count service)
    (effective.decisionRecall initial count service).antichain (2 * count + 1)
    (effective.bounded initial count service) depth clock
    (fun who final => utility final.state who)).mp targetRemaining
  obtain ⟨target, _strategy, targetSE, _beliefs, stateLaw⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium runtime leaks initial count service
      effectiveTarget (fun who state => utility state who) targetFull
  have utilityInvariant (state : app.ProtocolState) :
      utility ((runtime.reactiveNormalization leaks).state state) = utility state := by
    funext who
    simp only [utility, TerminalAudit.utility, TerminalAudit.charge, baseInvariant,
      ReactiveApplication.stateTraffic_normalization]
  have settlementInvariant (state : app.ProtocolState) :
      settle ((runtime.reactiveNormalization leaks).state state) = settle state := by
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
    have sameState (history : (retained.protocol initial count service).History) :
        (restriction.history history).state = history.state := rfl
    simpa only [FinDist.map_comp, FinDist.map_bind, Function.comp_def, sameState,
      settle, TerminalAudit.settlement] using projected.symm


end Vegas.EventGraphRuntime.MessageBounds
