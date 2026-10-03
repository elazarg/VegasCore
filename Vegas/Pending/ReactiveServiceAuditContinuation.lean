/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveRiskMenu
import Interaction.ReactiveInvariantContinuation
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditContinuation

/-! # Rational continuation after a public decision miss

A decision miss persists under every native continuation. The public branch of
the one-time audit therefore collects with certainty under every future policy,
regardless of traffic observation or report delivery. At an information site
where the owner sees this miss, the escrow subtracts the same constant from
every whole-policy continuation. Rational play there is exactly rational play
for the base payoff, rather than renewed compliance enforced by the deposit.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability
  GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The completed miss makes the collected charge constant under every
bounded native continuation, including arbitrary future deviations. -/
theorem serviceAudit_continuation_charge_of_miss (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (before : (runtime.reactiveApplication leaks).Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some before))
    (event : graph.EventId) (who : Player)
    (owned : graph.actor? event = some who)
    (missed : event ∈ before.execution.application.missedEvents)
    (final : (menu.protocol initial horizon scheduler).History)
    (supported : final ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile fuel ⟨some before, trace⟩).support) :
    TerminalAudit.charge (runtime.serviceAuditObservation leaks)
      (runtime.serviceAudit leaks trafficAudit) final.state who = 1 := by
  obtain ⟨result, stateEq, persists⟩ :=
    (runtime.reactiveMissedDecisionInvariant leaks event).behavioral_continuation
      menu initial horizon scheduler profile fuel before trace final missed supported
  rw [stateEq]
  exact runtime.serviceAudit_charge_of_miss leaks trafficAudit result who event owned persists

/-- The candidate continuation menu admits every effective later response after
this owner's public miss, whatever future policies or service commands do.
The miss is read from the actual later public view. -/
theorem riskActions_continuation_of_miss (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (before : (runtime.reactiveApplication leaks).Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some before))
    (event : graph.EventId) (who : Player)
    (owned : graph.actor? event = some who)
    (missed : event ∈ before.execution.application.missedEvents)
    (final : (menu.protocol initial horizon scheduler).History)
    (supported : final ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile fuel ⟨some before, trace⟩).support) :
    ∃ result, final.state = some result ∧
      bounds.riskActions runtime leaks bound who (result.execution.recall who)
          (result.execution.observe (runtime.reactiveApplication leaks) who) =
        (bounds.menu runtime leaks).actions who (result.execution.recall who)
          (result.execution.observe (runtime.reactiveApplication leaks) who) := by
  obtain ⟨result, stateEq, persists⟩ :=
    (runtime.reactiveMissedDecisionInvariant leaks event).behavioral_continuation
      menu initial horizon scheduler profile fuel before trace final missed supported
  refine ⟨result, stateEq, bounds.riskActions_of_risk runtime leaks bound who _ _ ?_⟩
  apply runtime.serviceRisk_of_public_miss leaks bound
  exact result.execution.application.publicView.missedDecisionBy_of_event who event owned persists

omit [Fintype Player] in
/-- Every hidden history in a player's information site has the contract view
the player currently sees. A publicly observed miss needs no watcher evidence. -/
theorem missedDecision_at_information_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (who : Player) (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (observed : site.1 = some (past, view)) (event : graph.EventId)
    (missed : event ∈ view.application.publicView.missedEvents)
    (history : (menu.information initial horizon scheduler).InformationHistory who site.1) :
    ∃ control, history.1.state = some control ∧
      event ∈ control.execution.application.missedEvents := by
  rcases history with ⟨⟨state, trace⟩, same⟩
  change (menu.signals initial horizon scheduler).infoOf who trace = site.1 at same
  rw [menu.info initial horizon scheduler who trace, observed] at same
  cases state with
  | none => cases same
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
        have views := congrArg (fun input => input.2.application.publicView)
          (Option.some.inj same)
        have markers := congrArg PublicView.missedEvents views
        change control.execution.application.missedEvents =
          view.application.publicView.missedEvents at markers
        exact ⟨control, rfl, markers ▸ missed⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
        cases same

/-- At a site where the owner sees its public miss, the actual audit changes
none of the whole-policy rationality comparisons. Base expectations are
explicitly integrable; no on-path or belief-consistency premise is required. -/
theorem serviceAudit_rationalAt_iff_of_miss (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (base : (runtime.reactiveApplication leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ)
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (fuel : Nat) (who : Player)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (observed : site.1 = some (past, view)) (event : graph.EventId)
    (owned : graph.actor? event = some who)
    (missed : event ∈ view.application.publicView.missedEvents)
    (integrable : ∀ alternative,
      (assessment.truncatedContinuationContext site (fun final => base final.state who)
        fuel).IntegrableAt alternative) :
    assessment.IsSequentiallyRationalAt site
        (assessment.truncatedContinuationContext site
          (fun final => TerminalAudit.utility (fun state => base state)
            (runtime.serviceAuditObservation leaks) (runtime.serviceAudit leaks trafficAudit)
              deposit final.state who) fuel) ↔
      assessment.IsSequentiallyRationalAt site
        (assessment.truncatedContinuationContext site
          (fun final => base final.state who) fuel) := by
  apply assessment.isSequentiallyRationalAt_iff_of_constant_collection
    ((menu.information initial horizon scheduler).truncatedRunner fuel) site
      (fun final => base final.state)
      (fun final => runtime.serviceAuditObservation leaks final.state)
      (runtime.serviceAudit leaks trafficAudit) deposit 1 integrable
  intro alternative
  change expect ((assessment.belief who site).bind fun history =>
    (menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        assessment.strategy who alternative) fuel history.1)
      (fun final => TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks trafficAudit) final.state who) = 1
  calc
    _ = expect ((assessment.belief who site).bind fun history =>
        (menu.information initial horizon scheduler).runBehavioralFrom
          (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
            assessment.strategy who alternative) fuel history.1) (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro final supported
      obtain ⟨history, _possible, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨control, stateEq, failed⟩ := runtime.missedDecision_at_information_history leaks
        menu initial horizon scheduler who site past view observed event missed history
      rcases history with ⟨⟨state, trace⟩, _info⟩
      change state = some control at stateEq
      subst state
      exact runtime.serviceAudit_continuation_charge_of_miss leaks menu initial horizon
        scheduler trafficAudit _ fuel control trace event who owned failed
          final reached
    _ = 1 := expect_constant _ 1

end Vegas.EventGraphRuntime
