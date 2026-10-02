/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterChoiceEvidence
import Vegas.Game.RevealServiceRosterPrefixSupport
import Vegas.Game.ServiceSettledAudit
import Vegas.Game.ServicePayoffBounds
import Vegas.Pending.ReactiveServicePublication

/-! # Settled audits of revelation rosters extend to the full bounded native game

One fixed deposit vector, computed from the finite payoff range and a positive
conditional observation rate, suffices for every retained sequential equilibrium.
Settlement judges signed packets against the settled record once the roster
plan has ended. The clean settled record, the breach of every additional
response and the native decision clock are discharged here. The audit remains
an explicit authentic settlement observation/collection service.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)

local instance : Nonempty ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History :=
  ⟨((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).initHistory⟩

omit [Fintype Player] in
/-- The roster calendar includes only unpublished packets. -/
theorem rosterScheduler_atMostOnce :
    (application setup leaks).AtMostOnce (rosterScheduler setup leaks rosters network) := by
  intro history view id selected
  dsimp only [rosterScheduler] at selected
  split at selected
  · cases (PMF.mem_support_pure_iff _ _).mp selected
  · exact (runtime setup).interactionInstruction_fresh leaks network history view _ id selected

omit [Fintype Player] in
/-- Every recorded transmission saw a ledger without repeated identifiers. -/
theorem roster_traffic_ledger_nodup :
    ∀ {state} (_ : ((application setup leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        state),
      ∀ record ∈ (application setup leaks).stateTraffic state,
        (record.ledger.map Message.id).Nodup
  | _, .start => by
      intro record member
      cases member
  | after, .extend (source := before) prior joint _ reached => by
      intro record member
      rw [(application setup leaks).stateTraffic_transition (initialLaw setup) _ _ ⟨_, prior⟩
        joint _ reached] at member
      rcases List.mem_append.mp member with old | fresh
      · exact roster_traffic_ledger_nodup prior record old
      · have valid := (application setup leaks).publishedOnce_history _
          (rosterScheduler_atMostOnce setup leaks rosters network) (initialLaw setup) _ prior
        cases before with
        | none => simp [ReactiveApplication.trafficStep] at fresh
        | some previous =>
            cases after with
            | none => simp [ReactiveApplication.trafficStep] at fresh
            | some next =>
                obtain ⟨input, _, rfl⟩ := List.mem_map.mp fresh
                exact valid

/-- At a terminal retained roster history the settled record permits every
ledger entry, and every transmitted packet is on the ledger. -/
theorem roster_terminal_published (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History)
    (control : (application setup leaks).Control) (current : history.state = some control)
    (terminal : (application setup leaks).terminal history.state) :
    (∀ message ∈ control.execution.network.ledger,
      ((runtime setup).settledRecord leaks control.execution).permits message = true) ∧
    ∀ input ∈ control.execution.network.inputs,
      input.envelope.id ∈ control.execution.network.ledger.map Message.id := by
  let menu := rosterMenu setup leaks bounds rosters
  have supported := menu.roundSupported_uniform (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) history.trace
  rw [current] at supported terminal
  obtain ⟨finished, idle⟩ := terminal
  obtain ⟨accounted, reached⟩ := supported
  rw [idle] at reached
  have position : control.execution.environmentRecall.length =
      (rosterPlan setup rosters).length := by
    rw [finished, Nat.add_zero] at accounted
    exact accounted
  rw [position, roster_roundsFrom setup leaks rosters network _ _ (Nat.le_refl _),
    List.take_length] at reached
  have completePlan : rosterPlanPrefix setup rosters (eventCount setup.program) =
      rosterPlan setup rosters := by
    apply congrArg (List.flatMap (rosterBlock setup rosters))
    simp only [List.take_eq_self_iff, List.length_finRange]
    exact Nat.le_refl _
  rw [← completePlan] at reached
  obtain ⟨_, _, state, related, _, _, _, clean⟩ :=
    initialized_roster_prefix_support setup leaks bounds rosters network reveals openable
      menu.uniformResponses
      (fun owner past view response member =>
        (menu.uniformResponses_support owner past view response).mp member)
      (eventCount setup.program) (Nat.le_refl _) control.execution reached
  obtain ⟨_, _, _, checkpoint⟩ := related.checkpoint setup.program _ _ _ 0 _ state
    control.execution
  exact ⟨publicationLedger_permitted setup leaks control.execution _
    checkpoint.invariant.reachable _ checkpoint.ledger checkpoint.receipts,
    fun input member => clean.inputs input member⟩

open Classical in
/-- Standard SE and the joint observation/realized settlement law survive
restoration of every bounded raw response under the settled audit. There is no
strategic watcher slot. -/
theorem roster_audited_sequential_equilibrium [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    [network.FiniteSupport]
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (baseInvariant : ∀ state,
      base (((runtime setup).reactiveNormalization leaks).state state) = base state)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual (record : SettledEvidence setup), record ∈ actual →
      record.2.sender = who → record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    {Observation : Type} (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (source : ((rosterMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((rosterMenu setup leaks bounds rosters).decisionInformationAntichain (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
      (fun who site => source.truncatedContinuationContext site (fun final => base final.state who)
        (2 * (rosterPlan setup rosters).length + 1))) :
    let deposit := rosterAuditDeposit setup leaks bounds rosters network base probability
    let audit := sourceServiceAudit setup leaks sample
    let observeAudit := (runtime setup).settlementObservation leaks
    let utility := TerminalAudit.utility base observeAudit audit deposit
    let settle := TerminalAudit.settlement base observeAudit audit deposit
    ∃ target : ((bounds.rawMenu (runtime setup) leaks).information (initialLaw setup)
        (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu (runtime setup) leaks).decisionInformationAntichain (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
        (fun who site => target.truncatedContinuationContext site (fun final => utility final.state
            who)
          (2 * (rosterPlan setup rosters).length + 1)) ∧
      (((bounds.rawMenu (runtime setup) leaks).information (initialLaw setup)
        (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).runBehavioral
          target.strategy (2 * (rosterPlan setup rosters).length + 1)).bind (fun final =>
            (settle final.state).map (fun payoffs => (observe final.state, payoffs))) =
        (((rosterMenu setup leaks bounds rosters).information (initialLaw setup)
          (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network)).runBehavioral source.strategy
            (2 * (rosterPlan setup rosters).length + 1)).map
              (fun final => (observe final.state, base final.state)) := by
  intro deposit audit observeAudit utility settle
  let effective := bounds.menu (runtime setup) leaks
  let retained := rosterMenu setup leaks bounds rosters
  let initial := initialLaw setup
  let count := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  let included := rosterMenu_in_effective setup leaks bounds rosters
  let payoff := fun who (history : (effective.protocol initial count scheduler).History) =>
    base history.state who
  let lower := fun who => FinitePayoffBounds.lower (payoff who)
  let upper := fun who => FinitePayoffBounds.upper (payoff who)
  choose depth clock using roster_menu_common_depth setup leaks rosters network effective
  have nonnegative (who : Player) : 0 ≤ deposit who :=
    div_nonneg (sub_nonneg.mpr (FinitePayoffBounds.lower_le_upper (payoff who))) (positive who).le
  have sufficient (who : Player) : upper who - probability who * deposit who ≤ lower who := by
    change upper who - probability who * ((upper who - lower who) / probability who) ≤ lower who
    rw [mul_div_cancel₀ _ (positive who).ne']
    linarith
  have completes (history : (effective.protocol initial count scheduler).History)
      (control : (application setup leaks).Control) (current : history.state = some control)
      (terminal : (application setup leaks).terminal history.state) :
      control.execution.application.config.cut.Terminal := by
    have rawTrace : ((application setup leaks).protocol initial count scheduler).Trace
        (some control) :=
      current ▸ effective.toRawTrace initial count scheduler history.trace
    exact rosterScheduler_completesPlay setup leaks rosters network control rawTrace
      (current ▸ terminal)
  have conforming (history : (retained.protocol initial count scheduler).History)
      (control : (application setup leaks).Control) (current : history.state = some control)
      (terminal : (application setup leaks).terminal history.state) :
      (∀ who, control.execution.application.publicView.missedBindingBy who = false) ∧
      ∀ record ∈ (application setup leaks).executionTraffic control.execution,
        ((runtime setup).settledRecord leaks control.execution).permits
          record.input.envelope = true := by
    refine ⟨control.execution.application.publicView.missedBindingBy_of_publications
      (reveal_publications setup reveals), ?_⟩
    obtain ⟨ledgerPermitted, published⟩ := roster_terminal_published setup leaks bounds rosters
      network reveals openable history control current terminal
    have rawTrace : ((application setup leaks).protocol initial count scheduler).Trace
        (some control) :=
      current ▸ retained.toRawTrace initial count scheduler history.trace
    have facts := settledFacts_history initial count scheduler rawTrace
    have inputs := (application setup leaks).stateTraffic_inputs initial count scheduler rawTrace
    change ((application setup leaks).executionTraffic control.execution).map
      ReactiveApplication.TrafficRecord.input = control.execution.network.inputs at inputs
    intro record member
    have inputMember : record.input ∈ control.execution.network.inputs := by
      rw [← inputs]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    obtain ⟨message, inLedger, sameId⟩ :=
      List.mem_map.mp (published record.input inputMember)
    have equal : message = record.input.envelope :=
      (facts.unique.inputs record.input inputMember).ledger message inLedger sameId
    rw [← equal]
    exact ledgerPermitted message inLedger
  exact settled_audited_raw_sequential_equilibrium setup leaks bounds count scheduler
    retained included completes (fun who site => depth who
      ((included.actionRestriction initial count scheduler).site who site))
    (fun who site => clock who ((included.actionRestriction initial count scheduler).site who site))
    sample authentic conforming
    (fun profile who site action extra history next supported => by
      obtain ⟨record, present, author, breach⟩ := roster_extra_choice_traffic setup leaks bounds
        rosters network reveals openable profile who site action extra history next supported
      refine ⟨record, present, author, ?_⟩
      cases verdict : (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope with
      | false => rfl
      | true =>
          have nodup := roster_traffic_ledger_nodup setup leaks rosters network
            (effective.toRawTrace initial count scheduler next.trace) record present
          have allowed := permittedRosterEnvelope_of_permittedService setup leaks reveals _ _ _
            nodup verdict
          change permittedRosterEnvelope setup leaks
            (record.observation, record.ledger, record.input.envelope) = false at breach
          rw [allowed] at breach
          cases breach)
    base baseInvariant lower upper probability deposit nonnegative
    (fun history who => FinitePayoffBounds.lower_le (payoff who)
      ((included.actionRestriction initial count scheduler).history history))
    (fun history who => FinitePayoffBounds.le_upper (payoff who) history) sufficient coverage
    observe observationInvariant source equilibrium

end Vegas
