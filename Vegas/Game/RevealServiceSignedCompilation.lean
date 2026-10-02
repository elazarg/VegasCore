/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEquilibrium
import Vegas.Game.RevealServiceAuditDeposits
import Vegas.Game.RevealServiceSignedDeparture
import Vegas.Game.RevealServiceReplayExtension
import Vegas.Game.RevealServiceClean
import Vegas.Game.ServiceSettledAudit

/-! # Source sequential equilibrium from settled signed-packet evidence

One fixed full bounded native game preserves every original reveal-only source
SE and its joint typed outcome/realized settlement law. Public packet copies
remain lawful for every player. Settlement happens once the declared service
horizon ends: it samples authentic signed packets and judges each against the
contract's settled record. It never authenticates a rebroadcaster or the time of
transmission. The settlement sample's conditional coverage and actual
collection are explicit assumptions.
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
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)

include reveals observer openable in
/-- One audited native game and deposit vector implement every original source
SE. Utilities may depend on persistent private initial data as well as results. -/
theorem signed_audit_source_sequential_equilibrium_preserved
    [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual (record : SettledEvidence setup), record ∈ actual →
      record.2.sender = who → record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.truncatedContinuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let base := baseUtility setup leaks utility
    let deposit := auditRangeDeposit setup leaks extended watcher base probability
    let audit := sourceServiceAudit setup leaks sample
    let observe := (runtime setup).settlementObservation leaks
    let net := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    let model := rawInformation setup leaks extended watcher
    ∃ target : model.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((extended.rawMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.truncatedContinuationContext site
          (fun final => net final.state who) (2 * horizon setup watcher + 1)) ∧
      (model.runBehavioral target.strategy (2 * horizon setup watcher + 1)).bind
          (fun final => (settle final.state).map
            (fun payoffs => (sourceReadout setup leaks final.state, payoffs))) =
        ((setup.informationModel admission).runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
            (fun final => (setup.protocolReadout final.state,
              fun who => (setup.protocolReadout final.state).elim 0
                (fun state => utility state who))) := by
  classical
  intro extended base deposit audit observe net settle model
  obtain ⟨retained, _compiled, retainedSE, sourceLaw⟩ :=
    source_sequential_equilibrium_preserved setup leaks bounds watcher reveals observer openable
      admission utility source equilibrium
  let appPayoff (state : Option (application setup leaks).State) (who : Player) : ℝ :=
    (state.bind (fun native => if native.config.cut.Terminal then
      Vegas.decodeState? (Vegas.terminalRefs setup.program) native.config.store
        else none)).elim 0 (fun final => utility final who)
  have factors (state : (application setup leaks).ProtocolState) (who : Player) :
      appPayoff (state.map (fun control => control.execution.application)) who =
        base state who := by
    cases state <;> rfl
  have originalSE : retained.IsSequentialEquilibriumFor
      ((menu setup leaks extended watcher).decisionInformationAntichain (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher))
      (fun who site => retained.truncatedContinuationContext site
        (fun final => appPayoff (final.state.map
          (fun control => control.execution.application)) who)
        (2 * horizon setup watcher + 1)) := by
    simpa only [factors] using retainedSE
  obtain ⟨replayed, replayedSE, _paired, replayLaw⟩ := replay_equilibrium_extends setup leaks
    extended watcher reveals observer openable appPayoff retained originalSE
  have replayedBase := replayedSE
  simp only [factors] at replayedBase
  have sufficient (who : Player) :
      auditPayoffUpper setup leaks extended watcher base who - probability who * deposit who ≤
        auditPayoffLower setup leaks extended watcher base who := by
    have bound := auditRangeDeposit_sufficient setup leaks extended watcher base probability
      positive who
    change _ - _ ≤ probability who * deposit who at bound
    linarith
  let menuProtocol := (replayMenu setup leaks extended watcher).protocol (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)
  have completes (history : ((extended.menu (runtime setup) leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
      (control : (application setup leaks).Control) (current : history.state = some control)
      (terminal : (application setup leaks).terminal history.state) :
      control.execution.application.config.cut.Terminal := by
    obtain ⟨execution, finishedEq, settled⟩ := terminal_history_settled setup leaks
      (extended.menu (runtime setup) leaks) watcher reveals history terminal
    rw [current] at finishedEq
    obtain rfl := Option.some.inj finishedEq
    exact settled
  have conforming (history : menuProtocol.History) (control : (application setup leaks).Control)
      (current : history.state = some control)
      (terminal : (application setup leaks).terminal history.state) :
      (∀ who, control.execution.application.publicView.missedBindingBy who = false) ∧
      ∀ record ∈ (application setup leaks).executionTraffic control.execution,
        ((runtime setup).settledRecord leaks control.execution).permits
          record.input.envelope = true := by
    refine ⟨control.execution.application.publicView.missedBindingBy_of_publications
      (reveal_publications setup reveals), ?_⟩
    obtain ⟨original, first, originalState, same⟩ := replay_history_counterpart setup leaks
      extended watcher reveals observer openable history control current
    have originalTerminal : (protocol setup leaks extended watcher).terminal original.state := by
      rw [current] at terminal
      rw [originalState]
      exact terminal
    obtain ⟨execution, finishedEq, ledgerPermitted, inputsPublished⟩ :=
      terminal_history_published setup leaks extended watcher reveals observer openable original
        originalTerminal
    rw [originalState] at finishedEq
    have firstEq : first = execution :=
      Option.some.inj (congrArg (Option.map ReactiveApplication.Control.execution) finishedEq)
    subst firstEq
    have recordEq : (runtime setup).settledRecord leaks control.execution =
        (runtime setup).settledRecord leaks first := by
      unfold settledRecord
      rw [same.applicationEq, same.receipts]
    have published : ∀ input ∈ control.execution.network.inputs,
        input.envelope.id ∈ control.execution.network.ledger.map Message.id := by
      intro input member
      by_cases watches : input.broadcaster = watcher
      · exact same.watcherPublished input member watches
      · have filtered : input ∈ control.execution.network.inputs.filter
            (fun input => input.broadcaster ≠ watcher) :=
          List.mem_filter.mpr ⟨member, decide_eq_true watches⟩
        rw [← same.inputs] at filtered
        rw [← same.ledger]
        exact inputsPublished input (List.mem_filter.mp filtered).1
    have rawTrace : ((application setup leaks).protocol (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control) :=
      current ▸ (replayMenu setup leaks extended watcher).toRawTrace (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) history.trace
    have facts := settledFacts_history (initialLaw setup) _ _ rawTrace
    have inputs := (application setup leaks).stateTraffic_inputs (initialLaw setup) _ _ rawTrace
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
    rw [← equal, recordEq]
    exact ledgerPermitted message (same.ledger ▸ inLedger)
  obtain ⟨target, targetSE, targetLaw⟩ := settled_audited_raw_sequential_equilibrium setup leaks
    extended (horizon setup watcher) (scheduler setup leaks watcher)
    (replayMenu setup leaks extended watcher) (replay_in_effective setup leaks extended watcher)
    completes
    (fun who site => decisionDepth setup leaks watcher who site.1)
    (fun who site => menu_common_decision_depth setup leaks (extended.menu (runtime setup) leaks)
      watcher reveals observer who
      (((replay_in_effective setup leaks extended watcher).actionRestriction
        (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).site who
          site))
    sample authentic conforming
    (fun profile who site action extra history next supported => by
      obtain ⟨record, present, author, breach⟩ := replay_extra_choice_traffic setup leaks
        extended watcher reveals observer openable profile who site action extra history next
          supported
      refine ⟨record, present, author, ?_⟩
      cases verdict : (runtime setup).permittedServiceEnvelope record.observation record.ledger
          record.input.envelope with
      | false => rfl
      | true =>
          have allowed := permittedEnvelope_of_permittedService setup leaks reveals _ _ _ verdict
          change permittedEnvelope setup leaks
            (record.observation, record.ledger, record.input.envelope) = false at breach
          rw [allowed] at breach
          cases breach)
    base (baseUtility_normalization setup leaks utility)
    (auditPayoffLower setup leaks extended watcher base)
    (auditPayoffUpper setup leaks extended watcher base) probability deposit
    (auditRangeDeposit_nonnegative setup leaks extended watcher base probability positive)
    (fun history who => auditPayoffLower_le setup leaks extended watcher base
      (((replay_in_effective setup leaks extended watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).history history) who)
    (le_auditPayoffUpper setup leaks extended watcher base) sufficient coverage
    (sourceReadout setup leaks) (sourceReadout_normalization setup leaks) replayed replayedBase
  have joint := congrArg (fun law => law.map (fun final =>
    (sourceReadout setup leaks final.state, base final.state))) replayLaw
  rw [PMF.map_comp] at joint
  exact ⟨target, targetSE, targetLaw.trans (joint.symm.trans sourceLaw)⟩

end Vegas
