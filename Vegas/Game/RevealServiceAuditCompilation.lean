/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEquilibrium
import Vegas.Pending.ReactiveAuditEquilibrium
import Vegas.Game.RevealServiceAuditDeposits
import Vegas.Game.RevealServiceTrafficDeparture
import Vegas.Game.RevealServiceTrafficSound

/-! # Source sequential equilibrium under an authenticated terminal audit

Fix a revelation program, bounded response alphabet, service calendar, declared
utilities and terminal audit service. Its fixed range-based deposits preserve
every original source sequential equilibrium, with the exact joint typed
terminal-state and realized settlement-payoff law in the full raw game.

The audit observes an authentic partial record of transmission phases,
broadcasters and prior ledger states, and collects the indicated deductions.
Its uniform record-coverage bound is explicit. No passive-reading coverage,
strategic reporting policy or zero-utility player is assumed for enforcement.
The final settlement lottery occurs after strategic play and adds no earlier
player observation. Envelope signatures alone do not authenticate a
rebroadcaster or its transmission phase.

The service still has one owner and one auxiliary activation per source event,
with protected inclusion and bounded expiry. Initial bindings are openable;
fresh source commitments and arbitrary intervening activations require separate
correspondence proofs. The result is forward preservation, not reflection or
uniqueness of the target equilibrium.
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
  [Finite (setup.executionProtocol admission).History]
  [∀ who (site : (setup.informationModel admission).InformationSite who),
    Fintype ((setup.informationModel admission).InformationHistory who site.1)]

include reveals observer openable in
/-- One audited native game and deposit vector implement every original source
SE. Utilities may depend on persistent private initial data as well as results. -/
theorem audited_source_sequential_equilibrium_preserved
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (application setup leaks).TrafficRecord →
      FinDist (List (application setup leaks).TrafficRecord))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.input.broadcaster = who →
      permittedTraffic setup leaks watcher record = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let base := baseUtility setup leaks utility
    let deposit := auditRangeDeposit setup leaks extended watcher base probability
    let audit := (application setup leaks).sampledTrafficAudit id (fun record =>
      record.input.broadcaster)
      (permittedTraffic setup leaks watcher) sample
    let net := TerminalAudit.utility base (application setup leaks).stateTraffic audit deposit
    let settle := TerminalAudit.settlement base (application setup leaks).stateTraffic audit deposit
    let model := rawInformation setup leaks extended watcher
    ∃ target : model.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((extended.rawMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.continuationContext site
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
  intro extended base deposit audit net settle model
  obtain ⟨retained, _compiled, retainedSE, sourceLaw⟩ :=
    source_sequential_equilibrium_preserved setup leaks bounds watcher reveals observer openable
      admission utility source equilibrium
  have sufficient (who : Player) :
      auditPayoffUpper setup leaks extended watcher base who - probability who * deposit who ≤
        auditPayoffLower setup leaks extended watcher base who := by
    have bound := auditRangeDeposit_sufficient setup leaks extended watcher base probability
      positive who
    change _ - _ ≤ probability who * deposit who at bound
    linarith
  obtain ⟨target, targetSE, targetLaw⟩ := extended.audited_raw_sequential_equilibrium
    (runtime setup) leaks (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    (menu setup leaks extended watcher) (menu_in_effective setup leaks extended watcher)
    (fun who site => decisionDepth setup leaks watcher who site.1)
    (menu_common_decision_depth setup leaks (extended.menu (runtime setup) leaks) watcher
      reveals observer)
    id (fun record => record.input.broadcaster)
    (permittedTraffic setup leaks watcher) sample authentic
    (retained_history_traffic setup leaks extended watcher reveals observer openable)
    (extra_choice_traffic setup leaks extended watcher reveals observer openable)
    base (baseUtility_normalization setup leaks utility)
    (auditPayoffLower setup leaks extended watcher base)
    (auditPayoffUpper setup leaks extended watcher base) probability deposit
    (auditRangeDeposit_nonnegative setup leaks extended watcher base probability positive)
    (retained_auditPayoffLower_le setup leaks extended watcher base)
    (le_auditPayoffUpper setup leaks extended watcher base) sufficient coverage
    (sourceReadout setup leaks) (sourceReadout_normalization setup leaks) retained retainedSE
  exact ⟨target, targetSE, targetLaw.trans sourceLaw⟩

end Vegas
