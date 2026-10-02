/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceSignedCompilation

/-! # Source sequential equilibrium under the settled terminal audit

Fix a revelation program, bounded response alphabet, service calendar, declared
utilities and settlement service. Its fixed range-based deposits preserve every
original source sequential equilibrium, with the exact joint typed
terminal-state and realized settlement-payoff law in the full raw game.

Settlement happens once the declared service horizon ends. It observes an
authentic partial sample of signed packets with the contract's settled record,
judges each packet against that record, and collects the indicated deductions.
Its uniform record-coverage bound is explicit. Neither the broadcaster nor the
time of transmission is part of the evidence, so the watcher's silence is not a
monitored obligation: the full raw game restores public packet copies for every
player (`Vegas.signed_audit_source_sequential_equilibrium_preserved`). No
passive-reading coverage, strategic reporting policy or zero-utility player is
assumed for enforcement. The settlement lottery occurs after strategic play and
adds no earlier player observation.

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

include reveals observer openable in
/-- One audited native game and deposit vector implement every original source
SE. Utilities may depend on persistent private initial data as well as results. -/
theorem audited_source_sequential_equilibrium_preserved
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
                (fun state => utility state who))) :=
  signed_audit_source_sequential_equilibrium_preserved setup leaks bounds watcher reveals observer
    openable admission utility sample authentic probability positive coverage source equilibrium

end Vegas
