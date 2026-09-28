/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEquilibrium
import Vegas.Pending.ReactiveAuditEquilibrium
import Vegas.Game.RevealServiceAuditDeposits
import Vegas.Game.RevealServiceSignedDeparture
import Vegas.Game.RevealServiceReplayExtension

/-! # Source sequential equilibrium from signed-author terminal evidence

One fixed full bounded native game preserves every original reveal-only source
SE and its joint typed outcome/realized settlement law. Public envelope replays
remain lawful for every player. The auditor authenticates the signed envelope,
its transmission phase and prior ledger, and never authenticates a rebroadcaster.
The terminal audit is sampled after strategic play; its conditional coverage and
actual collection are explicit assumptions.
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
theorem signed_audit_source_sequential_equilibrium_preserved
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (EnvelopeEvidence setup leaks) →
      FinDist (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.2.sender = who →
      permittedEnvelope setup leaks record = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let base := baseUtility setup leaks utility
    let deposit := auditRangeDeposit setup leaks extended watcher base probability
    let audit := (application setup leaks).sampledTrafficAudit (envelopeEvidence setup leaks)
      (fun evidence => evidence.2.2.sender) (permittedEnvelope setup leaks) sample
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
      (fun who site => retained.continuationContext site
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
  obtain ⟨target, targetSE, targetLaw⟩ := extended.audited_raw_sequential_equilibrium
    (runtime setup) leaks (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    (replayMenu setup leaks extended watcher) (replay_in_effective setup leaks extended watcher)
    (fun who site => decisionDepth setup leaks watcher who site.1)
    (menu_common_decision_depth setup leaks (extended.menu (runtime setup) leaks) watcher
      reveals observer)
    (envelopeEvidence setup leaks) (fun evidence => evidence.2.2.sender)
    (permittedEnvelope setup leaks) sample authentic
    (replay_history_traffic setup leaks extended watcher reveals observer openable)
    (replay_extra_choice_traffic setup leaks extended watcher reveals observer openable)
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
  rw [FinDist.map_comp] at joint
  exact ⟨target, targetSE, targetLaw.trans (joint.symm.trans sourceLaw)⟩

end Vegas
