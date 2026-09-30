/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterEquilibrium
import Vegas.Game.RevealServiceRosterAudit

/-! # Original source SE in the audited full bounded revelation runtime

The compiler fixes the native game, service roster and range-based deposit
before selecting a source equilibrium. Every original source sequential
equilibrium has a native sequential equilibrium with the same joint typed
source outcome and realized settlement-payoff law. The authentic partial audit
and positive conditional coverage are explicit service assumptions.

The program is reveal-only and initial bindings are openable. Every owner has
at least one activation at its event; arbitrary other finite roster visits and
the original passive observation rule are retained. Fresh source commitments
and sampling require the full-source continuation proof.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_audited_source_sequential_equilibrium_preserved
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (rosterCoverage : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    [network.FiniteSupport]
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (EnvelopeEvidence setup leaks) → PMF (List (EnvelopeEvidence setup leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.2.sender = who →
      permittedRosterEnvelope setup leaks record = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.truncatedContinuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let base := baseUtility setup leaks utility
    let deposit := rosterAuditDeposit setup leaks extended rosters network base probability
    let audit := (application setup leaks).sampledTrafficAudit (envelopeEvidence setup leaks)
      (fun evidence => evidence.2.2.sender) (permittedRosterEnvelope setup leaks) sample
    let net := TerminalAudit.utility base (application setup leaks).stateTraffic audit deposit
    let settle := TerminalAudit.settlement base (application setup leaks).stateTraffic audit deposit
    let horizon := (rosterPlan setup rosters).length
    let scheduler := rosterScheduler setup leaks rosters network
    let model := (extended.rawMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler
    ∃ target : model.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((extended.rawMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun final => net final.state who) (2 * horizon + 1)) ∧
      (model.runBehavioral target.strategy (2 * horizon + 1)).bind
          (fun final => (settle final.state).map
            (fun payoffs => (sourceReadout setup leaks final.state, payoffs))) =
        ((setup.informationModel admission).runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
            (fun final => (setup.protocolReadout final.state,
              fun who => (setup.protocolReadout final.state).elim 0
                (fun state => utility state who))) := by
  classical
  intro extended base deposit audit net settle horizon scheduler model
  obtain ⟨retained, _compiled, retainedSE, sourceLaw⟩ :=
    roster_source_sequential_equilibrium_preserved setup leaks bounds rosters rosterCoverage network
      reveals openable admission utility source equilibrium
  obtain ⟨target, targetSE, targetLaw⟩ := roster_audited_sequential_equilibrium setup leaks extended
    rosters network reveals openable base (baseUtility_normalization setup leaks utility)
    sample authentic probability positive coverage (sourceReadout setup leaks)
    (sourceReadout_normalization setup leaks) retained retainedSE
  have jointLaw := congrArg (fun law => law.map (fun output =>
    (output, fun who => output.elim 0 (fun state => utility state who)))) sourceLaw
  simp only [PMF.map_comp, Function.comp_def] at jointLaw
  exact ⟨target, targetSE, targetLaw.trans jointLaw⟩

end Vegas
