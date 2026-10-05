/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettledSound
import Vegas.Game.SourceServiceOmission
import Vegas.Game.SourceServiceLaw
import Vegas.Pending.ReactiveServiceAudit

/-! # Actual settlement on full-source compiled executions

The fixed service samples authentic signed packets, judges each against the
contract's settled record, and checks the record's missed-binding obligations.
No verdict reads when a packet was sent. Every retained history has zero
collection probability, including intermediate histories and correlated
private inputs. Consequently the compiled profile preserves the original joint
terminal-state and realized-payoff law. Incentives for arbitrary raw deviations
remain the separate continuation-repair obligation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Authenticated audit evidence: the contract's settled record and one signed
packet. Neither the broadcaster nor the time of transmission is part of it. -/
abbrev SettledEvidence (setup : Setup (Player := Player) (L := L)) :=
  SettledRecord (graph setup) × Message Player (WitnessedPacket (graph setup))

/-- A terminal audit of signed packets against the settled record and of public
binding omissions. The sample is authenticated separately; the verdict denotes
an actually collected charge under the declared inclusion and escrow service
contract. -/
def sourceServiceAudit
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup))) :=
  (runtime setup).serviceAudit leaks fun record =>
    (application setup leaks).sampledTrafficAudit
      (fun traffic => (record, traffic.envelope))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2) sample

/-- Soundness is over all retained histories, independently of the compiled
equilibrium. Partial monitoring needs authenticity but no positive coverage
assumption for this direction. -/
theorem sourceService_history_audit_clear
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History)
    (who : Player) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) history.state who = 0 := by
  obtain ⟨state, trace⟩ := history
  cases state with
  | none => exact (runtime setup).serviceAudit_charge_none leaks _ who
  | some control =>
      have noOmission := control.execution.application.publicView.missedBindingBy_clear
        (sourceService_history_no_omission setup leaks bounds values capacity rosters
          opportunities network control trace) who
      unfold sourceServiceAudit
      rw [(runtime setup).serviceAudit_charge, noOmission]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply (application setup leaks).sampledTrafficAudit_sound
      · exact authentic _
      · intro record member _
        exact sourceService_history_settled bounds values capacity opportunities network trace
          record member

/-- The joint settlement vector is exactly the base payoff on every legal
history, not just equal playerwise in expectation. -/
theorem sourceService_history_settlement
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History) :
    TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit history.state =
        PMF.pure (base history.state) :=
  TerminalAudit.settlement_clean base _ _ deposit history.state
    (sourceService_history_audit_clear setup leaks bounds values capacity rosters opportunities
      network sample authentic history)

/-- The full source compiler preserves the original typed outcome and actual
settlement jointly. This law requires no equilibrium assumption; the deposit
is arbitrary because permitted executions incur no charge. -/
theorem sourceServiceCompiledProfile_settlement_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let model := (sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    let settle := TerminalAudit.settlement (baseUtility setup leaks utility)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    (model.runBehavioral (sourceServiceCompiledProfile setup leaks bounds rosters network original)
      (2 * (rosterPlan setup rosters).length + 1)).bind (fun final =>
        (settle final.state).map fun payoffs => (sourceReadout setup leaks final.state, payoffs)) =
      (setup.run original).map (fun state => (some state, utility state)) := by
  intro model settle
  have bindingOpportunities := opportunities.binding
  let executions := model.runBehavioral
    (sourceServiceCompiledProfile setup leaks bounds rosters network original)
      (2 * (rosterPlan setup rosters).length + 1)
  have clean (history : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History) :
      settle history.state = PMF.pure (baseUtility setup leaks utility history.state) :=
    sourceService_history_settlement setup leaks bounds values capacity rosters
      bindingOpportunities network sample authentic _ deposit history
  change executions.bind _ = _
  have settled : executions.bind (fun final => (settle final.state).map
        (fun payoffs => (sourceReadout setup leaks final.state, payoffs))) =
      executions.map (fun final =>
        (sourceReadout setup leaks final.state, baseUtility setup leaks utility final.state)) := by
    simp only [clean, ← PMF.bind_pure_comp, Function.comp_def, PMF.pure_bind]
  rw [settled]
  have terminal := sourceServiceCompiledProfile_readout_law setup leaks bounds values initialValues
    capacity rosters opportunities network original permitted
  have joint := congrArg (PMF.map (fun state : Option (State L setup.program.terminalCtx) =>
    (state, fun who => state.elim 0 (fun final => utility final who)))) terminal
  change executions.map (fun final => (sourceReadout setup leaks final.state,
    fun who => (sourceReadout setup leaks final.state).elim 0
      (fun state => utility state who))) = _
  simpa only [PMF.map_comp, Function.comp_def, Option.elim_some,
    baseUtility, executions, model] using joint

end Vegas
