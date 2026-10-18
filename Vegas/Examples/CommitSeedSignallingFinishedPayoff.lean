/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFinishedOwner
import Interaction.ReactiveRoundTrace

/-! # Actual assessed payoff after successful native disclosure -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem basePayoff_nonnegative_of_survives (current : app.Control) (owner : Player)
    (active : owner ∉ current.execution.application.current.excluded) :
    0 ≤ basePayoff (some current) owner := by
  change 0 ≤ phaseExclusionBase setup .concurrentReveals runtime leaks utility excludedPayoff
    (some current) owner
  rw [phaseExclusionBase_eq_readout setup .concurrentReveals runtime leaks utility excludedPayoff
    current owner active]
  cases read : phaseSourceReadout setup .concurrentReveals runtime leaks (some current) with
  | none => exact le_refl _
  | some source => exact (utility_mem_Icc source owner).1

/-- From any genuine counted prefix, the unchanged assessed raw continuation
has zero charge on every terminal history in its support. -/
theorem raw_equilibrium_counted_terminal_charge_zero
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy (countedInRaw.history initial horizon scheduler history)).support)
    (owner : Player) :
    TerminalAudit.charge app.stateTraffic audit final.state owner = 0 := by
  have retained := supported
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at retained
  have sameRun := (countedInRaw.actionRestriction initial horizon scheduler).runFrom_law
    (countedAssessmentProfile assessment) assessment.strategy
      (raw_equilibrium_extends_counted assessment equilibrium) (2 * horizon + 1) history
  change (countedModel.runBehavioralFrom (countedAssessmentProfile assessment)
      (2 * horizon + 1) history).map (countedInRaw.history initial horizon scheduler) =
    rawModel.runBehavioralFrom assessment.strategy (2 * horizon + 1)
      (countedInRaw.history initial horizon scheduler history) at sameRun
  rw [← sameRun, PMF.support_map] at retained
  obtain ⟨original, _reached, same⟩ := retained
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    scheduler evidenceService original owner
  have state := congrArg History.state same
  change original.state = final.state at state
  change TerminalAudit.charge app.stateTraffic audit original.state owner = 0 at zero
  rw [state] at zero
  exact zero

/-- The exact assessed physical continuation after the actual selected opening
has nonnegative expected net payoff. The proof keeps the original scheduler
and assessed foreign strategies and derives, rather than assumes, charge zero. -/
theorem counted_successful_opening_assessed_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining + 1, none, execution⟩))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ execution.network.inputs)
    (lookup : execution.network.lookup message.id = some message)
    (candidate : Handle graph) (raw : Raw simpleExpr)
    (opening : message.payload.packet.call = .opening (revealEvent owner) candidate raw)
    (request : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩)
    (timely : execution.application.current.native.WithinDeadline runtime (revealEvent owner))
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (selected : (.include message.id : app.Command) ∈
      (scheduler execution.environmentRecall (execution.observeEnvironment app)).support)
    (next : app.Execution)
    (included : next ∈ (execution.environmentStep app (.include message.id)).support) :
    0 ≤ expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, next⟩)) (fun state => netPayoff state owner) := by
  classical
  obtain ⟨nextTrace⟩ := countedMenu.trace_environment initial horizon scheduler remaining execution
    next (.include message.id) trace selected included
  let history : countedProtocol.History := ⟨some ⟨remaining, none, next⟩, nextTrace⟩
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have law := raw_terminal_state_law assessment.strategy
    (countedInRaw.history initial horizon scheduler history)
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
      (countedInRaw.history initial horizon scheduler history)).map History.state =
    app.finish initial horizon scheduler players (some ⟨remaining, none, next⟩) at law
  rw [← law, expect_map]
  apply expect_nonneg
  intro final supported
  have zero := raw_equilibrium_counted_terminal_charge_zero assessment equilibrium history final
    supported owner
  have stateSupported : final.state ∈ ((rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy (countedInRaw.history initial horizon scheduler history)).map
        History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [law] at stateSupported
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind]
    at stateSupported
  obtain ⟨after, rounds, stateEq⟩ := PMF.support_map .. ▸ stateSupported
  have active := counted_successful_opening_future_survives scheduler
    ⟨remaining + 1, none, execution⟩ trace owner message member lookup candidate raw opening request
      timely value stored next included scheduler players remaining after rounds
  change 0 ≤ basePayoff final.state owner -
    TerminalAudit.charge app.stateTraffic audit final.state owner * deposit owner
  rw [zero, zero_mul, sub_zero, ← stateEq]
  exact basePayoff_nonnegative_of_survives ⟨0, none, after⟩ owner active

end Vegas.Examples.CommitSeedSignalling
