/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFinishedPayoff
import Vegas.Examples.CommitSeedSignallingRealization

/-! # Actual assessed payoff of a standing failed binding -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Once both declarations have completed, an owner's failed typed binding
gives payoff minus one under its unchanged assessed continuation. Completion,
permanent failure and zero charge are consequences of the actual native run. -/
theorem counted_failed_binding_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, none, execution⟩))
    (aliceDone : aliceBinding ∈ execution.application.current.native.config.cut.completed)
    (bobDone : bobBinding ∈ execution.application.current.native.config.cut.completed)
    (owner : Player)
    (failed : if owner = alice then
      execution.application.current.native.config.outputs aliceBinding = some .failure
      else execution.application.current.native.config.outputs bobBinding = some .failure) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state owner) = -1 := by
  classical
  let history : countedProtocol.History := ⟨some ⟨remaining, none, execution⟩, trace⟩
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have law := raw_terminal_state_law assessment.strategy
    (countedInRaw.history initial horizon scheduler history)
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
      (countedInRaw.history initial horizon scheduler history)).map History.state =
    app.finish initial horizon scheduler players (some ⟨remaining, none, execution⟩) at law
  rw [← law, expect_map, ← expect_constant _ (-1 : ℝ)]
  apply expect_congr_on_support
  intro final supported
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
  obtain ⟨countedFinal, _reached, same⟩ := retained
  have state := congrArg History.state same
  change countedFinal.state = final.state at state
  have physical : final.state ∈ ((rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy (countedInRaw.history initial horizon scheduler history)).map
        History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [law] at physical
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at physical
  obtain ⟨after, rounds, stateEq⟩ := PMF.support_map .. ▸ physical
  have terminal := rawModel.runBehavioralTerminalFrom_support_terminal canonicalCertificate
    assessment.strategy (countedInRaw.history initial horizon scheduler history) final supported
  have finalState : final.state = some (⟨0, none, after⟩ : app.Control) := stateEq.symm
  have finalTrace := rawMenu.toRawTrace initial horizon scheduler final.trace
  rw [finalState] at finalTrace terminal
  have complete := scheduler_completesPlay ⟨0, none, after⟩ finalTrace terminal
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun source _ => PhaseCount.countClean_initial runtime leaks source)
    countedFinal.trace
  rw [state, finalState] at clean
  have ownClean : OwnPermitted owner after :=
    ⟨clean.1, fun message member _ => clean.2 message member⟩
  have stillFailed := completed_binding_failure_persists scheduler players remaining remaining
    execution after (countedMenu.toRawTrace initial horizon scheduler trace) aliceDone bobDone
      rounds owner failed
  exact standing_bad_terminal_payoff final ⟨0, none, after⟩ finalState complete owner
    ownClean stillFailed

end Vegas.Examples.CommitSeedSignalling
