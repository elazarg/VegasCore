/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeReceiverRationality
import VegasTests.MonitoredGuessingNativeInitialRationality
import VegasTests.MonitoredGuessingNativeResolutionFinal
import VegasTests.MonitoredGuessingNativePayoff

/-! # Sequential equilibrium in the actual monitored native game

The fixed native game uses the full bounded raw response menu and ordinary
passive observation. For every source guessing law, a common consistent
assessment completes receiver responses at all other information sites.
The prescribed sender and reporting watcher are rational at every native site.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

private theorem watcher_context_value (assessment : nativeModel.BehavioralAssessment)
    (site : nativeModel.InformationSite watcher) (deposit : ℝ)
    (alternative : nativeModel.BehavioralPolicy watcher) :
    (assessment.continuationContext site
      (fun history => nativeUtility deposit watcher history.state)
        (2 * nativeHorizon + 1)).value alternative = 0 := by
  have zero : (fun history : nativeArena.History =>
      nativeUtility deposit watcher history.state) = fun _ => 0 := by
    funext history
    cases history.state <;> simp only [nativeUtility, Option.elim,
      native_execution_utility_watcher]
  rw [zero, BehavioralAssessment.continuationContext_value]
  exact FinDist.expect_const _ 0

/-- A single fixed deposit works for every source mixture. Off-path receiver
responses are completed in the original native information model. -/
theorem exists_native_sequential_equilibrium (guesses : FinDist Bool)
    (deposit : ℝ) (sufficient : 2 ≤ deposit) :
    ∃ assessment : nativeModel.BehavioralAssessment,
      assessment.strategy alice = nativeAliceBehavior ∧
      assessment.strategy watcher = nativeWatcherBehavior ∧
      assessment.strategy bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1 ∧
      assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.continuationContext site
          (fun history => nativeUtility deposit who history.state) (2 * nativeHorizon + 1)) := by
  obtain ⟨assessment, fixed, atQuiet, consistent, offQuiet⟩ :=
    exists_native_bob_completion (nativeBaseline guesses) quietBobSite deposit
  have alicePolicy : assessment.strategy alice = nativeAliceBehavior :=
    fixed alice (by decide)
  have watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior :=
    fixed watcher (by decide)
  refine ⟨assessment, alicePolicy, watcherPolicy, atQuiet, ?_, consistent⟩
  intro who site alternative _
  fin_cases who
  · change nativeModel.InformationSite alice at site
    rcases native_alice_site_cases site with ⟨bit, rfl⟩ | ⟨past, view, info, granted⟩
    · exact initial_alice_site_dominates deposit sufficient assessment guesses
        alicePolicy watcherPolicy atQuiet bit alternative
    · exact resolution_final_site_dominates deposit (by linarith) assessment alicePolicy
        site past view info granted alternative
  · change nativeModel.InformationSite bob at site
    by_cases quiet : site = quietBobSite
    · subst site
      exact quiet_receiver_site_dominates assessment consistent guesses deposit alicePolicy
        watcherPolicy atQuiet alternative
    · exact offQuiet site quiet alternative (Set.mem_univ _)
  · change nativeModel.InformationSite watcher at site
    exact le_of_eq ((watcher_context_value assessment site deposit alternative).trans
      (watcher_context_value assessment site deposit (assessment.strategy watcher)).symm)

/-- Every standard source sequential equilibrium has a standard native
sequential equilibrium with the same joint law of private initial bit,
public result and actual net payoff vector. The target game and deposit
are fixed before selecting the source equilibrium. -/
theorem source_equilibrium_preserved (deposit : ℝ) (sufficient : 2 ≤ deposit)
    (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (sourcePayoff who) 3)) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        target.continuationContext site
          (fun history => nativeUtility deposit who history.state) (2 * nativeHorizon + 1)) ∧
      (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
        (fun history => ((nativeObservation history.state).1,
          (nativeObservation history.state).2.1,
          fun who => nativeUtility deposit who history.state)) =
      (sourceModel.runBehavioral source.strategy 3).map
        (fun history => ((sourceObservation history.state).1,
          (sourceObservation history.state).2.1, fun who => sourcePayoff who history)) := by
  obtain ⟨target, alicePolicy, watcherPolicy, atQuiet, nativeEquilibrium⟩ :=
    exists_native_sequential_equilibrium
      (sourceDecisionLaw source.strategy bob sourceBobSite.1) deposit sufficient
  exact ⟨target, nativeEquilibrium, native_source_joint_payoffs deposit source equilibrium
    target.strategy alicePolicy watcherPolicy atQuiet⟩

end VegasTests.MonitoredGuessing
