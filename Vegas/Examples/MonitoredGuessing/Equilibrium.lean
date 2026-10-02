/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeReceiverRationality
import Vegas.Examples.MonitoredGuessing.NativeInitialRationality
import Vegas.Examples.MonitoredGuessing.NativeResolutionFinal
import Vegas.Examples.MonitoredGuessing.NativePayoff

/-! # Sequential equilibrium in the actual monitored native game

The fixed native game uses the full bounded raw response menu and ordinary
passive observation. For every source guessing law, a common consistent
assessment completes receiver responses at all other information sites.
The prescribed sender and reporting watcher are rational at every native site.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

private theorem watcher_context_value (assessment : nativeModel.BehavioralAssessment)
    (site : nativeModel.InformationSite watcher) (charge : ℝ)
    (alternative : nativeModel.BehavioralPolicy watcher) :
    (assessment.truncatedContinuationContext site
      (fun history => nativeComparisonUtility charge watcher history.state)
        (2 * nativeHorizon + 1)).value alternative = 0 := by
  have zero : (fun history : nativeArena.History =>
      nativeComparisonUtility charge watcher history.state) = fun _ => 0 := by
    funext history
    cases history.state <;> simp only [nativeComparisonUtility, Option.elim,
      native_execution_utility_watcher]
  rw [zero, BehavioralAssessment.truncatedContinuationContext_value]
  exact expect_constant _ 0

/-- A single fixed charge works for every source mixture. Off-path receiver
responses are completed in the original native information model. -/
theorem exists_native_sequential_equilibrium (guesses : PMF Bool)
    (charge : ℝ) (sufficient : 2 ≤ charge) :
    ∃ assessment : nativeModel.BehavioralAssessment,
      assessment.strategy alice = nativeAliceBehavior ∧
      assessment.strategy watcher = nativeWatcherBehavior ∧
      assessment.strategy bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1 ∧
      assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.truncatedContinuationContext site
          (fun history => nativeComparisonUtility charge who history.state) (2 * nativeHorizon
            + 1)) := by
  obtain ⟨assessment, fixed, atQuiet, consistent, offQuiet⟩ :=
    exists_native_bob_completion (nativeBaseline guesses) quietBobSite (nativeComparisonUtility
      charge bob)
  have alicePolicy : assessment.strategy alice = nativeAliceBehavior :=
    fixed alice (by decide)
  have watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior :=
    fixed watcher (by decide)
  refine ⟨assessment, alicePolicy, watcherPolicy, atQuiet, ?_, consistent⟩
  intro who site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => payoffIntegrable_of_finite _ _).mpr fun alternative _ => ?_
  fin_cases who
  · change nativeModel.InformationSite alice at site
    rcases native_alice_site_cases site with ⟨bit, rfl⟩ | ⟨past, view, info, responded⟩
    · exact initial_alice_site_dominates charge sufficient assessment guesses
        alicePolicy watcherPolicy atQuiet bit alternative
    · exact resolution_final_site_dominates charge (by linarith) assessment alicePolicy
        site past view info responded alternative
  · change nativeModel.InformationSite bob at site
    by_cases quiet : site = quietBobSite
    · subst site
      exact quiet_receiver_site_dominates assessment consistent guesses charge alicePolicy
        watcherPolicy atQuiet alternative
    · exact (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
        (payoffIntegrable_of_finite _ _)).mp (offQuiet site quiet)
        alternative (Set.mem_univ _)
  · change nativeModel.InformationSite watcher at site
    exact le_of_eq ((watcher_context_value assessment site charge alternative).trans
      (watcher_context_value assessment site charge (assessment.strategy watcher)).symm)

/-- Every standard source sequential equilibrium has a standard native
sequential equilibrium with the same joint law of private initial bit,
public result and comparison payoff vector. The target game and expected charge
are fixed before selecting the source equilibrium. -/
theorem source_equilibrium_preserved (charge : ℝ) (sufficient : 2 ≤ charge)
    (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.truncatedContinuationContext site (sourcePayoff who) 3)) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        target.truncatedContinuationContext site
          (fun history => nativeComparisonUtility charge who history.state) (2 * nativeHorizon
            + 1)) ∧
      (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
        (fun history => ((nativeObservation history.state).1,
          (nativeObservation history.state).2.1,
          fun who => nativeComparisonUtility charge who history.state)) =
      (sourceModel.runBehavioral source.strategy 3).map
        (fun history => ((sourceObservation history.state).1,
          (sourceObservation history.state).2.1, fun who => sourcePayoff who history)) := by
  obtain ⟨target, alicePolicy, watcherPolicy, atQuiet, nativeEquilibrium⟩ :=
    exists_native_sequential_equilibrium
      (sourceDecisionLaw source.strategy bob sourceBobSite.1) charge sufficient
  exact ⟨target, nativeEquilibrium, native_source_joint_payoffs charge source equilibrium
    target.strategy alicePolicy watcherPolicy atQuiet⟩

end Vegas.Examples.MonitoredGuessing
