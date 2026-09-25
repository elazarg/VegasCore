/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingEquilibrium

/-! # A fixed playerwise translation for the monitored guessing game

Only Bob's own source policy determines his native completion. Alice's opening
policy and Watcher's reporting policy are fixed. The completion is chosen once
for each receiver mixture and fixed deposit; it does not inspect other source
strategies or their beliefs. This is a semantic, noncomputable translation for
this game, with no claim of general deviation transport or effective synthesis.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

private def completion (deposit : ℝ) (sufficient : 2 ≤ deposit) (guesses : FinDist Bool) :
    nativeModel.BehavioralAssessment :=
  (exists_native_sequential_equilibrium guesses deposit sufficient).choose

private theorem completion_facts (deposit : ℝ) (sufficient : 2 ≤ deposit)
    (guesses : FinDist Bool) :
    (completion deposit sufficient guesses).strategy alice = nativeAliceBehavior ∧
    (completion deposit sufficient guesses).strategy watcher = nativeWatcherBehavior ∧
    (completion deposit sufficient guesses).strategy bob quietBobSite.1 =
      nativeGuessBehavior guesses quietBobSite.1 ∧
    (completion deposit sufficient guesses).IsSequentialEquilibriumFor nativeAntichain
      (fun who site => (completion deposit sufficient guesses).continuationContext site
        (fun history => nativeUtility deposit who history.state) (2 * nativeHorizon + 1)) :=
  (exists_native_sequential_equilibrium guesses deposit sufficient).choose_spec

/-- Each translated policy has only that player's source policy as an input.
The fixed target game and deposit are shared by every source equilibrium. -/
def compileNative (deposit : ℝ) (sufficient : 2 ≤ deposit) :
    (who : Player) → sourceModel.BehavioralPolicy who → nativeModel.BehavioralPolicy who :=
  Fin.cases (fun _ => nativeAliceBehavior)
    (Fin.cases (fun policy =>
      (completion deposit sufficient
        ((policy sourceBobSite.1).map (fun choice => OwnAction.disclosure choice.1))).strategy bob)
      (Fin.cases (fun _ => nativeWatcherBehavior) (fun i => i.elim0)))

private theorem compiled_profile (deposit : ℝ) (sufficient : 2 ≤ deposit)
    (profile : Profile sourceModel.behavioralSignature) :
    Profile.map (sig := sourceModel.behavioralSignature)
        (target := nativeModel.behavioralSignature) (compileNative deposit sufficient) profile =
      (completion deposit sufficient (sourceDecisionLaw profile bob sourceBobSite.1)).strategy := by
  funext who
  fin_cases who
  · exact (completion_facts deposit sufficient _).1.symm
  · change (completion deposit sufficient
      ((profile bob sourceBobSite.1).map (fun choice => OwnAction.disclosure choice.1))).strategy
        bob = _
    have law : (profile bob sourceBobSite.1).map
        (fun choice => OwnAction.disclosure choice.1) =
        sourceDecisionLaw profile bob sourceBobSite.1 := by
      simp only [sourceDecisionLaw, sourceChoice, FinDist.map_comp, Function.comp_def]
    rw [law]
    rfl
  · exact (completion_facts deposit sufficient _).2.1.symm

/-- Every source sequential equilibrium admits consistent target beliefs for
this one fixed playerwise policy translation, preserving the exact joint law
of initial secret, public results and actual net payoff vector. -/
theorem compiled_source_equilibrium (deposit : ℝ) (sufficient : 2 ≤ deposit)
    (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (sourcePayoff who) 3)) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.strategy = Profile.map (sig := sourceModel.behavioralSignature)
        (target := nativeModel.behavioralSignature) (compileNative deposit sufficient)
          source.strategy ∧
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
  let target := completion deposit sufficient
    (sourceDecisionLaw source.strategy bob sourceBobSite.1)
  obtain ⟨alicePolicy, watcherPolicy, atQuiet, nativeEquilibrium⟩ :=
    completion_facts deposit sufficient (sourceDecisionLaw source.strategy bob sourceBobSite.1)
  exact ⟨target, (compiled_profile deposit sufficient source.strategy).symm, nativeEquilibrium,
    native_source_joint_payoffs deposit source equilibrium target.strategy
      alicePolicy watcherPolicy atQuiet⟩

end VegasTests.MonitoredGuessing
