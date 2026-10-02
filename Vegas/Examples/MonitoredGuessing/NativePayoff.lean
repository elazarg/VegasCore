/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeLaw
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Joint preservation of the private bit, public results, and comparison payoffs

The native vector below uses `nativeComparisonUtility`, including the evidence charge.
The source vector uses the payoff function of the checked source equilibrium;
`source_settlement_eq_utility` connects it to the program's integer returns.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativePayoffObservation (charge : ℝ) (state : nativeApp.ProtocolState) :
    Bool × Results × (Player → ℝ) :=
  ((nativeObservation state).1, (nativeObservation state).2.1,
    fun who => nativeComparisonUtility charge who state)

def sourcePayoffObservation (state : sourceArena.State) :
    Bool × Results × (Player → ℝ) :=
  ((sourceObservation state).1, (sourceObservation state).2.1, sourceUtility state)

def observationPayoffs (charge : ℝ) (observation : Bool × Results × Bool) :
    Bool × Results × (Player → ℝ) :=
  (observation.1, observation.2.1, fun who => utility observation.2.1 who -
    if who = alice ∧ observation.2.2 then charge else 0)

def guessingPayoffs (bit guess : Bool) : Bool × Results × (Player → ℝ) :=
  (bit, ⟨.success bit, guessResult guess⟩,
    utility ⟨.success bit, guessResult guess⟩)

theorem native_some_payoffs (charge : ℝ) (control : nativeApp.Control) :
    nativePayoffObservation charge (some control) =
      observationPayoffs charge (nativeObservation (some control)) := rfl

theorem observation_guessing_payoffs (charge : ℝ) (bit guess : Bool) :
    observationPayoffs charge (guessingObservation bit guess) = guessingPayoffs bit guess := by
  simp only [observationPayoffs, guessingObservation, guessingPayoffs, Bool.false_eq_true,
    and_false, ↓reduceIte, sub_zero]

theorem source_done_payoffs (bit guess : Bool) :
    sourcePayoffObservation (SourcePath.done bit guess true).state = guessingPayoffs bit guess :=
    by cases bit <;> cases guess <;> rfl

theorem native_initialized_some (profile : Profile nativeModel.behavioralSignature)
    (state : nativeApp.ProtocolState)
    (supported : state ∈ ((nativeModel.runBehavioral profile
      (2 * nativeHorizon + 1)).map History.state).support) :
    ∃ control, state = some control := by
  rw [InformationModel.runBehavioral, nativeMenu.run_eq_finish nativeInitialLaw nativeHorizon
    nativeScheduler profile (2 * nativeHorizon + 1) nativeArena.initHistory (by rfl)] at supported
  change state ∈ (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler _ none).support
    at supported
  obtain ⟨initial, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨final, _, rfl⟩ := PMF.support_map .. ▸ reached
  exact ⟨_, rfl⟩

theorem native_initialized_payoffs (charge : ℝ)
    (profile : Profile nativeModel.behavioralSignature) (guesses : PMF Bool)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (watcherPolicy : profile watcher = nativeWatcherBehavior)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1) :
    ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
      (nativePayoffObservation charge) = (PMF.uniformOfFintype Bool).bind (fun bit =>
        guesses.map (guessingPayoffs bit)) := by
  have observationLaw := native_initialized_observation profile guesses alicePolicy watcherPolicy
    atQuiet
  calc
    _ = (((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
        nativeObservation).map (observationPayoffs charge) := by
      conv_rhs => rw [PMF.map_comp]
      apply map_congr_on_support _
      intro state supported
      obtain ⟨control, rfl⟩ := native_initialized_some profile state supported
      exact native_some_payoffs charge control
    _ = _ := by
      rw [observationLaw]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        observation_guessing_payoffs]

theorem source_equilibrium_payoffs (assessment : sourceModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      assessment.truncatedContinuationContext site (sourcePayoff who) 3)) :
    ((sourceModel.runBehavioral assessment.strategy 3).map History.state).map
      sourcePayoffObservation = (PMF.uniformOfFintype Bool).bind (fun bit =>
        (sourceDecisionLaw assessment.strategy bob sourceBobSite.1).map (guessingPayoffs bit)) := by
  rw [source_equilibrium_states assessment equilibrium]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, source_done_payoffs]

/-- The source payoff vector equals the native comparison vector on initialized
compiled play. Physical collection adequacy is established in `NativeSettlement`. -/
theorem native_source_joint_payoffs (charge : ℝ)
    (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.truncatedContinuationContext site (sourcePayoff who) 3))
    (target : Profile nativeModel.behavioralSignature)
    (alicePolicy : target alice = nativeAliceBehavior)
    (watcherPolicy : target watcher = nativeWatcherBehavior)
    (atQuiet : target bob quietBobSite.1 =
      nativeGuessBehavior (sourceDecisionLaw source.strategy bob sourceBobSite.1) quietBobSite.1) :
    (nativeModel.runBehavioral target (2 * nativeHorizon + 1)).map
      (fun history => ((nativeObservation history.state).1,
        (nativeObservation history.state).2.1,
          fun who => nativeComparisonUtility charge who history.state)) =
    (sourceModel.runBehavioral source.strategy 3).map
      (fun history => ((sourceObservation history.state).1,
        (sourceObservation history.state).2.1, fun who => sourcePayoff who history)) := by
  have native := native_initialized_payoffs charge target
    (sourceDecisionLaw source.strategy bob sourceBobSite.1) alicePolicy watcherPolicy atQuiet
  have original := source_equilibrium_payoffs source equilibrium
  have same := native.trans original.symm
  simpa only [PMF.map_comp, Function.comp_def, nativePayoffObservation,
    sourcePayoffObservation, sourcePayoff] using same

end Vegas.Examples.MonitoredGuessing
