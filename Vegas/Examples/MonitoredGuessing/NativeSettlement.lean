/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeCollection
import Vegas.Examples.MonitoredGuessing.NativeTerminalSupport
import Vegas.Examples.MonitoredGuessing.NativePayoff
import Vegas.Examples.MonitoredGuessing.Assessment
import GameTheoryExtensions.Analysis.Protocol.TerminalPayoffCongruence

/-! # Sequential incentives and realized payoffs of physical settlement

Terminal collection has the comparison utility as its conditional expectation
at every legal terminal history, including histories after deviations. Thus
its continuation incentives inherit the proved equilibrium comparisons. The
initialized clean-play law also preserves the realized payoff vector exactly.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeSettledUtility (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ) (who : Player)
    (state : nativeApp.ProtocolState) : ℝ :=
  state.elim 0 fun control =>
    expect (nativeCollectionLaw window rate nonnegative bounded deposit control.execution)
      (fun result => result.2 who)

def nativeCollectedObservation (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (state : nativeApp.ProtocolState) : PMF (Bool × Results × (Player → ℝ)) :=
  state.elim (PMF.pure (false, ⟨.failure, .failure⟩, fun _ => 0)) fun control =>
    (nativeCollectionLaw window rate nonnegative bounded deposit control.execution).map
      (fun result => (observedAliceBit (control.execution.observe nativeApp alice), result))

theorem native_settled_terminal_utility_eq (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ) (who : Player)
    (history : nativeArena.History) (terminal : nativeArena.terminal history.state) :
    nativeSettledUtility window rate nonnegative bounded deposit who history.state =
      nativeComparisonUtility (rate * deposit) who history.state := by
  cases state : history.state with
  | none => rfl
  | some control =>
      have trace : nativeArena.Trace (some control) := state ▸ history.trace
      have finished : nativeArena.terminal (some control) := state ▸ terminal
      have raw := nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace
      exact nativeCollectionLaw_expected window rate nonnegative bounded deposit control.execution
        (nativeReceipts_history control raw)
        (nativeApp.uniqueIds_history nativeScheduler nativeInitialLaw nativeHorizon control raw)
        (nativeApp.publishedOnce_history nativeScheduler nativeInitialLaw nativeHorizon raw)
        (native_terminal_control_complete control trace finished) who

theorem native_settled_equilibrium_iff (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (assessment : nativeModel.BehavioralAssessment) :
    assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.truncatedContinuationContext site
          (fun history => nativeComparisonUtility (rate * deposit) who history.state)
          (2 * nativeHorizon + 1)) ↔
      assessment.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        assessment.truncatedContinuationContext site
          (fun history => nativeSettledUtility window rate nonnegative bounded deposit who
            history.state) (2 * nativeHorizon + 1)) := by
  let horizon := nativeMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler
  exact assessment.isSequentialEquilibriumFor_iff_of_bounded_terminal_payoff_eq
    nativeAntichain horizon.wellFoundedHistories horizon _ _ (fun who history terminal =>
      (native_settled_terminal_utility_eq window rate nonnegative bounded deposit who history
        terminal).symm)

theorem native_initialized_terminal (profile : Profile nativeModel.behavioralSignature)
    (history : nativeArena.History)
    (supported : history ∈ (nativeModel.runBehavioral profile
      (2 * nativeHorizon + 1)).support) : nativeArena.terminal history.state := by
  let horizon := nativeMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler
  rw [InformationModel.runBehavioral,
    ← nativeModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      horizon.wellFoundedHistories horizon] at supported
  exact nativeModel.runBehavioralTerminalFrom_support_terminal horizon.wellFoundedHistories
    profile nativeArena.initHistory history supported

theorem native_initialized_collection_eq_payoffs (window : ChallengeWindow) (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (deposit : ℝ)
    (profile : Profile nativeModel.behavioralSignature) (guesses : PMF Bool)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (watcherPolicy : profile watcher = nativeWatcherBehavior)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1) :
    (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).bind
        (fun history => nativeCollectedObservation window rate nonnegative bounded deposit
          history.state) =
      (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
        (fun history => nativePayoffObservation (rate * deposit) history.state) := by
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro history supported
  change nativeCollectedObservation window rate nonnegative bounded deposit history.state =
    PMF.pure (nativePayoffObservation (rate * deposit) history.state)
  have actual : nativeObservation history.state ∈
      (((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
        nativeObservation).support := by
    exact PMF.support_map .. ▸ ⟨history.state,
      PMF.support_map .. ▸ ⟨history, supported, rfl⟩, rfl⟩
  rw [native_initialized_observation profile guesses alicePolicy watcherPolicy atQuiet,
    PMF.support_bind] at actual
  obtain ⟨bit, _, sampled⟩ := Set.mem_iUnion₂.mp actual
  obtain ⟨guess, _, observed⟩ := PMF.support_map .. ▸ sampled
  obtain ⟨execution, state, complete⟩ := native_terminal_history_complete history
    (native_initialized_terminal profile history supported)
  have trace : nativeArena.Trace (nativeApp.finished execution) := state ▸ history.trace
  have raw := nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace
  have clean : aliceLiability execution = false := by
    have equality := congrArg (fun observation : Bool × Results × Bool => observation.2.2)
      observed
    simpa only [state, nativeApp, ReactiveApplication.finished, nativeObservation,
      Option.elim_some, nativeExecutionObservation, guessingObservation] using equality.symm
  rw [state]
  change (nativeCollectionLaw window rate nonnegative bounded deposit execution).map _ = _
  rw [nativeCollectionLaw_clean window rate nonnegative bounded deposit execution
    (nativeReceipts_history _ raw)
    (nativeApp.uniqueIds_history nativeScheduler nativeInitialLaw nativeHorizon _ raw)
    (nativeApp.publishedOnce_history nativeScheduler nativeInitialLaw nativeHorizon raw)
    complete clean, PMF.pure_map]
  simp only [ReactiveApplication.finished, nativePayoffObservation, nativeObservation,
    Option.elim_some,
    nativeExecutionObservation, nativeComparisonUtility, nativeComparisonExecutionUtility,
    clean, Bool.false_eq_true, and_false, ↓reduceIte, sub_zero]
end Vegas.Examples.MonitoredGuessing
