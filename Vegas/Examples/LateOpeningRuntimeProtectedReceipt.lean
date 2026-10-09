/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeProtectedOpening
import Interaction.ReactiveResponseEvaluation

/-! # Actual protected receipts forced by terminal disclosure success

Only Alice's first authenticated envelope can complete her disclosure during
the protected service. Combining this origin fact with the raw continuation
obstruction identifies the actual accepting receipt forced by almost-sure
terminal success.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeProtectedReceipt

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
open LateOpeningRuntimeProtectedOpening

private def activated (state : app.State) : app.Execution :=
  recorded (ReactiveApplication.Execution.initial app state) (.activate alice) state

private theorem initial_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (state : app.State) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (ReactiveApplication.Execution.initial app state) =
        (players alice [] ((activated state).observe app alice)).map
          (fun response => (activated state).respond app alice response) := by
  rw [ReactiveApplication.round]
  change (PMF.pure (.activate alice : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    recorded_activation _ alice (by rfl), PMF.pure_bind]
  rfl

private theorem silence_selector (state : app.State) :
    latestAuthor alice (((activated state).respond app alice ⟨none⟩).observeEnvironment app) =
      .wait := rfl

private theorem submission_selector (state : app.State) (submission : app.Submission) :
    latestAuthor alice (((activated state).respond app alice
      ⟨some submission⟩).observeEnvironment app) = .include (alice, 0) := by
  unfold latestAuthor
  rfl

/-- Completion in the first two actual rounds is accompanied by acceptance
of Alice's first envelope, regardless of its raw syntax. -/
theorem protected_completed_has_receipt (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (state : app.State)
    (unfinished : aliceEvent ∉ state.config.cut.completed) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 2 (ReactiveApplication.Execution.initial app state)).support)
    (completed : aliceEvent ∈ execution.application.config.cut.completed) :
    ((alice, 0), true) ∈ execution.receipts := by
  obtain ⟨first, firstReached, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [initial_round, PMF.support_map] at firstReached
  obtain ⟨response, _, rfl⟩ := firstReached
  simp only [ReactiveApplication.runRounds, PMF.bind_pure] at continued
  change execution ∈ ((PMF.pure (latestAuthor alice
    (((activated state).respond app alice response).observeEnvironment app))).bind
      (fun command => app.dispatch players command
        ((activated state).respond app alice response))).support at continued
  rw [PMF.pure_bind] at continued
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      rw [silence_selector] at continued
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?] at continued
      rw [recorded_wait, PMF.pure_bind] at continued
      change execution ∈ (PMF.pure _).support at continued
      cases (PMF.mem_support_pure_iff _ _).mp continued
      exact (unfinished completed).elim
  | some submission =>
      rw [submission_selector] at continued
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind] at continued
      change execution ∈ (PMF.pure _).support at continued
      cases (PMF.mem_support_pure_iff _ _).mp continued
      let first := (activated state).respond app alice ⟨some submission⟩
      let packet := app.packet (app.submit state alice submission) alice [] submission
      have found : first.network.lookup (alice, 0) = some ⟨(alice, 0), packet⟩ := rfl
      have same : first.application.config = state.config :=
        (LateOpeningRuntimeService.runtime.reactive_respond_application
          leaks (activated state) alice ⟨some submission⟩).1
      change aliceEvent ∈ (first.includePending app (alice, 0)).application.config.cut.completed
        at completed
      change ((alice, 0), true) ∈ (first.includePending app (alice, 0)).receipts
      unfold ReactiveApplication.Execution.includePending
        MessageNetwork.includePending at completed ⊢
      rw [found] at completed ⊢
      change aliceEvent ∈ ((app.handle first.application ⟨(alice, 0), packet⟩).getD
        first.application).config.cut.completed at completed
      change ((alice, 0), true) ∈ [] ++ [((alice, 0),
        (app.handle first.application ⟨(alice, 0), packet⟩).isSome)]
      cases result : app.handle first.application ⟨(alice, 0), packet⟩ with
      | none =>
          rw [result, Option.getD_none, same] at completed
          exact (unfinished completed).elim
      | some next => simp only [Option.isSome_some, List.nil_append,
          List.mem_singleton]

/-- With unrestricted raw policies, almost-sure terminal Alice success forces
acceptance of her first envelope during protected inclusion. -/
theorem almost_sure_success_forces_protected_receipt (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (success : (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 26).map aliceSucceeded = PMF.pure true)
    (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 2).support) :
    ((alice, 0), true) ∈ execution.receipts := by
  have completed := almost_sure_success_forces_protected_completion weight nonnegative
    players success execution reached
  obtain ⟨state, supported, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have unfinished : aliceEvent ∉ state.config.cut.completed := by
    obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ supported
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId)
    simp
  exact protected_completed_has_receipt weight nonnegative players state unfinished
    execution continued completed

def protectedAccepted (execution : app.Execution) : Bool :=
  decide (((alice, 0), true) ∈ execution.receipts)

/-- The complete protected-receipt law is a point mass when terminal Alice
disclosure succeeds almost surely. -/
theorem almost_sure_success_protected_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (success : (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 26).map aliceSucceeded = PMF.pure true) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 2).map protectedAccepted = PMF.pure true := by
  calc
    _ = (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
        players 2).map (fun _ => true) := by
      apply map_congr_on_support
      intro execution reached
      exact decide_eq_true (almost_sure_success_forces_protected_receipt weight nonnegative
        players success execution reached)
    _ = _ := pmf_map_fun_const _ _

def stateSucceeded : app.ProtocolState → Bool
  | none => false
  | some control => aliceSucceeded control.execution

private theorem native_success_rounds (weight : ℝ) (nonnegative : 0 ≤ weight)
    (profile : ∀ who, (rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).BehavioralPolicy who)
    (success : ((rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).runBehavioralFrom profile
        (2 * LateOpeningRuntimeService.horizon + 1)
        (rawMenu.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).initHistory).map
            (fun history => stateSucceeded history.state) = PMF.pure true) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile) 26).map aliceSucceeded =
          PMF.pure true := by
  let builder := LateOpeningRuntimeService.scheduler weight nonnegative
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon builder profile
  let root := (rawMenu.protocol initial LateOpeningRuntimeService.horizon builder).initHistory
  have evaluated := rawMenu.run_eq_finish initial LateOpeningRuntimeService.horizon builder
    profile (2 * LateOpeningRuntimeService.horizon + 1) root (by exact le_refl _)
  have initialState : root.state = none := rfl
  rw [initialState] at evaluated
  calc
    _ = (app.finish initial LateOpeningRuntimeService.horizon builder players none).map
        stateSucceeded := by
      simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom,
        PMF.map_bind, PMF.map_comp, Function.comp_def]
      rfl
    _ = ((rawMenu.information initial LateOpeningRuntimeService.horizon builder).runBehavioralFrom
        profile (2 * LateOpeningRuntimeService.horizon + 1) root).map
          (fun history => stateSucceeded history.state) := by
      have mapped := congrArg (fun law : PMF app.ProtocolState => law.map stateSucceeded) evaluated
      simpa only [PMF.map_comp, Function.comp_def] using mapped.symm
    _ = _ := success

/-- In the actual bounded native game, every behavioral profile with
almost-sure terminal Alice success has almost-sure protected acceptance.
No equilibrium, audit, payoff or posterior hypothesis is required. -/
theorem native_almost_sure_success_protected_receipt_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (profile : ∀ who, (rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).BehavioralPolicy who)
    (success : ((rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).runBehavioralFrom profile
        (2 * LateOpeningRuntimeService.horizon + 1)
        (rawMenu.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).initHistory).map
            (fun history => stateSucceeded history.state) = PMF.pure true) :
    (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile) 2).map protectedAccepted =
          PMF.pure true :=
  almost_sure_success_protected_receipt_law weight nonnegative _
    (native_success_rounds weight nonnegative profile success)

end Vegas.Examples.LateOpeningRuntimeProtectedReceipt
