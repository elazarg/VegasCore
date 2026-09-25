/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeHonest
import VegasTests.MonitoredGuessingSourceEquilibrium

/-! # Joint initialized outcome and liability laws in the actual native game -/

noncomputable section
namespace VegasTests.MonitoredGuessing
open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeExecutionObservation (execution : nativeApp.Execution) : Bool × Results × Bool :=
  (observedAliceBit (execution.observe nativeApp alice),
    nativeResults execution.application.config, rejectedAlice execution.receipts)

def nativeObservation (state : nativeApp.ProtocolState) : Bool × Results × Bool :=
  state.elim (false, ⟨.failure, .failure⟩, false)
    (fun control => nativeExecutionObservation control.execution)

def sourceObservation (state : sourceArena.State) : Bool × Results × Bool :=
  match state with
  | some (.inr (.inr config)) =>
      ((config.state.get (.there (.there .here))).getD false, sourceResults config.state, false)
  | _ => (false, ⟨.failure, .failure⟩, false)

def guessingObservation (bit guess : Bool) : Bool × Results × Bool :=
  (bit, ⟨.success bit, guessResult guess⟩, false)

theorem source_done_observation (bit guess : Bool) :
    sourceObservation (SourcePath.done bit guess true).state = guessingObservation bit guess := by
  cases bit <;> cases guess <;> rfl

theorem quiet_guess_suffix_observation (players : Player → nativeApp.Policy)
    (prescribed : players alice = nativeAlicePolicy) (bit guess : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      (quietGuessRespond bit guess)).map nativeExecutionObservation =
      FinDist.pure (guessingObservation bit guess) := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := FinDist.support_map .. ▸ supported
  have summarized : (nativeResults final.application.config, rejectedAlice final.receipts) =
      (Results.mk (.success bit) (guessResult guess), false) := by
    apply FinDist.mem_support_pure.mp
    rw [← quiet_guess_suffix_summary players prescribed bit guess, FinDist.support_map]
    exact ⟨final, reached, rfl⟩
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) _
    (quietGuessRespond bit guess) final
    ((native_fixed_invariant bit).respond (quietBob bit) bob (nativeGuessAction guess)
      (quiet_bob_fixed bit)) reached
  unfold nativeExecutionObservation guessingObservation
  rw [native_observed_alice_bit bit final fixed]
  exact congrArg (Prod.mk bit) summarized

theorem native_finish_quiet (players : Player → nativeApp.Policy)
    (alicePolicy : players alice = nativeAlicePolicy)
    (watcherPolicy : players watcher = nativeWatcherPolicy) :
    nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players none =
      (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
          (some ⟨9, some bob, quietBob bit⟩)) := by
  have stopped := nativeApp.finish_after_steps nativeInitialLaw nativeHorizon nativeScheduler
    players 8 (FinDist.pure none)
  rw [quiet_bob_control_law players alicePolicy watcherPolicy,
    FinDist.bind_map, FinDist.pure_bind] at stopped
  exact stopped.symm

theorem quiet_guess_policy (profile : Profile nativeModel.behavioralSignature)
    (guesses : FinDist Bool)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1)
    (bit : Bool) :
    nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile bob
      ((quietBob bit).recall bob) ((quietBob bit).observe nativeApp bob) =
        guesses.map nativeGuessAction := by
  have input : some ((quietBob bit).recall bob, (quietBob bit).observe nativeApp bob) =
      quietBobSite.1 := quiet_bob_info bit
  change ((profile bob _).map _).map _ = _
  rw [input, atQuiet, ← input]
  exact congrFun (congrFun (decode_native_guess guesses) ((quietBob bit).recall bob))
    ((quietBob bit).observe nativeApp bob)

theorem native_initialized_observation (profile : Profile nativeModel.behavioralSignature)
    (guesses : FinDist Bool)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (watcherPolicy : profile watcher = nativeWatcherBehavior)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1) :
    ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
      nativeObservation = (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        guesses.map (guessingObservation bit)) := by
  let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile
  have aliceEq : players alice = nativeAlicePolicy := by
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler alice (profile alice)) = _
    rw [alicePolicy, decode_native_alice]
  have watcherEq : players watcher = nativeWatcherPolicy := by
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler watcher (profile watcher)) = _
    rw [watcherPolicy, decode_native_watcher]
  rw [InformationModel.runBehavioral, nativeMenu.run_eq_finish nativeInitialLaw nativeHorizon
    nativeScheduler profile (2 * nativeHorizon + 1) nativeArena.initHistory (by rfl)]
  change (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players none).map _ = _
  rw [native_finish_quiet players aliceEq watcherEq, FinDist.map_bind]
  apply FinDist.bind_congr
  intro bit _
  have finishLaw := native_finish_response players
    [.player alice, .player watcher, .wire, .grant bobPublication]
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
      .grant alicePublication, .player alice] ++ resolutionTail) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
    (some ⟨9, some bob, quietBob bit⟩) = _ at finishLaw
  rw [finishLaw]
  have decision : players bob ((quietBob bit).recall bob)
      ((quietBob bit).observe nativeApp bob) = guesses.map nativeGuessAction :=
    quiet_guess_policy profile guesses atQuiet bit
  rw [decision]
  simp only [FinDist.bind_map, FinDist.map_bind, FinDist.map_comp]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro guess _
  exact quiet_guess_suffix_observation players aliceEq bit guess

theorem source_equilibrium_observation (assessment : sourceModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      assessment.continuationContext site (sourcePayoff who) 3)) :
    ((sourceModel.runBehavioral assessment.strategy 3).map History.state).map sourceObservation =
      (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        (sourceDecisionLaw assessment.strategy bob sourceBobSite.1).map
          (guessingObservation bit)) :=
    by
  rw [source_equilibrium_states assessment equilibrium]
  simp only [FinDist.map_bind, FinDist.map_comp, Function.comp_def, source_done_observation]

end VegasTests.MonitoredGuessing
