/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeHonest
import Vegas.Examples.MonitoredGuessing.SourceEquilibrium
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Joint initialized outcome and liability laws in the actual native game -/

noncomputable section
namespace Vegas.Examples.MonitoredGuessing
open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativeExecutionObservation (execution : nativeApp.Execution) : Bool × Results × Bool :=
  (observedAliceBit (execution.observe nativeApp alice),
    nativeResults execution.application.config, aliceLiability execution)

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
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication, .player alice] ++
        resolutionTail)
      (quietGuessRespond bit guess)).map nativeExecutionObservation =
      PMF.pure (guessingObservation bit guess) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  have summarized : (nativeResults final.application.config, aliceLiability final) =
      (Results.mk (.success bit) (guessResult guess), false) := by
    apply (PMF.mem_support_pure_iff _ _).mp
    rw [← quiet_guess_suffix_summary players prescribed bit guess, PMF.support_map]
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
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
          (some ⟨8, some bob, quietBob bit⟩)) := by
  have stopped := nativeApp.finish_after_steps nativeInitialLaw nativeHorizon nativeScheduler
    players 7 (PMF.pure none)
  rw [quiet_bob_control_law players (by intro bit; rw [alicePolicy]; rfl)
    (by intro bit; rw [watcherPolicy]; rfl),
    PMF.bind_map, PMF.pure_bind] at stopped
  exact stopped.symm

theorem quiet_guess_policy (profile : Profile nativeModel.behavioralSignature)
    (guesses : PMF Bool)
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
    (guesses : PMF Bool)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (watcherPolicy : profile watcher = nativeWatcherBehavior)
    (atQuiet : profile bob quietBobSite.1 = nativeGuessBehavior guesses quietBobSite.1) :
    ((nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map History.state).map
      nativeObservation = (PMF.uniformOfFintype Bool).bind (fun bit =>
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
  rw [native_finish_quiet players aliceEq watcherEq, PMF.map_bind]
  apply bind_congr_on_support _
  intro bit _
  have finishLaw := native_finish_response players
    [.player alice, .player watcher, .wire]
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication, .player alice] ++
      resolutionTail) bob rfl (quietBob bit) rfl
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
    (some ⟨8, some bob, quietBob bit⟩) = _ at finishLaw
  rw [finishLaw]
  have decision : players bob ((quietBob bit).recall bob)
      ((quietBob bit).observe nativeApp bob) = guesses.map nativeGuessAction :=
    quiet_guess_policy profile guesses atQuiet bit
  rw [decision]
  simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro guess _
  exact quiet_guess_suffix_observation players aliceEq bit guess

theorem source_equilibrium_observation (assessment : sourceModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      assessment.truncatedContinuationContext site (sourcePayoff who) 3)) :
    ((sourceModel.runBehavioral assessment.strategy 3).map History.state).map sourceObservation =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        (sourceDecisionLaw assessment.strategy bob sourceBobSite.1).map
          (guessingObservation bit)) :=
    by
  rw [source_equilibrium_states assessment equilibrium]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, source_done_observation]

end Vegas.Examples.MonitoredGuessing
