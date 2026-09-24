/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationResponse
import Interaction.ReactiveResponseEvaluation

/-! # Native continuation values are independent of off-path belief choices -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def nativePlayers (profile : Profile nativeModel.behavioralSignature) : Bool → nativeApp.Policy :=
  nativeMenu.decodeProfile nativeInitialLaw 56 nativeScheduler profile

def nativeAnswerLaw (bit : Bool) (action : nativeApp.Action) : FinDist Bool :=
  (nativeTail 12 44 (nativeChosenState (nativeBobExecution bit) action)).map nativeGuess

def nativeGuessLaw (profile : Profile nativeModel.behavioralSignature) (bit : Bool) :
    FinDist Bool :=
  (nativePlayers profile true [] ((nativeBobExecution bit).observe nativeApp true)).bind
    (nativeAnswerLaw bit)

def nativeProtocolGuess : nativeApp.ProtocolState → Bool
  | none => false
  | some control => nativeGuess control.execution.application

theorem native_bob_guesses (profile : Profile nativeModel.behavioralSignature) (bit : Bool)
    (history : nativeModel.InformationHistory true (nativeBobSite bit).1) :
    (nativeModel.runBehavioralFrom profile 113 history.1).map
      (fun result => nativeProtocolGuess result.state) = nativeGuessLaw profile bit := by
  obtain ⟨execution, state, _position, empty, view⟩ := native_bob_fibre bit history
  have trace : nativeArena.Trace (some ⟨45, some true, execution⟩) := state ▸ history.1.trace
  have views := native_bob_playerView bit _ trace view
  have run := nativeMenu.run_eq_finish nativeInitialLaw 56 nativeScheduler profile 113 history.1
    (by rw [state]; change 91 ≤ 113; omega)
  calc
    _ = ((nativeModel.runBehavioralFrom profile 113 history.1).map History.state).map
          nativeProtocolGuess := by rw [FinDist.map_comp]; rfl
    _ = (nativeApp.finish nativeInitialLaw 56 nativeScheduler (nativePlayers profile)
          history.1.state).map nativeProtocolGuess :=
        congrArg (fun law : FinDist nativeApp.ProtocolState => law.map nativeProtocolGuess) run
    _ = _ := by
      rw [state]
      simp only [ReactiveApplication.finish, ReactiveApplication.resume, ReactiveApplication.invoke,
        FinDist.map_comp, FinDist.map_bind, FinDist.bind_map]
      change (nativePlayers profile true (execution.recall true)
        (execution.observe nativeApp true)).bind (fun action =>
          (nativeApp.runRounds nativeScheduler (nativePlayers profile) 45
            (execution.respond nativeApp true action)).map
              (fun next => nativeGuess next.application)) = _
      rw [empty, view]
      apply FinDist.bind_congr
      intro action _
      have tail := native_bob_response_tail bit _ trace rfl empty views
        (nativePlayers profile) action
      have guessed := congrArg (fun law : FinDist (State nativeGraph) => law.map nativeGuess) tail
      rw [FinDist.map_comp] at guessed
      exact guessed.trans (native_tail_guesses 12 44 _ _ (native_chosen_views _ _ action views))

def nativeStateUtility (matchBit : Bool) (state : State nativeGraph) (who : Bool) : ℝ :=
  if who && ((state.config.store (.inr secretEvent)).getD .failure).isFailure then
    if (nativeGuess state == (state.config.store (.inl typeInput)).getD false) = matchBit
      then 1 else 0
  else 0

def nativeUtility (matchBit : Bool) : nativeApp.ProtocolState → Bool → ℝ
  | none, _ => 0
  | some control, who => nativeStateUtility matchBit control.execution.application who

def nativePayoff (matchBit : Bool) (who : Bool) (history : nativeArena.History) : ℝ :=
  nativeUtility matchBit history.state who

theorem native_bob_secret_failure (bit : Bool) (state : State nativeGraph)
    (views : state.playerView true = (nativeBobExecution bit).application.playerView true) :
    state.config.store (.inr secretEvent) = some .failure := by
  have stored := congrArg (fun view : PlayerView nativeGraph =>
    view.publicView.observation.store (.inr secretEvent)) views
  change nativeGraph.publicStore state.config.store (.inr secretEvent) =
    nativeGraph.publicStore (nativeBobExecution bit).application.config.store (.inr secretEvent)
    at stored
  rw [nativeGraph.publicStore_of_public _ (.inr secretEvent) (by decide),
    nativeGraph.publicStore_of_public _ (.inr secretEvent) (by decide)] at stored
  rw [stored, native_bob_application]
  exact native_secret_failure bit

theorem native_tail_utility (matchBit bit : Bool) (execution : nativeApp.Execution)
    (action : nativeApp.Action)
    (typeKnown : execution.application.config.store (.inl typeInput) = some bit)
    (failed : execution.application.config.store (.inr secretEvent) = some .failure) :
    (nativeTail 12 44 (nativeChosenState execution action)).expect
      (nativeStateUtility matchBit · true) =
        ((nativeTail 12 44 (nativeChosenState execution action)).map nativeGuess).expect
          (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0) := by
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro next reached
  have typeFixed := native_tail_store 12 44 _ next (.inl typeInput) bit
    (native_chosen_store execution action _ _ typeKnown) reached
  have failureFixed := native_tail_store 12 44 _ next (.inr secretEvent) .failure
    (native_chosen_store execution action _ _ failed) reached
  simp only [nativeStateUtility, typeFixed, failureFixed, Option.getD_some,
    PublicationResult.isFailure, Bool.and_self, ↓reduceIte]

theorem native_bob_value (profile : Profile nativeModel.behavioralSignature)
    (matchBit bit : Bool) (history : nativeModel.InformationHistory true (nativeBobSite bit).1) :
    (nativeModel.runBehavioralFrom profile 113 history.1).expect (nativePayoff matchBit true) =
      (nativeGuessLaw profile bit).expect fun guess =>
        if (guess == bit) = matchBit then (1 : ℝ) else 0 := by
  obtain ⟨execution, state, _position, empty, view⟩ := native_bob_fibre bit history
  have trace : nativeArena.Trace (some ⟨45, some true, execution⟩) := state ▸ history.1.trace
  have views := native_bob_playerView bit _ trace view
  have known := native_bob_type bit history
  rw [state] at known
  have failed := native_bob_secret_failure bit execution.application views
  have run := nativeMenu.run_eq_finish nativeInitialLaw 56 nativeScheduler profile 113 history.1
    (by rw [state]; change 91 ≤ 113; omega)
  calc
    _ = ((nativeModel.runBehavioralFrom profile 113 history.1).map History.state).expect
          (nativeUtility matchBit · true) := (FinDist.expect_map _ _ _).symm
    _ = (nativeApp.finish nativeInitialLaw 56 nativeScheduler (nativePlayers profile)
          history.1.state).expect (nativeUtility matchBit · true) :=
        congrArg (fun law : FinDist nativeApp.ProtocolState =>
          law.expect (nativeUtility matchBit · true)) run
    _ = _ := by
      rw [state]
      simp only [ReactiveApplication.finish, ReactiveApplication.resume, ReactiveApplication.invoke,
        FinDist.expect_map, FinDist.expect_bind]
      change (nativePlayers profile true (execution.recall true)
        (execution.observe nativeApp true)).expect
        (fun action => (nativeApp.runRounds nativeScheduler (nativePlayers profile) 45
          (execution.respond nativeApp true action)).expect
            (fun next => nativeStateUtility matchBit next.application true)) = _
      rw [empty, view]
      unfold nativeGuessLaw
      rw [FinDist.expect_bind]
      apply FinDist.expect_congr
      intro action _
      have tail := native_bob_response_tail bit _ trace rfl empty views
        (nativePlayers profile) action
      have utility := congrArg (fun law => law.expect (nativeStateUtility matchBit · true)) tail
      rw [FinDist.expect_map] at utility
      exact utility.trans ((native_tail_utility matchBit bit execution action known failed).trans
        (congrArg (fun law : FinDist Bool => law.expect
          (fun guess => if (guess == bit) = matchBit then (1 : ℝ) else 0))
            (native_tail_guesses 12 44 _ _ (native_chosen_views _ _ action views))))

end VegasTests.SequentialValidation
