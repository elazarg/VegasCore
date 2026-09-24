/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationSelection
import VegasTests.SequentialValidationTail

/-! # The complete effect of Bob's last response -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeChosenState (execution : nativeApp.Execution) (action : nativeApp.Action) :
    State nativeGraph :=
  match action.transmission with
  | some (.submit submission) =>
      let submitted := nativeApp.submit execution.application true submission
      if submission.packet.event? nativeGraph = some guessEvent then
        (handle nativeRuntime submitted
          ⟨(true, execution.network.nextSerial true), submission.packet⟩).getD submitted
      else submitted
  | _ => execution.application

theorem native_chosen_views (left right : nativeApp.Execution) (action : nativeApp.Action)
    (views : left.application.playerView true = right.application.playerView true) :
    (nativeChosenState left action).playerView true =
      (nativeChosenState right action).playerView true := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact views
  | some transmission =>
      cases transmission with
      | replay id => exact views
      | submit submission =>
          have submitted := submit_playerView_congr nativeRuntime nativeLeaks
            left.application right.application true submission views
          simp only [nativeChosenState]
          split
          · exact handle_result_playerView_congr nativeRuntime _ _ true _ _ _ submitted
          · exact submitted

theorem native_bob_fresh_lookup (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (empty : control.execution.recall true = [])
    (submission : Submission nativeGraph) :
    (control.execution.respond nativeApp true ⟨some (.submit submission)⟩).network.lookup
      (true, control.execution.network.nextSerial true) =
        some ⟨(true, control.execution.network.nextSerial true), submission.packet⟩ := by
  have absent : (control.execution.network.pending.find? fun message =>
      decide (message.id = (true, control.execution.network.nextSerial true))) = none := by
    apply List.find?_eq_none.mpr
    intro message member same
    exact native_no_bob_pending control trace empty message member
      (congrArg Prod.fst (of_decide_eq_true same))
  simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit, MessageNetwork.lookup,
    List.find?_append, absent, List.find?_cons, decide_true]
  rfl

theorem native_bob_round (bit : Bool) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some true)
    (empty : control.execution.recall true = [])
    (views : control.execution.application.playerView true =
      (nativeBobExecution bit).application.playerView true)
    (players : Bool → nativeApp.Policy) (action : nativeApp.Action) :
    (nativeApp.round nativeScheduler players
      (control.execution.respond nativeApp true action)).map
        ReactiveApplication.Execution.application =
          FinDist.pure (nativeChosenState control.execution action) := by
  rw [ReactiveApplication.round, native_bob_selection bit control trace active empty views,
    FinDist.pure_bind]
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [nativeFinalCommand, ReactiveApplication.dispatch,
        ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.pure_bind]
      rfl
  | some transmission =>
      cases transmission with
      | replay id =>
          simp only [nativeFinalCommand, ReactiveApplication.dispatch,
            ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
            ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.pure_bind]
          rfl
      | submit submission =>
          by_cases address : submission.packet.event? nativeGraph = some guessEvent
          · simp only [nativeFinalCommand, address, ↓reduceIte, ReactiveApplication.dispatch,
              ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
              ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.pure_bind]
            simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
              native_bob_fresh_lookup control trace empty submission]
            simp only [nativeChosenState, address, ↓reduceIte]
            rfl
          · simp only [nativeFinalCommand, address, ↓reduceIte, ReactiveApplication.dispatch,
              ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
              ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.pure_bind,
              nativeChosenState]
            rfl

theorem native_round_length (players : Bool → nativeApp.Policy)
    (execution next : nativeApp.Execution)
    (reached : next ∈ (nativeApp.round nativeScheduler players execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  rw [nativeApp.dispatch_environmentRecall players command execution next supported,
    List.length_append, List.length_singleton]

theorem native_bob_response_tail (bit : Bool) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some true)
    (empty : control.execution.recall true = [])
    (views : control.execution.application.playerView true =
      (nativeBobExecution bit).application.playerView true)
    (players : Bool → nativeApp.Policy) (action : nativeApp.Action) :
    (nativeApp.runRounds nativeScheduler players 45
      (control.execution.respond nativeApp true action)).map
        ReactiveApplication.Execution.application =
          nativeTail 12 44 (nativeChosenState control.execution action) := by
  rw [show 45 = 44 + 1 from rfl, ReactiveApplication.runRounds, FinDist.map_bind]
  have position := (native_bob_remaining control trace active).1
  calc
    _ = (nativeApp.round nativeScheduler players
          (control.execution.respond nativeApp true action)).bind
            (fun next => nativeTail 12 44 next.application) := by
      apply FinDist.bind_congr
      intro next reached
      apply native_run_tail players 44 12 next _ (by omega) (by omega)
      rw [native_round_length players _ next reached, nativeApp.respond_environmentRecall, position]
    _ = _ := by
      rw [← FinDist.bind_map, native_bob_round bit control trace active empty views,
        FinDist.pure_bind]

theorem native_chosen_guess (bit guess : Bool) :
    nativeChosenState (nativeBobExecution bit) ⟨some (.submit (nativeGuessSubmission guess))⟩ =
      { nativeGuessState bit guess with serviceGrant := some guessEvent } := by
  have addressed : (nativeGuessSubmission guess).packet.event? nativeGraph = some guessEvent := by
    cases guess <;> rfl
  simp only [nativeChosenState, addressed, ↓reduceIte]
  change (nativeSubmit (nativeBobExecution bit).application true
    ((nativeBobExecution bit).network.nextSerial true) (nativeGuessSubmission guess)).getD _ = _
  rw [native_bob_application, native_guess_grant]
  rfl

theorem native_chosen_store (execution : nativeApp.Execution) (action : nativeApp.Action)
    (field : nativeGraph.Field) (value : (nativeGraph.layout field).Value)
    (stored : execution.application.config.store field = some value) :
    (nativeChosenState execution action).config.store field = some value := by
  let invariant := nativeRuntime.reactiveStoreInvariant nativeLeaks field value
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact stored
  | some transmission =>
      cases transmission with
      | replay id => exact stored
      | submit submission =>
          have submitted := invariant.submit execution.application true submission stored
          simp only [nativeChosenState]
          split
          · cases accepted : handle nativeRuntime (nativeApp.submit execution.application true
                submission) ⟨(true, execution.network.nextSerial true), submission.packet⟩ with
            | none => exact submitted
            | some next =>
                exact handle_store_of_some nativeRuntime _ next _ accepted field value submitted
          · exact submitted

theorem native_tail_guess (bit guess : Bool) :
    (nativeTail 12 44
      (nativeChosenState (nativeBobExecution bit)
        ⟨some (.submit (nativeGuessSubmission guess))⟩)).map nativeGuess = FinDist.pure guess := by
  rw [native_chosen_guess]
  calc
    _ = (nativeTail 12 44 { nativeGuessState bit guess with
          serviceGrant := some guessEvent }).map (fun _ => guess) := by
      apply FinDist.map_congr_of_eq_on_support
      intro next reached
      have stored := native_tail_store 12 44 _ next (.inr guessEvent)
        (if guess then .success true else .failure) rfl reached
      unfold nativeGuess
      rw [stored]
      cases guess <;> rfl
    _ = _ := FinDist.map_const _ _

end VegasTests.SequentialValidation
