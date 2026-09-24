/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationGuess
import Vegas.Pending.ReactiveContinuationObservation

/-! # The deterministic service tail contains no further player decisions -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeTailCommand (index : Nat) : EnvironmentCommand nativeGraph :=
  if index = 22 then .expire bindingEvent
  else if index = 33 then .expire dummyEvent
  else if index = 44 then .expire secretEvent
  else if index = 55 then .expire guessEvent
  else .advanceClock

theorem native_calendar_tail (index : Nat) (lower : 12 ≤ index) (upper : index < 56) :
    nativeCalendar index = .application (nativeTailCommand index) := by
  unfold nativeCalendar
  split <;> simp_all [nativeTailCommand]

theorem native_tail_maintenance (index : Nat) (event : nativeGraph.EventId) :
    nativeTailCommand index ≠ .executeSample event := by
  unfold nativeTailCommand
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> simp

def nativeTail : Nat → Nat → State nativeGraph → FinDist (State nativeGraph)
  | _, 0, state => FinDist.pure state
  | index, count + 1, state => (environmentStep nativeRuntime state (nativeTailCommand index)).bind
      (nativeTail (index + 1) count)

theorem native_run_tail (players : Bool → nativeApp.Policy) (count index : Nat)
    (execution : nativeApp.Execution) (position : execution.environmentRecall.length = index)
    (lower : 12 ≤ index) (upper : index + count ≤ 56) :
    (nativeApp.runRounds nativeScheduler players count execution).map
      ReactiveApplication.Execution.application = nativeTail index count execution.application := by
  induction count generalizing index execution with
  | zero => exact FinDist.map_pure _ _
  | succ count ih =>
      rw [ReactiveApplication.runRounds, ReactiveApplication.round,
        native_schedule execution (.application (nativeTailCommand index))
          (by rw [position]; exact native_calendar_tail index lower (by omega))]
      simp only [ReactiveApplication.uniformInstruction, FinDist.pure_bind,
        ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, FinDist.map_bind,
        ReactiveApplication.Execution.environmentStep, FinDist.bind_map, FinDist.bind_bind,
        nativeTail]
      apply FinDist.bind_congr
      intro next _
      apply ih
      · change (execution.environmentRecall ++ [_]).length = index + 1
        simp only [List.length_append, List.length_singleton, position]
      · omega
      · omega

theorem native_tail_views (index count : Nat) (left right : State nativeGraph)
    (views : left.playerView true = right.playerView true) :
    (nativeTail index count left).map (fun state => state.playerView true) =
      (nativeTail index count right).map (fun state => state.playerView true) := by
  induction count generalizing index left right with
  | zero => simpa only [nativeTail, FinDist.map_pure] using congrArg FinDist.pure views
  | succ count ih =>
      simp only [nativeTail, FinDist.map_bind]
      apply FinDist.bind_eq_of_map_eq _ _ _ _
        (maintenance_playerView_congr nativeRuntime left right true (nativeTailCommand index)
          (native_tail_maintenance index) views)
      intro next _ other _ same
      exact ih _ _ _ same

theorem native_tail_store (index count : Nat) (state next : State nativeGraph)
    (field : nativeGraph.Field) (value : (nativeGraph.layout field).Value)
    (stored : state.config.store field = some value)
    (reached : next ∈ (nativeTail index count state).support) :
    next.config.store field = some value := by
  induction count generalizing index state with
  | zero => cases FinDist.mem_support_pure.mp reached; exact stored
  | succ count ih =>
      obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      exact ih (index + 1) middle
        (environmentStep_store_of_some nativeRuntime state middle (nativeTailCommand index)
          supported field value stored) moved

theorem native_guess_views (left right : State nativeGraph)
    (views : left.playerView true = right.playerView true) : nativeGuess left = nativeGuess right :=
    by
  have stored := congrArg (fun view : PlayerView nativeGraph =>
    view.publicView.observation.store (.inr guessEvent)) views
  change nativeGraph.publicStore left.config.store (.inr guessEvent) =
    nativeGraph.publicStore right.config.store (.inr guessEvent) at stored
  rw [nativeGraph.publicStore_of_public left.config.store (.inr guessEvent) (by decide),
    nativeGraph.publicStore_of_public right.config.store (.inr guessEvent) (by decide)] at stored
  exact congrArg (fun value : Option (PublicationResult Bool) =>
    value.getD .failure |>.isSuccess) stored

theorem native_tail_guesses (index count : Nat) (left right : State nativeGraph)
    (views : left.playerView true = right.playerView true) :
    (nativeTail index count left).map nativeGuess =
      (nativeTail index count right).map nativeGuess := by
  rw [FinDist.map_eq_bind, FinDist.map_eq_bind]
  apply FinDist.bind_eq_of_map_eq _ _ _ _ (native_tail_views index count left right views)
  intro next _ other _ same
  exact congrArg FinDist.pure (native_guess_views next other same)

end VegasTests.SequentialValidation
