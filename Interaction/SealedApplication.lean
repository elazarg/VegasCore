/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication
import Interaction.SealedExecution

/-! # Sealed programs over the shared message runtime

The application accepts the sealed program's validated events and records
public acceptance/rejection receipts. Registration is principal-local;
arbitrary payloads, delivery, and replay use the shared message operations.
There are no application environment commands, deadlines, or progress
assumptions. Erasing receipts gives the untimed native reference semantics;
that projection alone is not a strategic or observation equivalence.
-/

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

structure ApplicationState (Principal : Type uPrincipal) (Value : Type uValue) where
  service : IdealCommitments Principal Nat Value
  events : List (Event Principal Value)

noncomputable def messageApplication [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) : MessageApplication Principal where
  Application := ApplicationState Principal Value
  Payload := Payload Principal Value
  PrivateCommand := ULift.{uPrincipal} (Nat × Value)
  EnvironmentCommand := ULift.{max uPrincipal uValue} Empty
  PlayerView := List (Event Principal Value)
  EnvironmentView := List (Event Principal Value)
  privateStep state owner command :=
    { state with service := (state.service.sealValue owner command.down.1 command.down.2).state }
  environmentStep _ command := nomatch command.down
  handle state message := (program.validateMessage? state.service state.events message).map
    fun event => { state with events := state.events ++ [event] }
  observePlayer state _ := state.events
  observeEnvironment state := state.events

def eraseReceipts [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (state : (program.messageApplication (Value := Value)).State) : State Principal Value :=
  ⟨state.application.service, state.pool, state.application.events⟩

def nativeAction [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) :
    (program.messageApplication (Value := Value)).Action → Action Principal Value
  | .privateCommand owner command => .register owner command.down.1 command.down.2
  | .submit author payload => .submit author payload
  | .replay who id => .replay who id
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .environment command => nomatch command.down

theorem step_eraseReceipts [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (state : (program.messageApplication (Value := Value)).State)
    (action : (program.messageApplication (Value := Value)).Action) :
    ((program.messageApplication (Value := Value)).step state action).map
        (program.eraseReceipts) =
      FinDist.pure (program.step (program.eraseReceipts state) (program.nativeAction action)) := by
  cases action with
  | privateCommand | submit | replay | deliver =>
      simp only [MessageApplication.step, FinDist.map_pure]
      rfl
  | environment command => exact nomatch command.down
  | «include» id =>
      simp only [MessageApplication.step, FinDist.map_pure, MessageApplication.includePending,
        MessagePool.includeApplication, messageApplication, eraseReceipts, nativeAction,
        step, includePending, handle]
      generalize state.pool.includePending id = included
      cases included with
      | mk message pool =>
          cases message with
          | none => rfl
          | some message =>
              dsimp only
              cases program.validateMessage? state.application.service
                  state.application.events message <;> rfl

theorem run_eraseReceipts [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (state : (program.messageApplication (Value := Value)).State)
    (actions : List (program.messageApplication (Value := Value)).Action) :
    ((program.messageApplication (Value := Value)).run actions state).map
        (program.eraseReceipts) =
      FinDist.pure (program.run (program.eraseReceipts state)
        (actions.map (program.nativeAction))) := by
  induction actions generalizing state with
  | nil => simp
  | cons action rest ih =>
      simp only [MessageApplication.run_cons, FinDist.map_bind, List.map_cons, run_cons]
      simp_rw [ih]
      rw [← FinDist.bind_map (program.eraseReceipts)
        ((program.messageApplication (Value := Value)).step state action)
        (fun next => FinDist.pure (program.run next (rest.map program.nativeAction))),
        program.step_eraseReceipts,
        FinDist.pure_bind]

end Interaction.SealedProgram
