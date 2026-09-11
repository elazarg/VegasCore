/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedApplication
import Interaction.MessageApplicationProjection
import Interaction.MessageApplicationMessageInvariant

/-! # Observation and policy projection for activation-relative applications

The projection drops activation metadata from the current state and every
remembered polling observation. Wire data, receipts, and commands are retained.
Lifted policies use those projected observations; arbitrary window-aware
policies remain available in the concrete runtime.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

def eraseState (runtime : WindowedApplication P L) (state : runtime.application.State) :
    runtime.image.orderedApplication.State :=
  ⟨state.application.base, state.pool, state.receipts⟩

def eraseView (runtime : WindowedApplication P L) (view : runtime.application.View) :
    runtime.image.orderedApplication.View :=
  ⟨view.messages, view.application.1, view.receipts⟩

def eraseEnvironmentView (runtime : WindowedApplication P L)
    (view : runtime.application.EnvironmentObservation) :
    runtime.image.orderedApplication.EnvironmentObservation :=
  ⟨view.pool, view.application.1, view.receipts⟩

def erasePlayerCommand (runtime : WindowedApplication P L) :
    runtime.application.PlayerCommand → runtime.image.orderedApplication.PlayerCommand
  | .privateCommand command => .privateCommand command
  | .submit payload => .submit payload
  | .replay id => .replay id
  | .wait => .wait

def liftPlayerCommand (runtime : WindowedApplication P L) :
    runtime.image.orderedApplication.PlayerCommand → runtime.application.PlayerCommand
  | .privateCommand command => .privateCommand command
  | .submit payload => .submit payload
  | .replay id => .replay id
  | .wait => .wait

def eraseEnvironmentCommand (runtime : WindowedApplication P L) :
    runtime.application.EnvironmentPolicyCommand →
      runtime.image.orderedApplication.EnvironmentPolicyCommand
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def liftEnvironmentCommand (runtime : WindowedApplication P L) :
    runtime.image.orderedApplication.EnvironmentPolicyCommand →
      runtime.application.EnvironmentPolicyCommand
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def eraseAction (runtime : WindowedApplication P L) :
    runtime.application.Action → runtime.image.orderedApplication.Action
  | .privateCommand who command => .privateCommand who command
  | .submit who payload => .submit who payload
  | .replay who id => .replay who id
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .environment command => .environment command

def erasePlayerEntry (runtime : WindowedApplication P L)
    (entry : runtime.application.PlayerEntry) : runtime.image.orderedApplication.PlayerEntry :=
  ⟨runtime.eraseView entry.beforeView, runtime.erasePlayerCommand entry.command⟩

def eraseEnvironmentEntry (runtime : WindowedApplication P L)
    (entry : runtime.application.EnvironmentEntry) :
    runtime.image.orderedApplication.EnvironmentEntry :=
  ⟨runtime.eraseEnvironmentView entry.beforeView, runtime.eraseEnvironmentCommand entry.command⟩

def eraseExecution (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) :
    runtime.image.orderedApplication.PolicyExecution :=
  ⟨runtime.eraseState execution.native,
    fun who => (execution.principalHistory who).map runtime.erasePlayerEntry,
    execution.environmentHistory.map runtime.eraseEnvironmentEntry,
    execution.nativeTrace.map runtime.eraseAction⟩

/-- A mathematical policy embedding, not emitted player software. -/
def liftPlayerPolicy (runtime : WindowedApplication P L)
    (policy : runtime.image.orderedApplication.PlayerPolicy) : runtime.application.PlayerPolicy :=
  fun history view =>
    (policy (history.map runtime.erasePlayerEntry) (runtime.eraseView view)).map
      runtime.liftPlayerCommand

def liftEnvironmentPolicy (runtime : WindowedApplication P L)
    (policy : runtime.image.orderedApplication.EnvironmentPolicy) :
    runtime.application.EnvironmentPolicy :=
  fun history view =>
    (policy (history.map runtime.eraseEnvironmentEntry) (runtime.eraseEnvironmentView view)).map
      runtime.liftEnvironmentCommand

@[simp] theorem erase_lift_playerCommand (runtime : WindowedApplication P L)
    (command : runtime.image.orderedApplication.PlayerCommand) :
    runtime.erasePlayerCommand (runtime.liftPlayerCommand command) = command := by
  cases command <;> rfl

@[simp] theorem erase_lift_environmentCommand (runtime : WindowedApplication P L)
    (command : runtime.image.orderedApplication.EnvironmentPolicyCommand) :
    runtime.eraseEnvironmentCommand (runtime.liftEnvironmentCommand command) = command := by
  cases command <;> rfl

@[simp] theorem erase_observe (runtime : WindowedApplication P L)
    (state : runtime.application.State) (who : P) :
    runtime.eraseView (MessageApplication.State.observe runtime.application state who) =
      MessageApplication.State.observe runtime.image.orderedApplication
        (runtime.eraseState state) who := rfl

@[simp] theorem erase_environmentView (runtime : WindowedApplication P L)
    (state : runtime.application.State) :
    runtime.eraseEnvironmentView
      (MessageApplication.State.environmentView runtime.application state) =
      MessageApplication.State.environmentView runtime.image.orderedApplication
        (runtime.eraseState state) := rfl

@[simp] theorem erase_initial (runtime : WindowedApplication P L)
    (base : ApplicationImage.State P L) :
    runtime.eraseExecution
      (PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (runtime.initial base))) =
      PolicyExecution.initial runtime.image.orderedApplication
        (MessageApplication.State.initial runtime.image.orderedApplication base) := rfl

end Vegas.WindowedApplication
