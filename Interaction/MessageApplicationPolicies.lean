/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication
import GameTheory.Core.Form

/-! # Observation-local policies for message applications

The policy game follows a fixed finite invocation list. Each principal sees
the current principal projection and only its own sampled command history.
The environment sees the complete message pool and the application's explicit
environment projection. Native application randomness remains a `FinDist`
transition and is not collapsed into policy randomization.
-/

noncomputable section

namespace Interaction.MessageInterface

open GameTheory GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal}

inductive PlayerCommand (interface : MessageInterface Principal) where
  | privateCommand (command : interface.PrivateCommand)
  | submit (payload : interface.Payload)
  | replay (id : MessageId Principal)
  | wait

structure PlayerEntry (interface : MessageInterface Principal) where
  beforeView : View interface
  command : PlayerCommand interface

abbrev PlayerPolicy (interface : MessageInterface Principal) :=
  List (PlayerEntry interface) → View interface → FinDist (PlayerCommand interface)

/-- Environment-controlled wire and application triggers. The application
command selects a fixed kernel, not one of its stochastic outcomes. -/
inductive EnvironmentPolicyCommand (interface : MessageInterface Principal) where
  | deliver (observer : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | application (command : interface.EnvironmentCommand)
  | wait

structure EnvironmentEntry (interface : MessageInterface Principal) where
  beforeView : EnvironmentObservation interface
  command : EnvironmentPolicyCommand interface

abbrev EnvironmentPolicy (interface : MessageInterface Principal) :=
  List (EnvironmentEntry interface) → EnvironmentObservation interface →
    FinDist (EnvironmentPolicyCommand interface)

/-- Policy-facing bounded execution. The native action trace is proof-facing
and is not included in either observation projection. -/
structure PolicyExecution (interface : MessageInterface Principal) where
  native : State interface
  principalHistory : Principal → List (PlayerEntry interface)
  environmentHistory : List (EnvironmentEntry interface)
  nativeTrace : List (Action interface)

end Interaction.MessageInterface

namespace Interaction.MessageApplication

open GameTheory GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal}

abbrev PlayerCommand (app : MessageApplication Principal) :=
  MessageInterface.PlayerCommand app.toMessageInterface

abbrev PlayerEntry (app : MessageApplication Principal) :=
  MessageInterface.PlayerEntry app.toMessageInterface

abbrev PlayerPolicy (app : MessageApplication Principal) :=
  MessageInterface.PlayerPolicy app.toMessageInterface

abbrev EnvironmentPolicyCommand (app : MessageApplication Principal) :=
  MessageInterface.EnvironmentPolicyCommand app.toMessageInterface

abbrev EnvironmentEntry (app : MessageApplication Principal) :=
  MessageInterface.EnvironmentEntry app.toMessageInterface

abbrev EnvironmentPolicy (app : MessageApplication Principal) :=
  MessageInterface.EnvironmentPolicy app.toMessageInterface

abbrev PolicyExecution (app : MessageApplication Principal) :=
  MessageInterface.PolicyExecution app.toMessageInterface

inductive Invocation where
  | player (who : Principal)
  | environment

def Invocation.isEnvironment : @Invocation Principal → Bool
  | .player _ => false
  | .environment => true

variable (app : MessageApplication Principal)

def PolicyExecution.initial (state : app.State) : app.PolicyExecution :=
  ⟨state, fun _ => [], [], []⟩

def PlayerCommand.toAction (who : Principal) : app.PlayerCommand → Option app.Action
  | .privateCommand command => some (.privateCommand who command)
  | .submit payload => some (.submit who payload)
  | .replay id => some (.replay who id)
  | .wait => none

def EnvironmentPolicyCommand.toAction :
    app.EnvironmentPolicyCommand → Option app.Action
  | .deliver observer id => some (.deliver observer id)
  | .include id => some (.include id)
  | .application command => some (.environment command)
  | .wait => none

/-- Execute an optional native action, retaining the full stochastic kernel. -/
def advance [DecidableEq Principal] (execution : app.PolicyExecution) :
    Option app.Action → FinDist (app.State × List app.Action)
  | none => FinDist.pure (execution.native, execution.nativeTrace)
  | some action =>
      (app.step execution.native action).bind fun next =>
        FinDist.pure (next, execution.nativeTrace ++ [action])

def playerStep [DecidableEq Principal] (who : Principal)
    (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    FinDist app.PolicyExecution :=
  let view := State.observe app execution.native who
  (app.advance execution (PlayerCommand.toAction app who command)).bind fun advanced =>
    FinDist.pure
      { execution with
        native := advanced.1
        principalHistory := fun other =>
          if other = who then execution.principalHistory who ++ [⟨view, command⟩]
          else execution.principalHistory other
        nativeTrace := advanced.2 }

def environmentPolicyStep [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand) :
    FinDist app.PolicyExecution :=
  let view := State.environmentView app execution.native
  (app.advance execution (EnvironmentPolicyCommand.toAction app command)).bind fun advanced =>
    FinDist.pure
      { execution with
        native := advanced.1
        environmentHistory := execution.environmentHistory ++ [⟨view, command⟩]
        nativeTrace := advanced.2 }

def invoke [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) : @Invocation Principal → FinDist app.PolicyExecution
  | .player who =>
      (players who (execution.principalHistory who) (State.observe app execution.native who)).bind
        (app.playerStep who execution)
  | .environment =>
      (environment execution.environmentHistory (State.environmentView app execution.native)).bind
        (app.environmentPolicyStep execution)

def runPolicies [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy) :
    List (@Invocation Principal) → app.PolicyExecution → FinDist app.PolicyExecution
  | [], execution => FinDist.pure execution
  | invocation :: rest, execution =>
      (invoke app players environment execution invocation).bind
        (runPolicies players environment rest)

theorem runPolicies_append [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (first second : List (@Invocation Principal)) (execution : app.PolicyExecution) :
    app.runPolicies players environment (first ++ second) execution =
      (app.runPolicies players environment first execution).bind
        (app.runPolicies players environment second) := by
  induction first generalizing execution with
  | nil => simp [runPolicies]
  | cons invocation rest ih =>
      simp only [List.cons_append, runPolicies, FinDist.bind_bind]
      congr 1
      funext next
      exact ih next

/-- Only the player policies invoked by the finite schedule affect its law. -/
theorem runPolicies_congr_on_schedule [DecidableEq Principal]
    (first second : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (hplayers : ∀ who, Invocation.player who ∈ schedule → first who = second who) :
    app.runPolicies first environment schedule execution =
      app.runPolicies second environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      have hrest : ∀ who, Invocation.player who ∈ rest → first who = second who :=
        fun who hmem => hplayers who (List.mem_cons_of_mem invocation hmem)
      have hinvoke : app.invoke first environment execution invocation =
          app.invoke second environment execution invocation := by
        cases invocation with
        | environment => rfl
        | player who => simp only [invoke, hplayers who (List.mem_cons_self ..)]
      simp only [runPolicies, hinvoke]
      exact FinDist.bind_congr fun next _ => ih next hrest

def policySignature (Principal : Type uPrincipal)
    (app : MessageApplication Principal) : GameSignature Principal where
  Strategy := fun _ => app.PlayerPolicy
  Outcome := app.PolicyExecution

def policyGame [DecidableEq Principal]
    (environment : app.EnvironmentPolicy) (schedule : List (@Invocation Principal))
    (initial : app.State) : GameForm Principal where
  sig := policySignature Principal app
  play players := runPolicies app players environment schedule
    (PolicyExecution.initial app initial)

/-! ## Local-history laws -/

/-- Recording a player command preserves the native transition law. -/
theorem playerStep_native [DecidableEq Principal] (who : Principal)
    (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    (app.playerStep who execution command).map MessageInterface.PolicyExecution.native =
      match command.toAction app who with
      | none => FinDist.pure execution.native
      | some action => app.step execution.native action := by
  cases hcommand : command.toAction app who <;>
    simp [playerStep, advance, hcommand, FinDist.map_bind]

/-- Recording an environment command preserves the native transition law. -/
theorem environmentStep_native [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand) :
    (app.environmentPolicyStep execution command).map
      MessageInterface.PolicyExecution.native =
      match command.toAction with
      | none => FinDist.pure execution.native
      | some action => app.step execution.native action := by
  cases hcommand : command.toAction <;>
    simp [environmentPolicyStep, advance, hcommand, FinDist.map_bind]

theorem playerStep_history_self [DecidableEq Principal]
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.principalHistory who = execution.principalHistory who ++
      [⟨State.observe app execution.native who, command⟩] := by
  simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨advanced, _, hnext⟩ := hnext
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  simp

theorem playerStep_other_history [DecidableEq Principal]
    (who other : Principal) (hne : other ≠ who)
    (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.principalHistory other = execution.principalHistory other := by
  simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, _, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  simp [hne]

theorem environmentStep_principalHistory [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    next.principalHistory = execution.principalHistory := by
  simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, _, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  rfl

theorem environmentStep_history_length [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    next.environmentHistory.length = execution.environmentHistory.length + 1 := by
  simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨advanced, _, hnext⟩ := hnext
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  simp

theorem playerStep_environmentHistory [DecidableEq Principal]
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.environmentHistory = execution.environmentHistory := by
  simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨advanced, _, hnext⟩ := hnext
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  rfl

/-- Environment-only invocation phases preserve all principal command histories. -/
theorem runPolicies_environment_principalHistory [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (count : Nat) (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.principalHistory = execution.principalHistory := by
  induction count generalizing execution with
  | zero =>
      simp only [List.replicate_zero, runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | succ count ih =>
      simp only [List.replicate_succ, runPolicies,
        FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, htail⟩ := hnext
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
      obtain ⟨command, _, hstep⟩ := hmiddle
      exact (ih middle htail).trans (app.environmentStep_principalHistory
        execution command middle hstep)

/-- Environment policy memory counts its own invocations, including waits,
independently of intervening player commands and application success. -/
theorem runPolicies_environmentHistory_length [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.environmentHistory.length = execution.environmentHistory.length +
      schedule.countP Invocation.isEnvironment := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have htail := ih middle hnext
      cases invocation with
      | player who =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hhistory := app.playerStep_environmentHistory who execution command middle hstep
          simp only [List.countP_cons, Invocation.isEnvironment, Bool.false_eq_true, ↓reduceIte]
          rw [htail, hhistory]
          omega
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hhistory := app.environmentStep_history_length execution command middle hstep
          simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
          omega

/-- Waiting records the invocation and sampled view but performs no native
action and leaves the proof-facing action trace unchanged. -/
theorem playerStep_wait [DecidableEq Principal] (who : Principal)
    (execution : app.PolicyExecution) :
    app.playerStep who execution .wait = FinDist.pure
      { execution with
        principalHistory := fun other =>
          if other = who then execution.principalHistory who ++
            [⟨State.observe app execution.native who, .wait⟩]
          else execution.principalHistory other } := by
  simp [playerStep, advance, PlayerCommand.toAction]

theorem environmentStep_wait [DecidableEq Principal]
    (execution : app.PolicyExecution) :
    app.environmentPolicyStep execution .wait = FinDist.pure
      { execution with
        environmentHistory := execution.environmentHistory ++
          [⟨State.environmentView app execution.native, .wait⟩] } := by
  simp [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction]

end Interaction.MessageApplication
