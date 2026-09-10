/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationLaws
import Interaction.MessageApplicationPolicies

/-! # Admission filters for message applications

An admission filter restricts public handler calls and application-owned
environment commands without changing the application's carrier, observations,
private transitions, or raw message-pool commands.  A rejected handler call has
no application result.  A disabled environment command stutters.

The local laws below state exactly when the filtered and original interpreters
agree.  They impose no restriction on the commands that policies may produce.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- Restrict application-owned effects while retaining the same message
interface, observations, private transition, and message-pool operations. -/
def withAdmission
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool) :
    MessageApplication Principal :=
  { app with
    handle := fun application message =>
      if messageAllowed (app.observeEnvironment application) message then
        app.handle application message
      else none
    environmentStep := fun application command =>
      if environmentAllowed (app.observeEnvironment application) command then
        app.environmentStep application command
      else FinDist.pure application }

@[simp] theorem withAdmission_toMessageInterface
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool) :
    (app.withAdmission messageAllowed environmentAllowed).toMessageInterface =
      app.toMessageInterface := rfl

@[simp] theorem withAdmission_privateStep
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) (who : Principal) (command : app.PrivateCommand) :
    (app.withAdmission messageAllowed environmentAllowed).privateStep application who command =
      app.privateStep application who command := rfl

@[simp] theorem withAdmission_observePlayer
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) (who : Principal) :
    (app.withAdmission messageAllowed environmentAllowed).observePlayer application who =
      app.observePlayer application who := rfl

@[simp] theorem withAdmission_observeEnvironment
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) :
    (app.withAdmission messageAllowed environmentAllowed).observeEnvironment application =
      app.observeEnvironment application := rfl

/-- An admitted message is handled exactly as it was by the underlying
application. -/
theorem handle_withAdmission_of_allowed
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) (message : Message Principal app.Payload)
    (hallowed : messageAllowed (app.observeEnvironment application) message = true) :
    (app.withAdmission messageAllowed environmentAllowed).handle application message =
      app.handle application message := by
  simp [withAdmission, hallowed]

theorem handle_withAdmission_of_disallowed
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) (message : Message Principal app.Payload)
    (hallowed : messageAllowed (app.observeEnvironment application) message = false) :
    (app.withAdmission messageAllowed environmentAllowed).handle application message = none := by
  simp [withAdmission, hallowed]

/-- A successful restricted handler call is also a successful call of the
underlying handler, with the same result. -/
theorem withAdmission_handle_some
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application next : app.Application) (message : Message Principal app.Payload)
    (hnext : (app.withAdmission messageAllowed environmentAllowed).handle
      application message = some next) :
    app.handle application message = some next := by
  simp only [withAdmission] at hnext
  split at hnext
  · exact hnext
  · simp at hnext

/-- An admitted application-owned environment command retains its complete
stochastic transition law. -/
theorem environmentStep_withAdmission_of_allowed
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) (command : app.EnvironmentCommand)
    (hallowed : environmentAllowed (app.observeEnvironment application) command = true) :
    (app.withAdmission messageAllowed environmentAllowed).environmentStep
      application command = app.environmentStep application command := by
  simp [withAdmission, hallowed]

theorem environmentStep_withAdmission_of_disallowed
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application : app.Application) (command : app.EnvironmentCommand)
    (hallowed : environmentAllowed (app.observeEnvironment application) command = false) :
    (app.withAdmission messageAllowed environmentAllowed).environmentStep
      application command = FinDist.pure application := by
  simp [withAdmission, hallowed]

/-- A supported restricted environment result either is the disabled-command
stutter or is supported by the underlying application kernel. -/
theorem withAdmission_environment_support
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (application next : app.Application) (command : app.EnvironmentCommand)
    (hnext : next ∈ ((app.withAdmission messageAllowed environmentAllowed).environmentStep
      application command).support) :
    next = application ∨ next ∈ (app.environmentStep application command).support := by
  simp only [withAdmission] at hnext
  split at hnext
  · exact Or.inr hnext
  · exact Or.inl (by simpa only [FinDist.mem_support_pure] using hnext)

/-- Player commands never invoke the public handler or application environment
kernel, so admission leaves their exact policy step unchanged. -/
theorem playerStep_withAdmission_eq [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    (app.withAdmission messageAllowed environmentAllowed).playerStep who execution command =
      app.playerStep who execution command := by
  cases command <;> rfl

/-- Looking up no envelope makes inclusion identical under every admission
filter. -/
theorem includePending_withAdmission_of_missing [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (state : app.State) (id : MessageId Principal)
    (hmissing : state.pool.lookup id = none) :
    (app.withAdmission messageAllowed environmentAllowed).includePending state id =
      app.includePending state id := by
  rw [(app.withAdmission messageAllowed environmentAllowed).includePending_missing
      state id hmissing,
    app.includePending_missing state id hmissing]

/-- Inclusion is identical when its actual looked-up envelope is admitted. -/
theorem includePending_withAdmission_of_allowed [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (state : app.State) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (hlookup : state.pool.lookup id = some message)
    (hallowed : messageAllowed (app.observeEnvironment state.application) message = true) :
    (app.withAdmission messageAllowed environmentAllowed).includePending state id =
      app.includePending state id := by
  unfold includePending MessagePool.includeApplication
  simp only [MessagePool.includePending, hlookup, withAdmission, hallowed, ↓reduceIte]

/-- Admission of an environment-policy command is evaluated against the exact
native state on which that command will run. Missing inclusion identifiers are
admitted because both applications stutter on them. -/
def EnvironmentCommandAdmitted [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (execution : app.PolicyExecution) : app.EnvironmentPolicyCommand → Prop
  | .deliver _ _ => True
  | .include id => ∀ message, execution.native.pool.lookup id = some message →
      messageAllowed (app.observeEnvironment execution.native.application) message = true
  | .application command =>
      environmentAllowed (app.observeEnvironment execution.native.application) command = true
  | .wait => True

private theorem includePending_withAdmission_of_command [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (state : app.State) (id : MessageId Principal)
    (hadmitted : ∀ message, state.pool.lookup id = some message →
      messageAllowed (app.observeEnvironment state.application) message = true) :
    (app.withAdmission messageAllowed environmentAllowed).includePending state id =
      app.includePending state id := by
  cases hlookup : state.pool.lookup id with
  | none =>
      exact app.includePending_withAdmission_of_missing messageAllowed environmentAllowed
        state id hlookup
  | some message =>
      exact app.includePending_withAdmission_of_allowed messageAllowed environmentAllowed
        state id message hlookup (hadmitted message hlookup)

/-- An explicitly admitted environment-policy command has exactly its original
state, history, and native-trace law. -/
theorem environmentPolicyStep_withAdmission_eq [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (hadmitted : app.EnvironmentCommandAdmitted messageAllowed environmentAllowed
      execution command) :
    (app.withAdmission messageAllowed environmentAllowed).environmentPolicyStep
      execution command = app.environmentPolicyStep execution command := by
  cases command with
  | deliver observer id => rfl
  | «include» id =>
      simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
        step, FinDist.pure_bind]
      rw [includePending_withAdmission_of_command app messageAllowed environmentAllowed
        execution.native id hadmitted]
      rfl
  | application command =>
      simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction, step]
      rw [app.environmentStep_withAdmission_of_allowed messageAllowed environmentAllowed
        execution.native.application command hadmitted]
      rfl
  | wait => rfl

/-- Admission requirements for one invocation at its original native prefix.
Player invocations are unconditional. An environment invocation requires every
command supported by the environment policy at that exact observation to be
admitted. -/
def InvocationAdmitted [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (environment : app.EnvironmentPolicy) (execution : app.PolicyExecution) :
    @Invocation Principal → Prop
  | .player _ => True
  | .environment => ∀ command,
      command ∈ (environment execution.environmentHistory
        (State.environmentView app execution.native)).support →
      app.EnvironmentCommandAdmitted messageAllowed environmentAllowed execution command

/-- Every environment command is admitted at every original execution prefix
reachable along a fixed schedule. This predicate records only local support
conditions; it does not contain a second execution or an outcome equality. -/
def PolicyRunAdmitted [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy) :
    List (@Invocation Principal) → app.PolicyExecution → Prop
  | [], _ => True
  | invocation :: rest, execution =>
      app.InvocationAdmitted messageAllowed environmentAllowed environment execution
          invocation ∧
        ∀ next, next ∈ (app.invoke players environment execution invocation).support →
          PolicyRunAdmitted messageAllowed environmentAllowed players environment rest next

/-- One invocation has its original law when its environment-policy support is
admitted. -/
theorem invoke_withAdmission_eq [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (invocation : @Invocation Principal)
    (hadmitted : app.InvocationAdmitted messageAllowed environmentAllowed environment
      execution invocation) :
    (app.withAdmission messageAllowed environmentAllowed).invoke
      players environment execution invocation =
        app.invoke players environment execution invocation := by
  cases invocation with
  | player who =>
      simp only [invoke]
      apply FinDist.bind_congr
      intro command _
      exact app.playerStep_withAdmission_eq messageAllowed environmentAllowed
        who execution command
  | environment =>
      simp only [invoke]
      apply FinDist.bind_congr
      intro command hcommand
      exact app.environmentPolicyStep_withAdmission_eq messageAllowed environmentAllowed
        execution command (hadmitted command hcommand)

/-- On a finite schedule, admission at every original reachable prefix makes
the restricted and original policy-run distributions exactly equal. -/
theorem runPolicies_withAdmission_eq [DecidableEq Principal]
    (messageAllowed : app.EnvironmentView → Message Principal app.Payload → Bool)
    (environmentAllowed : app.EnvironmentView → app.EnvironmentCommand → Bool)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (hadmitted : app.PolicyRunAdmitted messageAllowed environmentAllowed
      players environment schedule execution) :
    (app.withAdmission messageAllowed environmentAllowed).runPolicies
      players environment schedule execution =
        app.runPolicies players environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      simp only [runPolicies]
      rw [app.invoke_withAdmission_eq messageAllowed environmentAllowed players environment
        execution invocation hadmitted.1]
      apply FinDist.bind_congr
      intro next hnext
      exact ih next (hadmitted.2 next hnext)

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.playerStep_withAdmission_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.playerStep_withAdmission_eq

/-- info: 'Interaction.MessageApplication.environmentPolicyStep_withAdmission_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.environmentPolicyStep_withAdmission_eq

/-- info: 'Interaction.MessageApplication.runPolicies_withAdmission_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_withAdmission_eq
