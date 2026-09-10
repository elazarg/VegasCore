/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant

/-! # Conservative message-handler extensions

Replacing only an application's message handler leaves all carrier, command,
observation, private-transition, and environment-transition types unchanged.
If the replacement agrees on every message that the fixed policies can place
in the pool, the complete policy execution law is unchanged.  Other policies
may still submit newly handled messages, so this is a conservativity theorem,
not a strategic equivalence theorem.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- Replace exactly the public message handler of an application. -/
def withHandler
    (handler : app.Application → Message Principal app.Payload → Option app.Application) :
    MessageApplication Principal :=
  { app with handle := handler }

private theorem includePending_withHandler_eq [DecidableEq Principal]
    (handler : app.Application → Message Principal app.Payload → Option app.Application)
    (safe : Message Principal app.Payload → Prop)
    (hagrees : ∀ application message, safe message →
      handler application message = app.handle application message)
    (state : app.State) (id : MessageId Principal)
    (hsafe : state.pool.Satisfies safe) :
    (app.withHandler handler).includePending state id = app.includePending state id := by
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [(app.withHandler handler).includePending_missing state id hlookup,
        app.includePending_missing state id hlookup]
  | some message =>
      have hmessage : safe message :=
        hsafe.1 message (List.mem_of_find?_eq_some hlookup)
      unfold includePending MessagePool.includeApplication
      simp only [MessagePool.includePending, hlookup, withHandler]
      rw [hagrees state.application message hmessage]

private theorem playerStep_withHandler_eq [DecidableEq Principal]
    (handler : app.Application → Message Principal app.Payload → Option app.Application)
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    (app.withHandler handler).playerStep who execution command =
      app.playerStep who execution command := by
  cases command <;> rfl

private theorem environmentPolicyStep_withHandler_eq [DecidableEq Principal]
    (handler : app.Application → Message Principal app.Payload → Option app.Application)
    (safe : Message Principal app.Payload → Prop)
    (hagrees : ∀ application message, safe message →
      handler application message = app.handle application message)
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (hsafe : execution.native.pool.Satisfies safe) :
    (app.withHandler handler).environmentPolicyStep execution command =
      app.environmentPolicyStep execution command := by
  cases command with
  | deliver observer id => rfl
  | «include» id =>
      simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
        step, FinDist.pure_bind]
      rw [includePending_withHandler_eq app handler safe hagrees execution.native id hsafe]
      rfl
  | application command => rfl
  | wait => rfl

private theorem invoke_withHandler_eq [DecidableEq Principal]
    (handler : app.Application → Message Principal app.Payload → Option app.Application)
    (safe : Message Principal app.Payload → Prop)
    (hagrees : ∀ application message, safe message →
      handler application message = app.handle application message)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (invocation : @Invocation Principal)
    (hsafe : execution.native.pool.Satisfies safe) :
    (app.withHandler handler).invoke players environment execution invocation =
      app.invoke players environment execution invocation := by
  cases invocation with
  | player who =>
      simp only [invoke]
      apply FinDist.bind_congr
      intro command _
      exact playerStep_withHandler_eq app handler who execution command
  | environment =>
      simp only [invoke]
      apply FinDist.bind_congr
      intro command _
      exact environmentPolicyStep_withHandler_eq app handler safe hagrees
        execution command hsafe

/-- A handler extension has exactly the original execution law for fixed
policies whose supported submissions remain inside the agreement predicate. -/
theorem runPolicies_eq_of_handler_agrees [DecidableEq Principal]
    (handler : app.Application → Message Principal app.Payload → Option app.Application)
    (safe : Message Principal app.Payload → Prop)
    (hagrees : ∀ application message, safe message →
      handler application message = app.handle application message)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hsubmit : ∀ (execution : app.PolicyExecution) (who : Principal)
      (payload : app.Payload),
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe app execution.native who)).support →
      ∀ serial, safe ⟨(who, serial), payload⟩)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies safe) :
    (app.withHandler handler).runPolicies players environment schedule execution =
      app.runPolicies players environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      simp only [runPolicies]
      rw [invoke_withHandler_eq app handler safe hagrees players environment
        execution invocation hsafe]
      apply FinDist.bind_congr
      intro middle hmiddle
      apply ih middle
      apply app.runPolicies_pool_satisfies safe players environment hsubmit
        [invocation] execution middle hsafe
      simpa only [runPolicies, FinDist.bind_pure] using hmiddle

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_eq_of_handler_agrees' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_eq_of_handler_agrees
