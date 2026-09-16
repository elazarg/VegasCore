/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceController
import Interaction.MessageApplicationPolicyInvariant

/-! # Actual-run history laws for sample-once choice controllers

These laws connect the controller's list-level cache to the real
`MessageApplication` policy runner.  The first ready invocation records exactly
one draw from the supplied kernel, while every later continuation retains the
earliest recorded value.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uValue uInput

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)
variable {Value : Type uValue} {Input : Type uInput}

namespace ChoiceController

/-- The complete first-invocation law samples the decision kernel and runs the
actual encoded command. Native state, traffic, and both kinds of local history
remain in the outcome; this is not just a cached-value marginal. -/
theorem invoke_uncached_ready [DecidableEq Principal]
    (controller : ChoiceController app Value Input) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (input : Input)
    (hpolicy : players who (execution.principalHistory who)
      (State.observe app execution.native who) =
        controller.policy app (execution.principalHistory who)
          (State.observe app execution.native who))
    (hresolved : controller.resolved (State.observe app execution.native who) = false)
    (hcache : controller.codec.cachedValue app
      (execution.principalHistory who) = none)
    (hready : controller.ready (State.observe app execution.native who) = true)
    (hreadout : controller.readout? (execution.principalHistory who)
      (State.observe app execution.native who) = some input) :
    app.invoke players environment execution (.player who) =
      (controller.kernel input).bind fun value =>
        app.playerStep who execution (controller.codec.encode value) := by
  rw [invoke, hpolicy, controller.policy_of_uncached_ready app
    (execution.principalHistory who) (State.observe app execution.native who)
    input hresolved hcache hready hreadout, FinDist.bind_map]

/-- A ready, unresolved invocation with no cached command records exactly
the source-kernel draw in the principal's actual command history.  Application
state effects of the command cannot alter this projected law. -/
theorem invoke_uncached_ready_cachedValue [DecidableEq Principal]
    (controller : ChoiceController app Value Input) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (input : Input)
    (hpolicy : players who (execution.principalHistory who)
      (State.observe app execution.native who) =
        controller.policy app (execution.principalHistory who)
          (State.observe app execution.native who))
    (hresolved : controller.resolved (State.observe app execution.native who) = false)
    (hcache : controller.codec.cachedValue app
      (execution.principalHistory who) = none)
    (hready : controller.ready (State.observe app execution.native who) = true)
    (hreadout : controller.readout? (execution.principalHistory who)
      (State.observe app execution.native who) = some input) :
    (app.invoke players environment execution (.player who)).map
        (fun next => controller.codec.cachedValue app
          (next.principalHistory who)) =
      (controller.kernel input).map some := by
  rw [controller.invoke_uncached_ready app who players environment execution input
    hpolicy hresolved hcache hready hreadout, FinDist.map_bind]
  apply FinDist.bind_congr
  intro value _
  cases hcommand : controller.codec.encode value
  all_goals
    have hrecorded := controller.codec.cachedValue_append_encoded_of_none
      app (execution.principalHistory who)
        (State.observe app execution.native who) value hcache
    rw [hcommand] at hrecorded
    simpa [playerStep, advance, PlayerCommand.toAction, step] using
      congrArg FinDist.pure hrecorded

end ChoiceController

namespace ChoiceEncoding

/-- The complete cache update equation for an arbitrary player command.
Only the acting principal's history changes, retaining its first decoded value. -/
theorem playerStep_cachedValue [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (actor query : Principal)
    (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (hnext : next ∈ (app.playerStep actor execution command).support) :
    encoding.cachedValue app (next.principalHistory query) =
      if query = actor then
        (encoding.cachedValue app (execution.principalHistory query)).orElse
          (fun _ => encoding.decode command)
      else encoding.cachedValue app (execution.principalHistory query) := by
  by_cases hquery : query = actor
  · subst query
    rw [app.playerStep_history_self actor execution command next hnext]
    simp only [↓reduceIte, encoding.cachedValue_append, cachedValue_cons, cachedValue_nil]
    cases encoding.decode command <;> rfl
  · rw [app.playerStep_other_history actor query hquery execution command next hnext,
      if_neg hquery]

/-- The first encoded command records its value in the actual principal
history, independently of the command's native application effect. -/
theorem playerStep_cachedValue_of_none [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal)
    (execution next : app.PolicyExecution) (value : Value)
    (hcache : encoding.cachedValue app (execution.principalHistory who) = none)
    (hnext : next ∈ (app.playerStep who execution (encoding.encode value)).support) :
    encoding.cachedValue app (next.principalHistory who) = some value := by
  rw [app.playerStep_history_self who execution (encoding.encode value) next hnext]
  exact encoding.cachedValue_append_encoded_of_none app _ _ value hcache

/-- Appending one command outside an encoding's domain preserves an empty
earliest-command cache. -/
theorem cachedValue_append_unrecognized
    (encoding : ChoiceEncoding Value app.PlayerCommand)
    (history : List app.PlayerEntry) (view : app.View)
    (command : app.PlayerCommand)
    (hcache : encoding.cachedValue app history = none)
    (hdecode : encoding.decode command = none) :
    encoding.cachedValue app (history ++ [⟨view, command⟩]) = none := by
  rw [encoding.cachedValue_append_of_none app history _ hcache]
  simp [cachedValue, hdecode]

/-- Appending a command outside an encoding's domain leaves its earliest
recognized-command cache exactly unchanged, whether empty or populated. -/
theorem cachedValue_append_unrecognized_eq
    (encoding : ChoiceEncoding Value app.PlayerCommand)
    (history : List app.PlayerEntry) (view : app.View)
    (command : app.PlayerCommand)
    (hdecode : encoding.decode command = none) :
    encoding.cachedValue app (history ++ [⟨view, command⟩]) =
      encoding.cachedValue app history := by
  cases hcache : encoding.cachedValue app history with
  | none =>
      exact encoding.cachedValue_append_unrecognized app history view command hcache hdecode
  | some value =>
      exact encoding.cachedValue_append_of_some app history _ value hcache

/-- Once an endpoint value occurs in a principal's actual history, recording
any further player command preserves that earliest value. -/
theorem playerStep_cachedValue_of_some [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal)
    (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (value : Value)
    (hcache : encoding.cachedValue app
      (execution.principalHistory who) = some value)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    encoding.cachedValue app (next.principalHistory who) = some value := by
  rw [playerStep_history_self app who execution command next hnext]
  exact encoding.cachedValue_append_of_some app _ _ value hcache

/-- A cached value satisfies every predicate shared by the initial cache and
the designated player's supported decoded commands. Other players and all
environment actions are unrestricted. -/
theorem runPolicies_cachedValue_property [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal) (property : Value → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hcommand : ∀ history view command value,
      command ∈ (players who history view).support → encoding.decode command = some value →
        property value)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hinitial : ∀ value, encoding.cachedValue app (execution.principalHistory who) = some value →
      property value)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    ∀ value, encoding.cachedValue app (next.principalHistory who) = some value →
      property value := by
  apply app.runPolicies_execution_invariant
    (fun current => ∀ value,
      encoding.cachedValue app (current.principalHistory who) = some value → property value)
    players environment ?_ ?_ schedule execution next hinitial hnext
  · intro current actor command after hcurrent hchosen hafter value hcache
    rw [encoding.playerStep_cachedValue app actor who current after command hafter] at hcache
    by_cases hactor : who = actor
    · subst actor
      simp only [↓reduceIte] at hcache
      cases hprior : encoding.cachedValue app (current.principalHistory who) with
      | none =>
          simp only [hprior, Option.orElse_none] at hcache
          exact hcommand _ _ command value hchosen hcache
      | some prior =>
          simp only [hprior, Option.orElse_some, Option.some.injEq] at hcache
          subst value
          exact hcurrent prior hprior
    · rw [if_neg hactor] at hcache
      exact hcurrent value hcache
  · intro current command after hcurrent _hchosen hafter value hcache
    rw [congrFun (app.environmentStep_principalHistory current command after hafter) who] at hcache
    exact hcurrent value hcache

/-- Arbitrary later player and environment invocations cannot replace an
endpoint's earliest cached value.  No settlement or liveness premise is used. -/
theorem runPolicies_cachedValue_of_some [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (value : Value)
    (hcache : encoding.cachedValue app
      (execution.principalHistory who) = some value)
    (hnext : next ∈
      (app.runPolicies players environment schedule execution).support) :
    encoding.cachedValue app (next.principalHistory who) = some value := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hcache
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      apply ih middle ?_ hnext
      cases invocation with
      | player actor =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          by_cases hactor : actor = who
          · subst actor
            exact encoding.playerStep_cachedValue_of_some app who execution
              middle command value hcache hstep
          · rw [app.playerStep_other_history actor who (Ne.symm hactor)
                execution command middle hstep]
            exact hcache
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          rw [congrFun
            (app.environmentStep_principalHistory execution command middle hstep) who]
          exact hcache

/-- Carry a first sample jointly with the complete subsequent native
execution. Later policies and delivery may depend on the sampled command;
the law retains that dependence rather than multiplying separate marginals.
No completion, inclusion, or restriction on later commands is assumed. -/
theorem runPolicies_sample_joint [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (choices : FinDist Value)
    (hchoice : players who (execution.principalHistory who)
        (State.observe app execution.native who) = choices.map encoding.encode)
    (hcache : encoding.cachedValue app (execution.principalHistory who) = none) :
    (app.runPolicies players environment (.player who :: schedule) execution).map
        (fun next => (encoding.cachedValue app (next.principalHistory who), next)) =
      choices.bind fun value =>
        ((app.playerStep who execution (encoding.encode value)).bind
          (app.runPolicies players environment schedule)).map (fun next => (some value, next)) := by
  rw [runPolicies, invoke, hchoice, FinDist.bind_map, FinDist.bind_bind, FinDist.map_bind]
  apply FinDist.bind_congr
  intro value _
  apply FinDist.map_congr_of_eq_on_support
  intro next hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hrecorded := encoding.playerStep_cachedValue_of_none app who execution middle
    value hcache hmiddle
  exact congrArg (fun cached => (cached, next))
    (encoding.runPolicies_cachedValue_of_some app who players environment schedule
      middle next value hrecorded hnext)

end ChoiceEncoding

end Interaction.MessageApplication
