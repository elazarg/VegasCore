/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import Interaction.MessageApplicationLaws

/-! # Distribution-valued invariants of message-policy execution -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uOutcome

variable {Principal : Type uPrincipal} {Outcome : Type uOutcome}

/-- A continuation law preserved by every native action is preserved by an
arbitrary finite policy execution. Player and environment policies may be
randomized and history-dependent. -/
theorem runPolicies_harmonic (app : MessageApplication Principal)
    [DecidableEq Principal] (kernel : app.State → FinDist Outcome)
    (harmonic : ∀ state action,
      (app.step state action).bind kernel = kernel state)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution) :
    (app.runPolicies players environment schedule execution).bind
        (fun next => kernel next.native) =
      kernel execution.native := by
  have hplayer : ∀ who (current : app.PolicyExecution) command,
      (app.playerStep who current command).bind (fun next => kernel next.native) =
        kernel current.native := by
    intro who current command
    rw [← FinDist.bind_map, app.playerStep_native]
    cases command with
    | privateCommand command => exact harmonic current.native (.privateCommand who command)
    | submit payload => exact harmonic current.native (.submit who payload)
    | replay id => exact harmonic current.native (.replay who id)
    | wait => exact FinDist.pure_bind _ _
  have henvironment : ∀ (current : app.PolicyExecution) command,
      (app.environmentPolicyStep current command).bind (fun next => kernel next.native) =
        kernel current.native := by
    intro current command
    rw [← FinDist.bind_map, app.environmentStep_native]
    cases command with
    | deliver observer id => exact harmonic current.native (.deliver observer id)
    | «include» id => exact harmonic current.native (.include id)
    | application command => exact harmonic current.native (.environment command)
    | wait => exact FinDist.pure_bind _ _
  induction schedule generalizing execution with
  | nil => exact FinDist.pure_bind _ _
  | cons invocation schedule ih =>
      rw [runPolicies, FinDist.bind_bind]
      calc
        _ = (app.invoke players environment execution invocation).bind
              (fun next => kernel next.native) := by
            apply FinDist.bind_congr
            intro next _
            exact ih next
        _ = kernel execution.native := by
          cases invocation with
          | player who =>
              simp only [invoke, FinDist.bind_bind]
              calc
                _ = (players who (execution.principalHistory who)
                      (State.observe app execution.native who)).bind
                    (fun _ => kernel execution.native) := by
                  apply FinDist.bind_congr
                  intro command _
                  exact hplayer who execution command
                _ = kernel execution.native := FinDist.bind_const _ _
          | environment =>
              simp only [invoke, FinDist.bind_bind]
              calc
                _ = (environment execution.environmentHistory
                      (State.environmentView app execution.native)).bind
                    (fun _ => kernel execution.native) := by
                  apply FinDist.bind_congr
                  intro command _
                  exact henvironment execution command
                _ = kernel execution.native := FinDist.bind_const _ _

/-- info: 'Interaction.MessageApplication.runPolicies_harmonic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_harmonic

/-- Application-local distribution invariants lift through the public message
pool and arbitrary policy histories. Deterministic handlers preserve the
continuation law pointwise; probabilistic environment actions preserve it in
expectation. Submission, delivery, replay, and rejected inclusion need no
application-specific proof. -/
theorem runPolicies_application_harmonic (app : MessageApplication Principal)
    [DecidableEq Principal] (kernel : app.Application → FinDist Outcome)
    (hprivate : ∀ state who command,
      kernel (app.privateStep state who command) = kernel state)
    (hhandler : ∀ state message next, app.handle state message = some next →
      kernel next = kernel state)
    (henvironment : ∀ state command,
      (app.environmentStep state command).bind kernel = kernel state)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution) :
    (app.runPolicies players environment schedule execution).bind
        (fun next => kernel next.native.application) =
      kernel execution.native.application := by
  apply app.runPolicies_harmonic (fun state => kernel state.application)
  intro state action
  cases action with
  | privateCommand who command =>
      simpa only [step, FinDist.pure_bind] using hprivate state.application who command
  | submit who payload | replay who id | deliver who id =>
      simp only [step, FinDist.pure_bind]
  | «include» id =>
      simp only [step, FinDist.pure_bind]
      exact app.includePending_application_invariant
        (fun current => kernel current = kernel state.application)
        (fun current message next hcurrent hnext =>
          (hhandler current message next hnext).trans hcurrent) state id rfl
  | environment command =>
      simpa only [step, FinDist.bind_map] using henvironment state.application command

/-- info: 'Interaction.MessageApplication.runPolicies_application_harmonic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_application_harmonic

end Interaction.MessageApplication
