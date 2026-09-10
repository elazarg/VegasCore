/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Environment phases on the shared policy runner

The environment may change service policy after a fixed number of its own
invocations. Both policies receive the real history and current observation;
the switch neither resets memory nor changes the operational interpreter.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

def switchEnvironmentAfter (turns : Nat) (first second : app.EnvironmentPolicy) :
    app.EnvironmentPolicy := fun history view =>
  if history.length < turns then first history view else second history view

/-- A finite run depends only on the environment policy at the history lengths
it actually visits. The current observations and complete histories are kept. -/
theorem runPolicies_environment_congr [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (first second : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution : app.PolicyExecution)
    (hagree : ∀ history view,
      execution.environmentHistory.length ≤ history.length →
      history.length < execution.environmentHistory.length +
        schedule.countP Invocation.isEnvironment → first history view = second history view) :
    app.runPolicies players first schedule execution =
      app.runPolicies players second schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      have hinvoke : app.invoke players first execution invocation =
          app.invoke players second execution invocation := by
        cases invocation with
        | player who => rfl
        | environment =>
            unfold invoke
            rw [hagree _ _ (by rfl) (by simp [Invocation.isEnvironment])]
      simp only [runPolicies, hinvoke]
      apply FinDist.bind_congr
      intro next hnext
      have hlength := app.runPolicies_environmentHistory_length players second
        [invocation] execution next (by simpa [runPolicies] using hnext)
      apply ih next
      intro history view hlo hhi
      apply hagree history view <;>
        cases invocation <;>
        simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte] at hlength ⊢ <;> omega

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_environment_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_environment_congr
