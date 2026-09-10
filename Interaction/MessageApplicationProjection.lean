/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Projection of message-application policy runs

A projection between policy executions need not identify native states,
observations, commands, or histories.  If each concrete invocation projects to
the corresponding abstract invocation while a reachable invariant holds, then
the complete finite policy run projects exactly.  The theorem is a generic
kernel-composition fact; constructing the one-step law remains the caller's
semantic obligation.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable {concrete : MessageApplication Principal}
variable {abstract : MessageApplication Principal}

/-- Exact projection of every reachable invocation lifts through the actual
finite `runPolicies` interpreter.  `Good` need hold only at the initial state
and at concrete successors supported by the invocation kernel. -/
theorem runPolicies_map_of_invoke
    (concretePlayers : Principal → concrete.PlayerPolicy)
    (concreteEnvironment : concrete.EnvironmentPolicy)
    (abstractPlayers : Principal → abstract.PlayerPolicy)
    (abstractEnvironment : abstract.EnvironmentPolicy)
    (project : concrete.PolicyExecution → abstract.PolicyExecution)
    (Good : concrete.PolicyExecution → Prop)
    (hinvokeGood : ∀ execution invocation next,
      Good execution →
      next ∈ (concrete.invoke concretePlayers concreteEnvironment execution
        invocation).support →
      Good next)
    (hinvoke : ∀ execution invocation,
      Good execution →
      (concrete.invoke concretePlayers concreteEnvironment execution invocation).map project =
        abstract.invoke abstractPlayers abstractEnvironment (project execution) invocation)
    (schedule : List (@Invocation Principal))
    (execution : concrete.PolicyExecution) (hgood : Good execution) :
    (concrete.runPolicies concretePlayers concreteEnvironment schedule execution).map project =
      abstract.runPolicies abstractPlayers abstractEnvironment schedule
        (project execution) := by
  induction schedule generalizing execution with
  | nil => simp [runPolicies]
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.map_bind]
      calc
        (concrete.invoke concretePlayers concreteEnvironment execution invocation).bind
            (fun next =>
              (concrete.runPolicies concretePlayers concreteEnvironment rest next).map project) =
            (concrete.invoke concretePlayers concreteEnvironment execution invocation).bind
              (fun next => abstract.runPolicies abstractPlayers abstractEnvironment rest
                (project next)) := by
                  apply FinDist.bind_congr
                  intro next hnext
                  exact ih next (hinvokeGood execution invocation next hgood hnext)
        _ = ((concrete.invoke concretePlayers concreteEnvironment execution invocation).map
              project).bind
                (abstract.runPolicies abstractPlayers abstractEnvironment rest) := by
              rw [FinDist.bind_map]
        _ = (abstract.invoke abstractPlayers abstractEnvironment (project execution)
              invocation).bind
                (abstract.runPolicies abstractPlayers abstractEnvironment rest) := by
              rw [hinvoke execution invocation hgood]

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_map_of_invoke' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_map_of_invoke
