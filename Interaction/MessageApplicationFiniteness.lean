/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationWirePolicy

/-! # Finitely branching message applications

Transport, inclusion, and private commands are deterministic, so a native step
branches only through the application's environment kernel. Policies branch
through their own laws. When all of these have finite support, every native
step and every policy invocation has finite support.
-/

noncomputable section

namespace Interaction.MessageApplication

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- Every environment kernel of the application has finite support. -/
def FiniteEnvironment : Prop :=
  ∀ application command, (app.environmentStep application command).support.Finite

/-- A player policy draws finitely many commands at every local input. -/
def PlayerPolicy.FiniteSupport {app : MessageApplication Principal}
    (policy : app.PlayerPolicy) : Prop :=
  ∀ past view, (policy past view).support.Finite

/-- An environment policy draws finitely many commands at every input. -/
def EnvironmentPolicy.FiniteSupport {app : MessageApplication Principal}
    (policy : app.EnvironmentPolicy) : Prop :=
  ∀ past view, (policy past view).support.Finite

/-- A wire policy draws finitely many commands at every input. -/
def WirePolicy.FiniteSupport {app : MessageApplication Principal}
    (policy : app.WirePolicy) : Prop :=
  ∀ past view, (policy past view).support.Finite

variable {app} [DecidableEq Principal]

theorem step_support_finite (finite : app.FiniteEnvironment) (state : app.State)
    (action : app.Action) : (app.step state action).support.Finite := by
  cases action with
  | environment command =>
      simp only [step, PMF.support_map]
      exact (finite _ command).image _
  | _ => simp [step]

theorem advance_support_finite (finite : app.FiniteEnvironment)
    (execution : app.PolicyExecution) (action : Option app.Action) :
    (app.advance execution action).support.Finite := by
  cases action with
  | none => simp [advance]
  | some action =>
      rw [advance, PMF.support_bind]
      exact (step_support_finite finite _ action).biUnion fun _ _ => by simp

theorem playerStep_support_finite (finite : app.FiniteEnvironment) (who : Principal)
    (execution : app.PolicyExecution) (command : app.PlayerCommand) :
    (app.playerStep who execution command).support.Finite := by
  rw [playerStep, PMF.support_bind]
  exact (advance_support_finite finite _ _).biUnion fun _ _ => by simp

theorem environmentPolicyStep_support_finite (finite : app.FiniteEnvironment)
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand) :
    (app.environmentPolicyStep execution command).support.Finite := by
  rw [environmentPolicyStep, PMF.support_bind]
  exact (advance_support_finite finite _ _).biUnion fun _ _ => by simp

omit [DecidableEq Principal] in
theorem wireEnvironment_finiteSupport {policy : app.WirePolicy}
    (finite : policy.FiniteSupport) : (app.wireEnvironment policy).FiniteSupport := by
  intro past view
  rw [wireEnvironment, PMF.support_map]
  exact (finite past view).image _

theorem invoke_support_finite (finite : app.FiniteEnvironment)
    {players : Principal → app.PlayerPolicy} {environment : app.EnvironmentPolicy}
    (playersFinite : ∀ who, (players who).FiniteSupport)
    (environmentFinite : environment.FiniteSupport)
    (execution : app.PolicyExecution) (invocation : @Invocation Principal) :
    (app.invoke players environment execution invocation).support.Finite := by
  cases invocation with
  | player who =>
      rw [invoke, PMF.support_bind]
      exact (playersFinite who _ _).biUnion fun _ _ => playerStep_support_finite finite _ _ _
  | environment =>
      rw [invoke, PMF.support_bind]
      exact (environmentFinite _ _).biUnion fun _ _ =>
        environmentPolicyStep_support_finite finite _ _

end Interaction.MessageApplication
