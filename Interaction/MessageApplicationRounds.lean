/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationWirePolicy
import Interaction.MessageApplicationPolicyLaws

/-! # Bounded rounds of the shared message interpreter

A driver supplies a fixed application command at each round boundary and a
completion test. Each round invokes a principal roster, offers a fixed number
of adaptive wire opportunities, and executes that boundary command. This module
does not require the command to be a clock or assert termination before the
budget; those properties belong to the application's instantiation.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal}

structure RoundDriver (app : MessageApplication Principal) where
  boundary : app.EnvironmentCommand
  complete : app.Application → Bool

namespace RoundDriver

variable {app : MessageApplication Principal} [DecidableEq Principal]

def round (driver : RoundDriver app) (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy) (environment : app.WirePolicy)
    (execution : app.PolicyExecution) : FinDist app.PolicyExecution :=
  (app.runPolicies players (app.wireEnvironment environment)
    (principals.map Invocation.player ++ List.replicate serviceSlots .environment)
    execution).bind fun next => app.environmentPolicyStep next (.application driver.boundary)

/-- Execute at most the supplied number of rounds, stopping at the initial
state or the first completed round. No discarded suffix is executed. -/
def runRounds (driver : RoundDriver app) (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy) (environment : app.WirePolicy) :
    Nat → app.PolicyExecution → FinDist app.PolicyExecution
  | 0, execution => FinDist.pure execution
  | count + 1, execution =>
      if driver.complete execution.native.application then FinDist.pure execution
      else (driver.round principals serviceSlots players environment execution).bind
        (driver.runRounds principals serviceSlots players environment count)

theorem runRounds_of_complete (driver : RoundDriver app)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy) (environment : app.WirePolicy)
    (count : Nat) (execution : app.PolicyExecution)
    (hcomplete : driver.complete execution.native.application = true) :
    driver.runRounds principals serviceSlots players environment count execution =
      FinDist.pure execution := by
  cases count <;> simp [runRounds, hcomplete]

/-- Native application invariants survive the actual early-stopping driver,
including its fixed boundary commands and arbitrary wire/player policies. -/
theorem runRounds_application_invariant (driver : RoundDriver app)
    (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hhandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy) (environment : app.WirePolicy)
    (count : Nat) (execution next : app.PolicyExecution)
    (hinitial : invariant execution.native.application)
    (hnext : next ∈ (driver.runRounds principals serviceSlots players environment
      count execution).support) : invariant next.native.application := by
  induction count generalizing execution with
  | zero =>
      simp only [runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | succ count ih =>
      simp only [runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinitial
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        simp only [round, FinDist.support_bind, Set.mem_iUnion] at hmiddle
        obtain ⟨serviced, hserviced, hmiddle⟩ := hmiddle
        have hservicedInvariant := app.runPolicies_application_invariant
          invariant hprivate hhandler henvironment players (app.wireEnvironment environment)
          _ execution serviced hinitial hserviced
        have hnative : middle.native ∈ ((app.environmentPolicyStep serviced
            (.application driver.boundary)).map
              MessageInterface.PolicyExecution.native).support := by
          rw [FinDist.support_map]
          exact ⟨middle, hmiddle, rfl⟩
        rw [app.environmentStep_native] at hnative
        apply ih middle ?_ hnext
        exact app.step_application_invariant invariant hprivate hhandler henvironment
          serviced.native middle.native (.environment driver.boundary) hservicedInvariant hnative

/-- Splitting the budget preserves actual early stopping and its execution law. -/
theorem runRounds_add (driver : RoundDriver app)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy) (environment : app.WirePolicy)
    (first rest : Nat) (execution : app.PolicyExecution) :
    driver.runRounds principals serviceSlots players environment (first + rest) execution =
      (driver.runRounds principals serviceSlots players environment first execution).bind
        (driver.runRounds principals serviceSlots players environment rest) := by
  induction first generalizing execution with
  | zero => simp [runRounds]
  | succ first ih =>
      by_cases hcomplete : driver.complete execution.native.application = true
      · simp [driver.runRounds_of_complete principals serviceSlots players environment _ _
          hcomplete]
      · simp only [Nat.succ_add, runRounds, hcomplete, Bool.false_eq_true, ↓reduceIte,
          FinDist.bind_bind]
        apply FinDist.bind_congr
        intro middle _
        exact ih middle

/-- An exact round embedding that preserves the completion test also preserves
the stopped driver. The reachable invariant is needed only on source rounds. -/
theorem runRounds_map {target : MessageApplication Principal}
    (driver : RoundDriver app) (targetDriver : RoundDriver target)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy) (wire : app.WirePolicy)
    (targetPlayers : Principal → target.PlayerPolicy) (targetWire : target.WirePolicy)
    (project : app.PolicyExecution → target.PolicyExecution)
    (Good : app.PolicyExecution → Prop)
    (hcomplete : ∀ execution, Good execution →
      targetDriver.complete (project execution).native.application =
        driver.complete execution.native.application)
    (hround : ∀ execution, Good execution →
      (driver.round principals serviceSlots players wire execution).map project =
        targetDriver.round principals serviceSlots targetPlayers targetWire (project execution))
    (hgood : ∀ execution next, Good execution →
      next ∈ (driver.round principals serviceSlots players wire execution).support → Good next)
    (count : Nat) (execution : app.PolicyExecution) (h : Good execution) :
    (driver.runRounds principals serviceSlots players wire count execution).map project =
      targetDriver.runRounds principals serviceSlots targetPlayers targetWire count
        (project execution) := by
  induction count generalizing execution with
  | zero => simp only [runRounds, FinDist.map_pure]
  | succ count ih =>
      simp only [runRounds, hcomplete execution h]
      split
      · exact FinDist.map_pure _ _
      · rw [FinDist.map_bind, ← hround execution h, FinDist.bind_map]
        apply FinDist.bind_congr
        intro next hnext
        exact ih next (hgood execution next h hnext)

end RoundDriver

end Interaction.MessageApplication
