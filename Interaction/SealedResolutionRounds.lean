/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionLaws
import Interaction.MessageApplicationWirePolicy
import Interaction.MessageApplicationPolicyInvariant

/-! # Public-message rounds with fixed clock boundaries

Each round invokes the supplied principal roster, then gives the adaptive
wire policy a fixed number of delivery/inclusion opportunities, then advances
the clock once. The wire policy cannot advance it in those opportunities.
The clock command is an ordinary native action and is recorded by the shared
policy runner, including its environment history entry.

The roster and service-slot count are explicit model parameters. Liveness
needs every player to occur and sufficient deadline-relative service. Neither
that theorem nor a source payoff for an unfinished finite run is asserted here.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

def round (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution : runtime.messageApplication.PolicyExecution) :
    FinDist runtime.messageApplication.PolicyExecution :=
  let app := runtime.messageApplication
  (app.runPolicies players (app.wireEnvironment environment)
    (principals.map MessageApplication.Invocation.player ++
      List.replicate serviceSlots .environment) execution).bind fun next =>
    app.environmentPolicyStep next (.application ⟨()⟩)

def complete (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Bool :=
  (List.range runtime.program.rules.length).all state.completed

/-- Run at most the supplied number of rounds, stopping after application
completion. The result retains actual histories, pending traffic, and receipts. -/
def runRounds (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy) :
    Nat → runtime.messageApplication.PolicyExecution →
      FinDist runtime.messageApplication.PolicyExecution
  | 0, execution => FinDist.pure execution
  | count + 1, execution =>
      if runtime.complete execution.native.application.visible then FinDist.pure execution
      else (runtime.round principals serviceSlots players environment execution).bind
        (runtime.runRounds principals serviceSlots players environment count)

private theorem playerStep_clock (runtime : SealedResolution Principal Value) (who : Principal)
    (execution next : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.PlayerCommand)
    (hnext : next ∈ (runtime.messageApplication.playerStep who execution command).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock := by
  have hnative : next.native ∈ ((runtime.messageApplication.playerStep who execution command).map
      MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.playerStep_native] at hnative
  cases command <;>
    simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative <;>
    rw [hnative]
  rfl

private theorem wireStep_clock (runtime : SealedResolution Principal Value)
    (execution next : runtime.messageApplication.PolicyExecution) (command : WireCommand Principal)
    (hnext : next ∈ (runtime.messageApplication.environmentPolicyStep execution
      (command.toEnvironmentCommand runtime.messageApplication)).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock := by
  have hnative : next.native ∈ ((runtime.messageApplication.environmentPolicyStep execution
      (command.toEnvironmentCommand runtime.messageApplication)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  cases command with
  | deliver | wait =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rw [hnative]
  | «include» id =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      apply runtime.messageApplication.includePending_application_invariant
        (fun state => state.visible.clock = execution.native.application.visible.clock)
        ?_ execution.native id rfl
      intro state message after hstate hafter
      exact (runtime.handle_clock state after message hafter).trans hstate

/-- Arbitrary player policies and adaptive wire scheduling cannot advance the
clock. This includes every inclusion attempt, not only accepted traffic. -/
theorem runPolicies_wire_clock (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players
      (runtime.messageApplication.wireEnvironment environment) schedule execution).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock := by
  apply runtime.messageApplication.runPolicies_execution_invariant
    (fun current => current.native.application.visible.clock =
      execution.native.application.visible.clock)
    players (runtime.messageApplication.wireEnvironment environment) ?_ ?_
    schedule execution next rfl hnext
  · intro current who command final hcurrent _ hfinal
    exact (runtime.playerStep_clock who current final command hfinal).trans hcurrent
  · intro current command final hcurrent hcommand hfinal
    simp only [MessageApplication.wireEnvironment, FinDist.support_map, Set.mem_image] at hcommand
    obtain ⟨wire, _, hwire⟩ := hcommand
    rw [← hwire] at hfinal
    exact (runtime.wireStep_clock current final wire hfinal).trans hcurrent

private theorem clockStep_native (runtime : SealedResolution Principal Value)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.messageApplication.environmentPolicyStep execution
      (.application ⟨()⟩)).support) :
    next.native =
      { execution.native with application := runtime.tick execution.native.application } := by
  have hnative : next.native ∈ ((runtime.messageApplication.environmentPolicyStep execution
      (.application ⟨()⟩)).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  simpa only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    messageApplication, FinDist.map_pure, FinDist.mem_support_pure] using hnative

/-- Exactly one clock unit passes in a round, regardless of player traffic or
wire scheduling. Progress of a particular message is a separate service premise. -/
theorem round_clock (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.round principals serviceSlots players environment execution).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock + 1 := by
  simp only [round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  rw [runtime.clockStep_native middle next hnext, runtime.tick_clock,
    runtime.runPolicies_wire_clock players environment _ execution middle hmiddle]

/-- Immutable ideal registrations survive arbitrary native policies, including
clock resolution and post-timeout traffic. -/
theorem runPolicies_lookup_of_eq_some (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : execution.native.application.service.lookup handle = some value)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) :
    next.native.application.service.lookup handle = some value := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => state.service.lookup handle = some value) ?_ ?_ ?_
    players environment schedule execution next hlookup hnext
  · intro state who command hstate
    exact IdealCommitments.lookup_sealValue_of_eq_some state.service who
      command.down.1 command.down.2 handle value hstate
  · intro state message after hstate hafter
    rw [runtime.handle_service state after message hafter]
    exact hstate
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate

theorem runRounds_lookup_of_eq_some (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : execution.native.application.service.lookup handle = some value)
    (hnext : next ∈ (runtime.runRounds principals serviceSlots players environment
      count execution).support) :
    next.native.application.service.lookup handle = some value := by
  induction count generalizing execution with
  | zero =>
      simp only [runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hlookup
  | succ count ih =>
      simp only [runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hlookup
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        apply ih middle ?_ hnext
        simp only [round, FinDist.support_bind, Set.mem_iUnion] at hmiddle
        obtain ⟨serviced, hserviced, hmiddle⟩ := hmiddle
        rw [runtime.clockStep_native serviced middle hmiddle, runtime.tick_service]
        exact runtime.runPolicies_lookup_of_eq_some players
          (runtime.messageApplication.wireEnvironment environment) _ execution serviced
          handle value hlookup hserviced

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.round_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.round_clock

/-- info: 'Interaction.SealedResolution.runRounds_lookup_of_eq_some'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runRounds_lookup_of_eq_some
