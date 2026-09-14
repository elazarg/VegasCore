/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionLaws
import Interaction.MessageApplicationRounds
import Interaction.MessageApplicationPolicyInvariant

/-! # Public-message rounds with fixed clock boundaries

Each round invokes the supplied principal roster, then gives the adaptive
wire policy a fixed number of delivery/inclusion opportunities, then advances
the clock once. The wire policy cannot advance it in those opportunities.
The clock command is an ordinary native action and is recorded by the shared
policy runner, including its environment history entry.

The roster and service-slot count are explicit model parameters. Successful
honest play needs roster coverage and deadline-relative service. Finite
termination through defaults is proved separately in the termination module;
it does not require either condition or assign payoffs to unfinished runs.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal]

def complete (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) : Bool :=
  (List.range runtime.program.rules.length).all state.completed

/-- The clock and completion test depend only on the public resolution state,
for any hosted commitment service. -/
abbrev hostRoundDriver {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value Service)) :
    MessageApplication.RoundDriver (runtime.host prepare applyMessage) where
  boundary := ⟨()⟩
  complete state := runtime.complete state.visible

/-- The shared round driver instantiated with the registered commitment host. -/
abbrev roundDriver [DecidableEq Value] (runtime : SealedResolution Principal Value) :
    MessageApplication.RoundDriver runtime.messageApplication :=
  runtime.hostRoundDriver (Service := IdealCommitments Principal Nat Value)
    (fun state owner slot value => (state.sealValue owner slot value).state) runtime.handle

section Host

variable {Service : Type (max uPrincipal uValue)}
variable (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value Service))

private theorem playerStep_clock (who : Principal)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (command : (runtime.host prepare applyMessage).PlayerCommand)
    (hnext : next ∈ ((runtime.host prepare applyMessage).playerStep who execution
      command).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock := by
  have hnative : next.native ∈ (((runtime.host prepare applyMessage).playerStep who execution
    command).map
      MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.playerStep_native] at hnative
  cases command <;>
    simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative <;>
    rw [hnative]

private theorem wireStep_clock
    (hrecords : runtime.HandlerRecords applyMessage)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution) (command : WireCommand
      Principal)
    (hnext : next ∈ ((runtime.host prepare applyMessage).environmentPolicyStep execution
      (command.toEnvironmentCommand (runtime.host prepare applyMessage))).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock := by
  have hnative : next.native ∈ (((runtime.host prepare applyMessage).environmentPolicyStep execution
      (command.toEnvironmentCommand (runtime.host prepare applyMessage))).map
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
      apply (runtime.host prepare applyMessage).includePending_application_invariant
        (fun state => state.visible.clock = execution.native.application.visible.clock)
        ?_ execution.native id rfl
      intro state message after hstate hafter
      obtain ⟨event, hvisible⟩ := hrecords state message after hafter
      rw [hvisible, runtime.refresh_clock]
      exact hstate

/-- Arbitrary player policies and adaptive wire scheduling cannot advance the
clock. This includes every inclusion attempt, not only accepted traffic. -/
theorem runPolicies_wire_clock
    (hrecords : runtime.HandlerRecords applyMessage)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.host prepare applyMessage).runPolicies players
      ((runtime.host prepare applyMessage).wireEnvironment environment) schedule
        execution).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock := by
  apply (runtime.host prepare applyMessage).runPolicies_execution_invariant
    (fun current => current.native.application.visible.clock =
      execution.native.application.visible.clock)
    players ((runtime.host prepare applyMessage).wireEnvironment environment) ?_ ?_
    schedule execution next rfl hnext
  · intro current who command final hcurrent _ hfinal
    exact (runtime.playerStep_clock prepare applyMessage who current final command hfinal).trans
      hcurrent
  · intro current command final hcurrent hcommand hfinal
    simp only [MessageApplication.wireEnvironment, FinDist.support_map, Set.mem_image] at hcommand
    obtain ⟨wire, _, hwire⟩ := hcommand
    rw [← hwire] at hfinal
    exact (runtime.wireStep_clock prepare applyMessage hrecords current final wire hfinal).trans
      hcurrent

/-- The round boundary performs exactly the application's clock transition. -/
theorem clockStep_native
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.host prepare applyMessage).environmentPolicyStep execution
      (.application ⟨()⟩)).support) :
    next.native =
      { execution.native with application := runtime.tick execution.native.application } := by
  have hnative : next.native ∈ (((runtime.host prepare applyMessage).environmentPolicyStep execution
      (.application ⟨()⟩)).map MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  simpa only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    host, FinDist.map_pure, FinDist.mem_support_pure] using hnative

/-- Exactly one clock unit passes in a round, regardless of player traffic or
wire scheduling. Progress of a particular message is a separate service premise. -/
theorem round_clock
    (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).round
      principals serviceSlots players environment execution).support) :
    next.native.application.visible.clock = execution.native.application.visible.clock + 1 := by
  simp only [MessageApplication.RoundDriver.round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  rw [runtime.clockStep_native prepare applyMessage middle next hnext, runtime.tick_clock,
    runtime.runPolicies_wire_clock prepare applyMessage hrecords players environment _ execution
      middle hmiddle]

/-- If a bounded round run is still incomplete, every round in its budget
has advanced the clock once. No message-service premise is used. -/
theorem runRounds_clock_of_incomplete
    (hrecords : runtime.HandlerRecords applyMessage)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).WirePolicy)
    (count : Nat) (execution next : (runtime.host prepare applyMessage).PolicyExecution)
    (hnext : next ∈ ((runtime.hostRoundDriver prepare applyMessage).runRounds principals
      serviceSlots players environment
      count execution).support)
    (hincomplete : runtime.complete next.native.application.visible = false) :
    next.native.application.visible.clock = execution.native.application.visible.clock + count := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      omega
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        simp_all
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        rw [ih middle hnext,
          runtime.round_clock prepare applyMessage hrecords principals serviceSlots players
            environment execution middle hmiddle]
        omega

end Host

variable [DecidableEq Value]

/-- Immutable ideal registrations survive arbitrary native action sequences,
including clock resolution and post-timeout traffic. -/
theorem run_lookup_of_eq_some (runtime : SealedResolution Principal Value)
    (actions : List runtime.messageApplication.Action)
    (initial next : runtime.messageApplication.State)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : initial.application.service.lookup handle = some value)
    (hnext : next ∈ (runtime.messageApplication.run actions initial).support) :
    next.application.service.lookup handle = some value := by
  apply runtime.messageApplication.run_application_invariant
    (fun state => state.service.lookup handle = some value) ?_ ?_ ?_
    initial next actions hlookup hnext
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

/-- The policy runner inherits persistence from its native action execution. -/
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
  obtain ⟨actions, _, hnative⟩ := runtime.messageApplication.runPolicies_native_support
    players environment schedule execution next hnext
  exact runtime.run_lookup_of_eq_some actions execution.native next.native handle value
    hlookup hnative

theorem runRounds_lookup_of_eq_some (runtime : SealedResolution Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.WirePolicy)
    (count : Nat) (execution next : runtime.messageApplication.PolicyExecution)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : execution.native.application.service.lookup handle = some value)
    (hnext : next ∈ (runtime.roundDriver.runRounds principals serviceSlots players environment
      count execution).support) :
    next.native.application.service.lookup handle = some value := by
  induction count generalizing execution with
  | zero =>
      simp only [MessageApplication.RoundDriver.runRounds, FinDist.mem_support_pure] at hnext
      subst next
      exact hlookup
  | succ count ih =>
      simp only [MessageApplication.RoundDriver.runRounds] at hnext
      split at hnext
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hlookup
      · simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := hnext
        apply ih middle ?_ hnext
        simp only [MessageApplication.RoundDriver.round, FinDist.support_bind,
          Set.mem_iUnion] at hmiddle
        obtain ⟨serviced, hserviced, hmiddle⟩ := hmiddle
        rw [runtime.clockStep_native
          (fun (service : IdealCommitments Principal Nat Value) owner slot value =>
            (service.sealValue owner slot value).state) runtime.handle serviced middle hmiddle,
              runtime.tick_service]
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
