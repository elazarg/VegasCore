/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolution
import Interaction.SealedResolutionLaws
import Interaction.SealedMemory

/-! # Local command memory through deadline resolution

The event projection forgets timing metadata, not wire observations or private
commands. The same registration encoding therefore reads the same first value
from either history. This projection does not assert equivalence of the two
runtime executions after a timeout.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Forget timing metadata while retaining the actual pool, receipts, and
private service for proofs about the sealed event kernel. -/
def eventState (runtime : SealedResolution Principal Value)
    (state : runtime.messageApplication.State) :
    (runtime.program.messageApplication (Value := Value)).State :=
  ⟨⟨state.application.service, state.application.visible.events⟩, state.pool, state.receipts⟩

def eventView (runtime : SealedResolution Principal Value)
    (view : runtime.messageApplication.View) :
    (runtime.program.messageApplication (Value := Value)).View :=
  ⟨view.messages, view.application.events, view.receipts⟩

def eventHistory (runtime : SealedResolution Principal Value)
    (history : List runtime.messageApplication.PlayerEntry) :
    List (runtime.program.messageApplication (Value := Value)).PlayerEntry :=
  history.map fun entry => ⟨runtime.eventView entry.beforeView, entry.command⟩

theorem eventHistory_cache (runtime : SealedResolution Principal Value)
    (encoding : ChoiceEncoding Value runtime.messageApplication.PlayerCommand)
    (history : List runtime.messageApplication.PlayerEntry) :
    encoding.cachedValue (runtime.program.messageApplication (Value := Value))
        (runtime.eventHistory history) =
      encoding.cachedValue runtime.messageApplication history := by
  induction history with
  | nil => rfl
  | cons entry rest ih =>
      simp only [eventHistory, List.map_cons, ChoiceEncoding.cachedValue]
      cases encoding.decode entry.command
      · exact ih
      · rfl

/-- Every first registered value is retained in its owner's actual local
command history. Timeout defaults affect public events, not this equality. -/
def RegistrationMemory (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution) : Prop :=
  ∀ owner slot, execution.native.application.service.lookup (owner, slot) =
    (runtime.program.registrationEncoding slot).cachedValue runtime.messageApplication
      (execution.principalHistory owner)

namespace RegistrationMemory

variable {runtime : SealedResolution Principal Value}

theorem initial : RegistrationMemory runtime
    (PolicyExecution.initial _ (State.initial _ runtime.initial)) := by
  intro owner slot
  rfl

theorem playerStep (execution next : runtime.messageApplication.PolicyExecution)
    (owner : Principal) (command : runtime.messageApplication.PlayerCommand)
    (hmemory : RegistrationMemory runtime execution)
    (hnext : next ∈ (runtime.messageApplication.playerStep owner execution command).support) :
    RegistrationMemory runtime next := by
  intro query slot
  rw [ChoiceEncoding.playerStep_cachedValue runtime.messageApplication
    (runtime.program.registrationEncoding slot) owner query execution next command hnext]
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      change (execution.native.application.service.sealValue
        owner command.down.1 command.down.2).state.lookup (query, slot) = _
      rw [IdealCommitments.lookup_sealValue, hmemory query slot]
      rfl
  | submit payload | replay id | wait =>
      simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      rw [hmemory query slot]
      split
      · cases (runtime.program.registrationEncoding slot).cachedValue runtime.messageApplication
          (execution.principalHistory query) <;> rfl
      · rfl

theorem environmentStep (execution next : runtime.messageApplication.PolicyExecution)
    (command : runtime.messageApplication.EnvironmentPolicyCommand)
    (hmemory : RegistrationMemory runtime execution)
    (hnext : next ∈ (runtime.messageApplication.environmentPolicyStep execution command).support) :
    RegistrationMemory runtime next := by
  intro query slot
  rw [runtime.messageApplication.environmentStep_principalHistory execution command next hnext]
  have hnative : next.native ∈
      ((runtime.messageApplication.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  cases command with
  | deliver observer id | wait =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hmemory query slot
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      have hservice := runtime.messageApplication.includePending_application_invariant
        (fun state => state.service = execution.native.application.service)
        (fun state message after hstate hafter =>
          (runtime.handle_service state after message hafter).trans hstate)
        execution.native id rfl
      simpa only [hservice] using hmemory query slot
  | application command =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step, messageApplication,
        FinDist.map_pure, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hmemory query slot

/-- The local cache and the ideal service agree under arbitrary native
policies, including repeated registrations, ticks, and execution after timeout. -/
theorem runPolicies (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hmemory : RegistrationMemory runtime execution)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) : RegistrationMemory runtime next := by
  apply runtime.messageApplication.runPolicies_execution_invariant (RegistrationMemory runtime)
    players environment ?_ ?_ schedule execution next hmemory hnext
  · intro current owner command final hcurrent _ hfinal
    exact playerStep current final owner command hcurrent hfinal
  · intro current command final hcurrent _ hfinal
    exact environmentStep current final command hcurrent hfinal

end RegistrationMemory

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.RegistrationMemory.runPolicies' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.RegistrationMemory.runPolicies
