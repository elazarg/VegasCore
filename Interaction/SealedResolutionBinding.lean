/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionLaws
import Interaction.SealedBinding
import Interaction.MessageApplicationPolicyLaws

/-! # Valid sealed prefixes in the resolving runtime

Before any timeout, accepted handles and opened values satisfy the original
sealed binding invariant. This remains true under arbitrary native policies:
timeout completion cannot be removed, and a tick that produces no timeout
preserves the event log. After a timeout the conditional invariant makes no
claim that a defaulted public value equals its private commitment.
-/

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

private theorem visit_clear (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat)
    (hclear : (runtime.visit resolveExpired state node).timeouts = []) :
    state.timeouts = [] ∧ (runtime.visit resolveExpired state node).events = state.events := by
  revert hclear
  unfold visit
  split
  · exact fun hclear => ⟨hclear, rfl⟩
  · split
    · exact fun hclear => ⟨hclear, rfl⟩
    · split
      · exact fun hclear => ⟨hclear, rfl⟩
      · dsimp only
        split
        · intro hclear
          have hempty : state.timeouts = [] := by simpa using hclear
          simp_all
        · split <;> simp_all [expire]
      · dsimp only
        split <;> simp_all [expire]

theorem refresh_clear (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value)
    (hclear : (runtime.refresh resolveExpired state).timeouts = []) :
    state.timeouts = [] ∧ (runtime.refresh resolveExpired state).events = state.events := by
  unfold refresh at hclear ⊢
  generalize List.range runtime.program.rules.length = nodes at hclear ⊢
  induction nodes generalizing state with
  | nil => exact ⟨hclear, rfl⟩
  | cons node rest ih =>
      obtain ⟨hhead, hevents⟩ := ih (runtime.visit resolveExpired state node) hclear
      obtain ⟨hbefore, hvisit⟩ := runtime.visit_clear resolveExpired state node hhead
      exact ⟨hbefore, hevents.trans hvisit⟩

variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}

def BeforeTimeoutBinding (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) : Prop :=
  state.visible.timeouts = [] → SealedProgram.BindingInvariant runtime.program
    ⟨state.service, MessagePool.empty Principal _, state.visible.events⟩

omit [DecidableEq Principal] [DecidableEq Value] in
theorem BeforeTimeoutBinding.initial : BeforeTimeoutBinding runtime runtime.initial := by
  intro _
  exact (SealedProgram.BindingInvariant.empty runtime.program).copy rfl
    (runtime.refresh_false_events {} rfl)

omit [DecidableEq Value] in
theorem BeforeTimeoutBinding.register {state : ApplicationState Principal Value}
    (invariant : BeforeTimeoutBinding runtime state)
    (owner : Principal) (slot : Nat) (value : Value) :
    BeforeTimeoutBinding runtime
      { state with service := (state.service.sealValue owner slot value).state } := by
  classical
  intro hclear
  exact (invariant hclear).step (.register owner slot value)

omit [DecidableEq Principal] [DecidableEq Value] in
theorem BeforeTimeoutBinding.tick {state : ApplicationState Principal Value}
    (invariant : BeforeTimeoutBinding runtime state) :
    BeforeTimeoutBinding runtime (runtime.tick state) := by
  intro hclear
  obtain ⟨hbefore, hevents⟩ := runtime.refresh_clear true
    { state.visible with clock := state.visible.clock + 1 } hclear
  exact (invariant hbefore).copy rfl hevents

theorem BeforeTimeoutBinding.handle {state next : ApplicationState Principal Value}
    (invariant : BeforeTimeoutBinding runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) : BeforeTimeoutBinding runtime next := by
  intro hclear
  unfold SealedResolution.handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp only [hvalid, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      obtain ⟨hbefore, hevents⟩ := runtime.refresh_clear false
        { state.visible with events := state.visible.events ++ [event] } hclear
      have hraw : runtime.program.validateMessage? state.service state.visible.events message =
          some event := by
        rw [← runtime.validateMessage?_no_timeout state hbefore message]
        exact hvalid
      have hincluded := (invariant hbefore).handle_preserved message
      simp only [SealedProgram.handle, hraw] at hincluded
      exact hincluded.copy rfl hevents

noncomputable section

/-- A timeout-free final execution cannot have resumed from a timed-out state.
This is a property of the actual application steps, for arbitrary policies and
finite invocation lists; it requires no fairness premise. -/
theorem runPolicies_clear_before
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support)
    (hclear : next.native.application.visible.timeouts = []) :
    execution.native.application.visible.timeouts = [] := by
  have h := runtime.messageApplication.runPolicies_application_invariant
    (fun state => state.visible.timeouts = [] → execution.native.application.visible.timeouts = [])
    ?_ ?_ ?_ players environment schedule execution next (fun h => h) hnext
  · exact h hclear
  · intro state who command hstate
    exact hstate
  · intro state message after hstate hafter hclear
    exact hstate ((runtime.handle_timeouts state after message hafter).symm.trans hclear)
  · intro state command after hstate hafter hclear
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate (runtime.refresh_clear true _ hclear).1

/-- The invariant is conditional on the actual runtime log, not a fairness
assumption. Arbitrary policy traffic and arbitrary clock triggers preserve it. -/
theorem runPolicies_beforeTimeoutBinding
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : runtime.messageApplication.PolicyExecution)
    (hinitial : BeforeTimeoutBinding runtime execution.native.application)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment
      schedule execution).support) : BeforeTimeoutBinding runtime next.native.application := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (BeforeTimeoutBinding runtime) ?_ ?_ ?_ players environment schedule
    execution next hinitial hnext
  · intro state who command hstate
    exact hstate.register who command.down.1 command.down.2
  · intro state message after hstate hafter
    exact hstate.handle message hafter
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate.tick

theorem BeforeTimeoutBinding.playerStep
    {execution next : runtime.messageApplication.PolicyExecution}
    (invariant : BeforeTimeoutBinding runtime execution.native.application)
    (who : Principal) (command : runtime.messageApplication.PlayerCommand)
    (hnext : next ∈ (runtime.messageApplication.playerStep who execution command).support) :
    BeforeTimeoutBinding runtime next.native.application := by
  apply runPolicies_beforeTimeoutBinding (fun _ _ _ => FinDist.pure command)
    (fun _ _ => FinDist.pure .wait) [.player who] execution next invariant
  simpa only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.pure_bind, FinDist.bind_pure] using hnext

theorem BeforeTimeoutBinding.environmentStep
    {execution next : runtime.messageApplication.PolicyExecution}
    (invariant : BeforeTimeoutBinding runtime execution.native.application)
    (command : runtime.messageApplication.EnvironmentPolicyCommand)
    (hnext : next ∈ (runtime.messageApplication.environmentPolicyStep execution command).support) :
    BeforeTimeoutBinding runtime next.native.application := by
  apply runPolicies_beforeTimeoutBinding (fun _ _ _ => FinDist.pure .wait)
    (fun _ _ => FinDist.pure command) [.environment] execution next invariant
  simpa only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.pure_bind, FinDist.bind_pure] using hnext

end

end Interaction.SealedResolution
