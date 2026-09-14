/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionRounds
import Interaction.MessageApplicationPolicyCheckpoint

/-! # Registration provenance through continuing resolution

Every private value was registered by its owner. Delivery, inclusion, rejected
traffic, and timeout defaults cannot introduce a private service entry. The
trace used for this statement is proof-facing, not a player observation.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable (runtime : SealedResolution Principal Value)

private theorem step_lookup_origin (initial next : runtime.messageApplication.State)
    (action : runtime.messageApplication.Action)
    (hnext : next ∈ (runtime.messageApplication.step initial action).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.application.service.lookup (owner, slot) = some value) :
    initial.application.service.lookup (owner, slot) = some value ∨
      action = .privateCommand owner ⟨(slot, value)⟩ := by
  cases action with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hnext
      subst next
      rcases IdealCommitments.lookup_sealValue_origin initial.application.service
        who command.down.1 command.down.2 (owner, slot) value hlookup with hprior | ⟨heq, hvalue⟩
      · exact Or.inl hprior
      · right
        rcases command with ⟨index, submitted⟩
        obtain ⟨rfl, hslot⟩ := Prod.mk.inj heq
        dsimp only at hslot hvalue
        subst slot value
        rfl
  | submit who payload | replay who id | deliver who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inl hlookup
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hnext
      subst next
      have hservice := runtime.messageApplication.includePending_application_invariant
        (fun state => state.service = initial.application.service)
        (fun state message after hstate hafter =>
          (runtime.handle_service state after message hafter).trans hstate) initial id rfl
      exact Or.inl (hservice ▸ hlookup)
  | environment command =>
      simp only [MessageApplication.step, messageApplication, FinDist.map_pure,
        FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inl hlookup

/-- An invocation can create a private entry only by selecting its owner's
registration command. The conclusion exposes the policy input before that
invocation, rather than only the action retained in the final trace. -/
theorem invoke_lookup_origin
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (initial next : runtime.messageApplication.PolicyExecution)
    (invocation : @Invocation Principal)
    (hnext : next ∈ (runtime.messageApplication.invoke players environment initial
      invocation).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.native.application.service.lookup (owner, slot) = some value) :
    initial.native.application.service.lookup (owner, slot) = some value ∨
      .privateCommand ⟨(slot, value)⟩ ∈
        (players owner (initial.principalHistory owner)
          (State.observe runtime.messageApplication initial.native owner)).support :=
  runtime.messageApplication.invoke_privateCommand_origin
    (fun state => state.application.service.lookup (owner, slot) = some value)
    owner ⟨(slot, value)⟩
    (fun before after action hstep hvalue =>
      runtime.step_lookup_origin before after action hstep owner slot value hvalue)
    players environment initial next invocation hnext hlookup

/-- A new service entry present at the cutoff has a genuine registration
checkpoint strictly before that cutoff. The owner policy may be arbitrary and
randomized; no fairness, positive probability under a second policy, or
assumption about the scheduler's observations is used. -/
theorem registrationCheckpoint_selected
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (initial : runtime.messageApplication.PolicyExecution)
    (trace : runtime.messageApplication.PolicyTrace)
    (htrace : trace ∈ (runtime.messageApplication.tracePolicies players environment schedule
      initial).support)
    (stop : runtime.messageApplication.PolicyExecution → Bool)
    (owner : Principal) (slot : Nat) (value : Value)
    (hinitial : initial.native.application.service.lookup (owner, slot) ≠ some value)
    (hlookup : (trace.prefixThrough stop).last.native.application.service.lookup (owner, slot) =
      some value) :
    let selected := runtime.messageApplication.commandCheckpoint players trace stop owner
      (.privateCommand ⟨(slot, value)⟩)
    stop selected = false ∧ .privateCommand ⟨(slot, value)⟩ ∈
      (players owner (selected.principalHistory owner)
        (State.observe runtime.messageApplication selected.native owner)).support :=
  runtime.messageApplication.commandCheckpoint_selected_of_new_fact players environment
    (fun execution => execution.native.application.service.lookup (owner, slot) = some value)
    owner (.privateCommand ⟨(slot, value)⟩)
    (fun before after invocation hstep hvalue =>
      runtime.invoke_lookup_origin players environment before after invocation hstep
        owner slot value hvalue)
    schedule initial trace htrace stop hinitial hlookup

/-- Native private entries originate in the initial service or in an actual
owner-authenticated registration in the supplied action sequence. -/
theorem run_lookup_origin (actions : List runtime.messageApplication.Action)
    (initial next : runtime.messageApplication.State)
    (hnext : next ∈ (runtime.messageApplication.run actions initial).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.application.service.lookup (owner, slot) = some value) :
    initial.application.service.lookup (owner, slot) = some value ∨
      .privateCommand owner ⟨(slot, value)⟩ ∈ actions := by
  induction actions generalizing initial with
  | nil =>
      simp only [MessageApplication.run, FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inl hlookup
  | cons action rest ih =>
      simp only [MessageApplication.run, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      rcases ih middle hnext with hprior | hrest
      · rcases runtime.step_lookup_origin initial middle action hmiddle owner slot value hprior
          with hprior | haction
        · exact Or.inl hprior
        · exact Or.inr (List.mem_cons.mpr (Or.inl haction.symm))
      · exact Or.inr (List.mem_cons_of_mem _ hrest)

theorem runPolicies_lookup_origin
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.native.application.service.lookup (owner, slot) = some value) :
    .privateCommand owner ⟨(slot, value)⟩ ∈ next.nativeTrace := by
  have hnative := runtime.messageApplication.runPolicies_initial_native_support
    players environment schedule (State.initial _ runtime.initial) next hnext
  rcases runtime.run_lookup_origin next.nativeTrace _ _ hnative owner slot value hlookup
    with hprior | hrecorded
  · cases hprior
  · exact hrecorded

/-- A registration attempt leaves its owner-scoped slot occupied. Repeated
attempts may retain an earlier value, so no equality with the last payload is
claimed. The occupied entry survives all later native actions. -/
theorem run_registration_occupied (actions : List runtime.messageApplication.Action)
    (initial next : runtime.messageApplication.State)
    (hnext : next ∈ (runtime.messageApplication.run actions initial).support)
    (owner : Principal) (slot : Nat) (submitted : Value)
    (hrecord : .privateCommand owner ⟨(slot, submitted)⟩ ∈ actions) :
    ∃ value, next.application.service.lookup (owner, slot) = some value := by
  induction actions generalizing initial with
  | nil => simp only [List.not_mem_nil] at hrecord
  | cons action rest ih =>
      simp only [MessageApplication.run, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      rcases List.mem_cons.mp hrecord with heq | hrest
      · subst action
        simp only [MessageApplication.step, FinDist.mem_support_pure] at hmiddle
        subst middle
        have hoccupied : ∃ value,
            (initial.application.service.sealValue owner slot submitted).state.lookup
              (owner, slot) = some value := by
          rw [IdealCommitments.lookup_sealValue, if_pos rfl]
          cases initial.application.service.lookup (owner, slot) <;> simp
        obtain ⟨value, hvalue⟩ := hoccupied
        exact ⟨value, runtime.run_lookup_of_eq_some rest _ next (owner, slot)
          value hvalue hnext⟩
      · exact ih middle hnext hrest

theorem runPolicies_registration_occupied
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (next : runtime.messageApplication.PolicyExecution)
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).support)
    (owner : Principal) (slot : Nat) (submitted : Value)
    (hrecord : .privateCommand owner ⟨(slot, submitted)⟩ ∈ next.nativeTrace) :
    ∃ value, next.native.application.service.lookup (owner, slot) = some value :=
  runtime.run_registration_occupied next.nativeTrace _ _
    (runtime.messageApplication.runPolicies_initial_native_support players environment
      schedule (State.initial _ runtime.initial) next hnext) owner slot submitted hrecord

end Interaction.SealedResolution
