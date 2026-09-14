/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateBinding

/-! # Provenance of private candidate values

Openable values originate in their owner's private preparation commands.
Acceptance may instead fix an unopenable candidate, but cannot create an
opening. Every preparation leaves its slot nonfresh. These facts concern the
actual native runner, including arbitrary traffic and post-timeout execution.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue
variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable (runtime : SealedResolution Principal Value)

/-- Handling a message cannot create a previously unavailable opening. -/
theorem candidateHandle_openable_origin
    (initial next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle initial message = some next)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : next.service.lookup handle = .openable value) :
    initial.service.lookup handle = .openable value := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge initial.visible.timeouts).candidateMessage?
        initial.service initial.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        rcases (runtime.program.discharge initial.visible.timeouts).candidateMessage?_effect
            initial.service initial.visible.events message result hmessage with
          ⟨node, selected, _hp, rfl⟩ | ⟨node, selected, claimed, _hp, rfl⟩
        · exact (initial.service.lookup_accept_openable_iff selected handle value).mp hlookup
        · exact hlookup

private theorem step_candidate_openable_origin (initial next : runtime.candidateApplication.State)
    (action : runtime.candidateApplication.Action)
    (hnext : next ∈ (runtime.candidateApplication.step initial action).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.application.service.lookup (owner, slot) = .openable value) :
    initial.application.service.lookup (owner, slot) = .openable value ∨
      action = .privateCommand owner ⟨(slot, value)⟩ := by
  cases action with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hnext
      subst next
      rcases initial.application.service.lookup_prepare_openable_origin who
        command.down.1 command.down.2 (owner, slot) value hlookup with hprior | ⟨heq, hvalue⟩
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
      apply Or.inl
      have hpreserved := runtime.candidateApplication.includePending_application_invariant
        (fun state => state.service.lookup (owner, slot) = .openable value →
          initial.application.service.lookup (owner, slot) = .openable value)
        (fun state message after hstate hafter hvalue =>
          hstate (runtime.candidateHandle_openable_origin state after message hafter
            (owner, slot) value hvalue)) initial id (fun h => h)
      exact hpreserved hlookup
  | environment command =>
      simp only [MessageApplication.step, candidateApplication, host, FinDist.map_pure,
        FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inl hlookup

/-- Any opening available after native execution was initially present or
was supplied by a recorded owner preparation. -/
theorem run_candidate_openable_origin (actions : List runtime.candidateApplication.Action)
    (initial next : runtime.candidateApplication.State)
    (hnext : next ∈ (runtime.candidateApplication.run actions initial).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.application.service.lookup (owner, slot) = .openable value) :
    initial.application.service.lookup (owner, slot) = .openable value ∨
      .privateCommand owner ⟨(slot, value)⟩ ∈ actions := by
  induction actions generalizing initial with
  | nil =>
      simp only [MessageApplication.run, FinDist.mem_support_pure] at hnext
      subst next
      exact Or.inl hlookup
  | cons action rest ih =>
      simp only [MessageApplication.run, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      rcases ih middle hnext with hprior | hrecorded
      · rcases runtime.step_candidate_openable_origin initial middle action hmiddle owner slot
          value hprior with hbefore | heq
        · exact Or.inl hbefore
        · exact Or.inr (List.mem_cons.mpr (Or.inl heq.symm))
      · exact Or.inr (List.mem_cons_of_mem _ hrecorded)

/-- Every openable candidate in an actual initialized policy run has an
owner preparation in its proof-facing native trace. -/
theorem runPolicies_candidate_openable_origin
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support)
    (owner : Principal) (slot : Nat) (value : Value)
    (hlookup : next.native.application.service.lookup (owner, slot) = .openable value) :
    .privateCommand owner ⟨(slot, value)⟩ ∈ next.nativeTrace := by
  have hnative := runtime.candidateApplication.runPolicies_initial_native_support
    players environment schedule (State.initial _ runtime.candidateInitial) next hnext
  rcases runtime.run_candidate_openable_origin next.nativeTrace _ _ hnative owner slot value
    hlookup with hprior | hrecorded
  · cases hprior
  · exact hrecorded

/-- A preparation leaves its candidate nonfresh. It may retain an earlier
opening or a permanently unopenable meaning, so success is not assumed. -/
theorem run_candidate_preparation_fixed (actions : List runtime.candidateApplication.Action)
    (initial next : runtime.candidateApplication.State)
    (hnext : next ∈ (runtime.candidateApplication.run actions initial).support)
    (owner : Principal) (slot : Nat) (submitted : Value)
    (hrecord : .privateCommand owner ⟨(slot, submitted)⟩ ∈ actions) :
    next.application.service.lookup (owner, slot) ≠ .fresh := by
  induction actions generalizing initial with
  | nil => simp only [List.not_mem_nil] at hrecord
  | cons action rest ih =>
      simp only [MessageApplication.run, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      rcases List.mem_cons.mp hrecord with heq | hrest
      · subst action
        simp only [MessageApplication.step, FinDist.mem_support_pure] at hmiddle
        subst middle
        have hfixed : (initial.application.service.prepare owner slot submitted).lookup
            (owner, slot) ≠ .fresh := by
          rw [CommitmentCandidates.lookup_prepare_self]
          cases initial.application.service.lookup (owner, slot) <;> simp
        rw [runtime.run_candidate_lookup_of_not_fresh rest _ next (owner, slot) hfixed hnext]
        exact hfixed
      · exact ih middle hnext hrest

theorem runPolicies_candidate_preparation_fixed
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support)
    (owner : Principal) (slot : Nat) (submitted : Value)
    (hrecord : .privateCommand owner ⟨(slot, submitted)⟩ ∈ next.nativeTrace) :
    next.native.application.service.lookup (owner, slot) ≠ .fresh :=
  runtime.run_candidate_preparation_fixed next.nativeTrace _ _
    (runtime.candidateApplication.runPolicies_initial_native_support players environment
      schedule (State.initial _ runtime.candidateInitial) next hnext) owner slot submitted hrecord

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_candidate_openable_origin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_openable_origin
