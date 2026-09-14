/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidatePolicyEmbedding
import Interaction.SealedCandidateBinding

/-! # Honest owner memory under arbitrary candidate traffic

A player that submits commitments only for its own previously cached values
retains exact cache/catalog agreement. Every other player remains unrestricted:
it may prepare competing candidates or submit unprepared handles. The pool
invariant follows the designated owner's packets through delivery and replay.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}

private def OwnerPrepared (who : Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (message : Message Principal (SealedProgram.Payload Principal Value)) : Prop :=
  ∀ node handle, message.payload = .commitment node handle → message.sender = who →
    candidates.lookup handle ≠ .fresh

omit [DecidableEq Principal] [DecidableEq Value] in
private theorem OwnerPrepared.mono {who : Principal}
    {left right : CommitmentCandidates Principal Nat Value}
    (hfixed : ∀ handle, left.lookup handle ≠ .fresh → right.lookup handle = left.lookup handle)
    {message : Message Principal (SealedProgram.Payload Principal Value)}
    (h : OwnerPrepared who left message) : OwnerPrepared who right message := by
  intro node handle hpayload howner
  rw [hfixed handle (h node handle hpayload howner)]
  exact h node handle hpayload howner

private theorem candidateMessage?_commitment_sender (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat) (result)
    (hpayload : message.payload = .commitment node handle)
    (hresult : program.candidateMessage? candidates events message = some result) :
    message.sender = handle.1 := by
  simp only [SealedProgram.candidateMessage?, hpayload] at hresult
  cases hrule : program.rules[node]? with
  | none => simp [hrule] at hresult
  | some rule =>
      simp only [hrule] at hresult
      cases hkind : rule.kind with
      | disabled | reveal => simp only [hkind] at hresult; contradiction
      | commit owner =>
          simp only [hkind] at hresult
          split at hresult
          next hchecks => exact hchecks.1.trans hchecks.2.1.symm
          next => contradiction

private theorem candidateHandle_owner_lookup
    (who : Principal)
    (state next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hprepared : OwnerPrepared who state.service message)
    (hnext : runtime.candidateHandle state message = some next) (slot : Nat) :
    next.service.lookup (who, slot) = state.service.lookup (who, slot) := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        rcases (runtime.program.discharge state.visible.timeouts).candidateMessage?_effect
            state.service state.visible.events message result hmessage with
          ⟨node, handle, hpayload, rfl⟩ | ⟨node, handle, value, _hpayload, rfl⟩
        · by_cases heq : (who, slot) = handle
          · have hsender := candidateMessage?_commitment_sender _ _ _ _ node handle _
              hpayload hmessage
            have howner : message.sender = who := by rw [← heq] at hsender; exact hsender
            exact state.service.lookup_accept_eq_of_not_fresh (who, slot) handle
              (heq ▸ hprepared node handle hpayload howner)
          · exact state.service.lookup_accept_other handle (who, slot) heq
        · rfl

/-- One owner's candidate table equals its first-value command cache, and its
retained commitment packets refer to already fixed candidate meanings. -/
structure PreparedCandidateOwner (runtime : SealedResolution Principal Value)
    (who : Principal) (execution : runtime.candidateApplication.PolicyExecution) : Prop where
  memory : ∀ slot, execution.native.application.service.lookup (who, slot) =
    ((runtime.program.registrationEncoding slot).cachedValue runtime.candidateApplication
      (execution.principalHistory who) |>.map CommitmentCandidate.openable).getD .fresh
  private messages : execution.native.pool.Satisfies
    (OwnerPrepared who execution.native.application.service)

namespace PreparedCandidateOwner

variable {who : Principal}

theorem initial : PreparedCandidateOwner runtime who
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) :=
  ⟨fun _ => rfl, MessagePool.Satisfies.empty⟩

theorem playerStep (execution next : runtime.candidateApplication.PolicyExecution)
    (actor : Principal) (command : runtime.candidateApplication.PlayerCommand)
    (h : PreparedCandidateOwner runtime who execution)
    (hsubmit : ∀ payload, command = .submit payload →
      OwnerPrepared who execution.native.application.service
        ⟨(actor, execution.native.pool.nextSerial actor), payload⟩)
    (hnext : next ∈ (runtime.candidateApplication.playerStep actor execution command).support) :
    PreparedCandidateOwner runtime who next := by
  constructor
  · intro slot
    rw [ChoiceEncoding.playerStep_cachedValue runtime.candidateApplication
      (runtime.program.registrationEncoding slot) actor who execution next command hnext]
    cases command with
    | privateCommand command =>
        simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
          MessageApplication.step,
          FinDist.pure_bind, FinDist.mem_support_pure] at hnext
        subst next
        change (execution.native.application.service.prepare actor command.down.1
          command.down.2).lookup (who, slot) = _
        by_cases hactor : who = actor
        · subst actor
          rw [if_pos rfl]
          by_cases hslot : command.down.1 = slot
          · rw [hslot, CommitmentCandidates.lookup_prepare_self, h.memory slot]
            generalize (runtime.program.registrationEncoding slot).cachedValue
              runtime.candidateApplication (execution.principalHistory who) = cached
            cases cached <;>
              simp only [SealedProgram.registrationEncoding, hslot, ↓reduceIte] <;> rfl
          · rw [CommitmentCandidates.lookup_prepare_other _ who command.down.1 command.down.2
              (who, slot) (by intro heq; exact hslot (congrArg Prod.snd heq).symm), h.memory slot]
            generalize (runtime.program.registrationEncoding slot).cachedValue
              runtime.candidateApplication (execution.principalHistory who) = cached
            cases cached <;>
              simp only [SealedProgram.registrationEncoding, hslot, ↓reduceIte] <;> rfl
        · rw [CommitmentCandidates.lookup_prepare_other _ actor command.down.1 command.down.2
            (who, slot) (by intro heq; exact hactor (congrArg Prod.fst heq)), if_neg hactor]
          exact h.memory slot
    | submit payload | replay id | wait =>
        simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
          MessageApplication.step,
          FinDist.pure_bind, FinDist.mem_support_pure] at hnext
        subst next
        rw [h.memory slot]
        split
        · cases (runtime.program.registrationEncoding slot).cachedValue
            runtime.candidateApplication (execution.principalHistory who) <;> rfl
        · rfl
  · cases command with
    | privateCommand command =>
        simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
          MessageApplication.step,
          FinDist.pure_bind, FinDist.mem_support_pure] at hnext
        subst next
        exact h.messages.mono fun _ hmessage => hmessage.mono fun handle hfixed =>
          execution.native.application.service.lookup_prepare_eq_of_not_fresh handle actor
            command.down.1 command.down.2 hfixed
    | submit payload =>
        simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
          MessageApplication.step,
          FinDist.pure_bind, FinDist.mem_support_pure] at hnext
        subst next
        exact h.messages.submit actor payload (hsubmit payload rfl)
    | replay id =>
        simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
          MessageApplication.step,
          FinDist.pure_bind, FinDist.mem_support_pure] at hnext
        subst next
        exact h.messages.replay actor id
    | wait =>
        simp only [MessageApplication.playerStep, advance, PlayerCommand.toAction,
          FinDist.pure_bind, FinDist.mem_support_pure] at hnext
        subst next
        exact h.messages

private theorem includePending (execution : runtime.candidateApplication.PolicyExecution)
    (h : PreparedCandidateOwner runtime who execution) (id : MessageId Principal) :
    (∀ slot, CommitmentCandidates.lookup
      (runtime.candidateApplication.includePending execution.native id).application.service
        (who, slot) = execution.native.application.service.lookup (who, slot)) ∧
    (runtime.candidateApplication.includePending execution.native id).pool.Satisfies
      (OwnerPrepared who
        (runtime.candidateApplication.includePending execution.native id).application.service) := by
  cases hlookup : execution.native.pool.lookup id with
  | none =>
      rw [runtime.candidateApplication.includePending_missing execution.native id hlookup]
      exact ⟨fun _ => rfl, h.messages⟩
  | some message =>
      cases hresult : runtime.candidateHandle execution.native.application message with
      | none =>
          rw [runtime.candidateApplication.includePending_reject execution.native id message
            hlookup hresult]
          exact ⟨fun _ => rfl, h.messages.includePending id⟩
      | some result =>
          rw [runtime.candidateApplication.includePending_accept execution.native id message result
            hlookup hresult]
          refine ⟨candidateHandle_owner_lookup who _ _ message
            (h.messages.1 message (List.mem_of_find?_eq_some hlookup)) hresult, ?_⟩
          exact (h.messages.includePending id).mono fun _ hmessage => hmessage.mono
            (fun handle hfixed => runtime.candidateHandle_lookup_eq_of_not_fresh _ _ message
              handle hfixed hresult)

theorem environmentStep (execution next : runtime.candidateApplication.PolicyExecution)
    (command : runtime.candidateApplication.EnvironmentPolicyCommand)
    (h : PreparedCandidateOwner runtime who execution)
    (hnext : next ∈
      (runtime.candidateApplication.environmentPolicyStep execution command).support) :
    PreparedCandidateOwner runtime who next := by
  have hhistory := runtime.candidateApplication.environmentStep_principalHistory
    execution command next hnext
  have hnative : next.native ∈
      ((runtime.candidateApplication.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  have hmemory : ∀ slot, next.native.application.service.lookup (who, slot) =
      execution.native.application.service.lookup (who, slot) := by
    cases command with
    | deliver observer id | wait =>
        simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact fun _ => rfl
    | «include» id =>
        simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact (h.includePending execution id).1
    | application command =>
        simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step, candidateApplication,
          host, FinDist.map_pure, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact fun _ => rfl
  refine ⟨fun slot => (hmemory slot).trans (hhistory ▸ h.memory slot), ?_⟩
  cases command with
  | deliver observer id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact h.messages.deliver observer id
  | wait =>
      simp only [EnvironmentPolicyCommand.toAction,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact h.messages
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact (h.includePending execution id).2
  | application command =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step, candidateApplication,
        host, FinDist.map_pure, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact h.messages

end PreparedCandidateOwner

/-- The only discipline is imposed on the designated owner's commitment
submissions. All other players and the environment remain arbitrary. -/
theorem runPolicies_preparedCandidateOwner (who : Principal)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (hsubmit : ∀ execution payload, PreparedCandidateOwner runtime who execution →
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe _ execution.native who)).support →
      ∀ node handle, payload = .commitment node handle →
        execution.native.application.service.lookup handle ≠ .fresh)
    (schedule : List (@Invocation Principal)) (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support) :
    PreparedCandidateOwner runtime who next := by
  apply runtime.candidateApplication.runPolicies_execution_invariant
    (PreparedCandidateOwner runtime who) players environment ?_ ?_ schedule _ next
    PreparedCandidateOwner.initial hnext
  · intro execution actor command after h hcommand hafter
    apply h.playerStep execution after actor command ?_ hafter
    intro payload hpayload node handle hpacket howner
    change actor = who at howner
    subst actor
    subst command
    exact hsubmit execution payload h hcommand node handle hpacket
  · intro execution command after h _hcommand hafter
    exact h.environmentStep execution after command hafter

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_preparedCandidateOwner' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_preparedCandidateOwner
