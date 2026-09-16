/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationSubmissionOrigin
import Vegas.Pending.EventPolicies
import Vegas.Pending.EventService

/-! # Canonical origins of retained event submissions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A commitment submitted by the compiled event policy has the canonical
owner/event handle and addresses an event owned by that player. -/
theorem compilePlayerPolicy_commitment_origin
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (handle : Handle graph)
    (supported : (.submit (.commitment event handle) : Command runtime) ∈
      (runtime.compilePlayerPolicy who policy history view).support) :
    handle = (who, eventSlot event) ∧ graph.actor? event = some who := by
  unfold compilePlayerPolicy at supported
  repeat' first | split at supported
  all_goals subst_vars
  all_goals try simp only [bindingStageCommand, resolutionSubmission,
    resolutionPayload] at supported
  all_goals repeat' first | split at supported
  all_goals try simp only [FinDist.mem_support_pure] at supported
  all_goals try { cases supported }
  all_goals try {
    rw [FinDist.support_map, Set.mem_image] at supported
    obtain ⟨action, _, impossible⟩ := supported
    cases impossible }
  have payloadEq := MessageInterface.PlayerCommand.submit.inj supported
  have address := congrArg (Payload.event? graph) payloadEq
  have canonical := congrArg (fun packet : Payload graph =>
    match packet with
    | .commitment _ candidate => some candidate
    | _ => none) payloadEq
  simp only [Payload.event?] at address
  simp only at canonical
  have eventEq := Option.some.inj address
  subst event
  exact ⟨Option.some.inj canonical, by assumption⟩

/-- Commitment-shape safety for messages authenticated as one prescribed
owner. Messages from every other sender are unrestricted. -/
def CanonicalCommitments (owner : Player) (message : Message Player (Payload graph)) : Prop :=
  message.sender = owner → ∀ event handle, message.payload = .commitment event handle →
    handle = (owner, eventSlot event) ∧ graph.actor? event = some owner

private theorem retained_of_satisfies
    {runtime : EventGraphRuntime graph} {owner : Player}
    {pool : MessagePool Player (Payload graph)}
    (safe : pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    {message : Message Player (Payload graph)}
    (retained : runtime.application.Retained pool message) :
    CanonicalCommitments owner message := by
  rcases retained with pending | ledger | ⟨who, inbox⟩ | ⟨who, sent⟩
  · exact safe.1 message pending
  · exact safe.2.1 message ledger
  · exact safe.2.2.1 who message inbox
  · exact safe.2.2.2 who message sent

/-- Every service instruction preserves the authenticated canonical shape of
commitments submitted by a prescribed owner. -/
theorem serviceStep_canonicalCommitments
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner) := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, commandMem, step⟩ := member
      apply runtime.application.playerStep_pool_satisfies _ who before after command safe _ step
      intro payload commandEq
      subst command
      intro sender event handle payloadEq
      have same : who = owner := sender
      subst who
      rw [ownerPolicy] at commandMem
      exact runtime.compilePlayerPolicy_commitment_origin owner policy
        (before.principalHistory owner)
        (MessageApplication.State.observe runtime.application before.native owner)
        event handle (payloadEq ▸ commandMem)
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.application.environmentPolicyStep_pool_satisfies _ before after command
        safe step
  | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.application.environmentPolicyStep_pool_satisfies _ before after _ safe member

/-- Arbitrary service instructions preserve canonical commitment provenance
for the one player whose policy is prescribed. Replay, delivery, and inclusion
retain the original authenticated sender and therefore need no special case. -/
theorem runServicePlan_canonicalCommitments
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    after.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner) := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      exact safe
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, first, last⟩ := member
      exact ih middle (serviceStep_canonicalCommitments runtime owner policy players ownerPolicy
        wire instruction before middle safe first) last

/-- Adaptive order selection does not affect the retained-message invariant;
the selected epoch plan preserves it pointwise. -/
theorem serviceEpoch_canonicalCommitments
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (member : after ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      before).support) :
    after.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner) := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨chosen, _, run⟩ := member
  exact runServicePlan_canonicalCommitments runtime owner policy players ownerPolicy wire
    (epochPlan chosen roster reactionRounds) before after safe run

/-- Canonical owner commitment provenance survives every adaptive service
epoch, including all reaction replays and environment inclusions. -/
theorem runService_canonicalCommitments
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner))
    (member : after ∈ (runtime.runService roster reactionRounds players wire order count
      before).support) :
    after.native.pool.Satisfies (CanonicalCommitments (graph := graph) owner) := by
  induction count generalizing before with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at member
      subst after
      exact safe
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, epoch, rest⟩ := member
      exact ih middle (serviceEpoch_canonicalCommitments runtime owner policy roster
        reactionRounds players ownerPolicy wire order before middle safe epoch) rest

/-- Retained owner-authored commitments after an actual service plan from the
native empty pool have canonical event handles and genuine owner provenance. -/
theorem runServicePlan_retained_commitment_origin
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runServicePlan players wire plan
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))).support)
    (message : Message Player (Payload graph))
    (retained : runtime.application.Retained after.native.pool message)
    (sender : message.sender = owner) (event : graph.EventId) (handle : Handle graph)
    (payloadEq : message.payload = .commitment event handle) :
    handle = (owner, eventSlot event) ∧ graph.actor? event = some owner := by
  have initialSafe :
      MessagePool.Satisfies
        (CanonicalCommitments (graph := graph) owner)
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial inputs))).native.pool := by
    exact ⟨fun _ member => (List.not_mem_nil member).elim,
      fun _ member => (List.not_mem_nil member).elim,
      fun _ _ member => (List.not_mem_nil member).elim,
      fun _ _ member => (List.not_mem_nil member).elim⟩
  have safe := runServicePlan_canonicalCommitments runtime owner policy players ownerPolicy wire
    plan _ after initialSafe member
  exact (retained_of_satisfies safe retained) sender event handle payloadEq

/-- The adaptive finite service from native initialization retains only
canonical commitments authenticated as the prescribed owner. -/
theorem runService_retained_commitment_origin
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runService roster reactionRounds players wire order count
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))).support)
    (message : Message Player (Payload graph))
    (retained : runtime.application.Retained after.native.pool message)
    (sender : message.sender = owner) (event : graph.EventId) (handle : Handle graph)
    (payloadEq : message.payload = .commitment event handle) :
    handle = (owner, eventSlot event) ∧ graph.actor? event = some owner := by
  have initialSafe : MessagePool.Satisfies
      (CanonicalCommitments (graph := graph) owner)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial inputs))).native.pool := MessagePool.Satisfies.empty
  have safe := runService_canonicalCommitments runtime owner policy roster reactionRounds
    players ownerPolicy wire order count _ after initialSafe member
  exact (retained_of_satisfies safe retained) sender event handle payloadEq

end Vegas.EventGraphRuntime
