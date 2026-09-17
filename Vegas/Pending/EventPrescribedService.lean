/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedBlock
import Vegas.Pending.EventPrescribedAction
import Vegas.Pending.EventResolutionOrigin
import Vegas.Pending.EventHonestDeadline

/-! # Actual prescribed-owner event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Only the live activations owned by one prescribed player need the one-block
age bound. No timing condition is imposed on events owned by arbitrary players. -/
def State.OwnerActivationAgeOne (state : State graph) (owner : Player) : Prop :=
  ∀ event, graph.actor? event = some owner → ∀ entered,
    state.activatedAt event = some entered →
    event ∉ state.config.cut.completed → state.clock - entered ≤ 1

theorem State.ownerActivationAgeOne_initial (inputs : graph.Inputs) (owner : Player) :
    (State.initial inputs).OwnerActivationAgeOne owner := by
  intro event _ entered activated unfinished
  exact State.initial_activationAgeOne inputs event entered activated unfinished

omit [DecidableEq Player] in
theorem State.OwnerActivationAgeOne.withinDeadline
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    {state : State graph} {owner : Player}
    (age : state.OwnerActivationAgeOne owner) (event : graph.EventId)
    (actor : graph.actor? event = some owner) (entered : Nat)
    (activated : state.activatedAt event = some entered)
    (unfinished : event ∉ state.config.cut.completed) :
    state.WithinDeadline runtime event :=
  withinDeadline_of_age_le_one runtime feasible state event entered activated
    (age event actor entered activated unfinished)

omit [DecidableEq Player] in
theorem State.OwnerActivationAgeOne.of_zero_progress
    {inputs : graph.Inputs} {before after : State graph} {owner : Player}
    (age : before.OwnerActivationAgeOne owner)
    (progress : State.ServiceProgress inputs 0 before after)
    (origin : State.ActivationOrigin before after) :
    after.OwnerActivationAgeOne owner := by
  intro event actor entered activated unfinished
  exact State.age_le_one_of_zero_progress event (age event actor) progress origin entered activated
    unfinished

omit [DecidableEq Player] in
theorem State.OwnerActivationAgeOne.after_epoch
    {inputs : graph.Inputs} {before after : State graph} {owner : Player}
    (progress : State.ServiceProgress inputs 1 before after)
    (origin : State.ActivationOrigin before after)
    (serviced : ∀ event, graph.actor? event = some owner → ∀ entered,
      before.activatedAt event = some entered → event ∈ after.config.cut.completed) :
    after.OwnerActivationAgeOne owner := by
  intro event actor entered activated unfinished
  exact State.age_le_one_after_epoch event progress origin (serviced event actor) entered activated
    unfinished

/-- A feasible prescribed-owner event cannot be expired while its owner-local
age bound holds. Other owners may have arbitrarily old events. -/
theorem serviceStep_expire_owner_application_eq
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (owner : Player)
    (execution next : runtime.application.PolicyExecution)
    (age : execution.native.application.OwnerActivationAgeOne owner)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (member : next ∈
      (runtime.serviceStep players wire (.expire event) execution).support) :
    next.native.application = execution.native.application :=
  runtime.serviceStep_expire_application_eq players wire event (feasible event) execution next
    (age event actor) member

/-- The actual adaptive epoch re-establishes the owner-local one-block bound
once all of that owner's entry activations were serviced during the epoch. -/
theorem serviceEpoch_ownerActivationAgeOne
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (owner : Player) (before after : runtime.application.PolicyExecution)
    (invariant : before.native.application.Invariant inputs)
    (member : after ∈ (runtime.serviceEpoch roster reactionRounds players wire order
      before).support)
    (serviced : ∀ event, graph.actor? event = some owner → ∀ entered,
      before.native.application.activatedAt event = some entered →
        event ∈ after.native.application.config.cut.completed) :
    after.native.application.OwnerActivationAgeOne owner := by
  apply State.OwnerActivationAgeOne.after_epoch
    (runtime.serviceEpoch_facts inputs roster reactionRounds players wire order before after
      invariant member)
    (runtime.serviceEpoch_activationOrigin inputs roster reactionRounds players wire order before
      after invariant member)
    serviced

/-- Every matching pending binding packet from a prescribed owner is locally
acceptable at a timely ready event. -/
theorem matching_binding_packets_accepted
    (runtime : EventGraphRuntime graph) (owner : Player)
    (execution : runtime.application.PolicyExecution)
    (safe : execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (resources : execution.native.application.CanonicalResources owner)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event) :
    ∀ message ∈ execution.native.pool.pending, Payload.Matches event owner message →
      ∃ next, runtime.handle execution.native.application message = some next := by
  rintro ⟨⟨sender, nonce⟩, packet⟩ pending ⟨senderEq, addressed⟩
  change sender = owner at senderEq
  subst sender
  have packetEq := safe.1 ⟨(owner, nonce), packet⟩ pending rfl event payload outputEq addressed
  change packet = .commitment event (owner, eventSlot event) at packetEq
  subst packet
  exact Option.isSome_iff_exists.mp
    (runtime.handle_canonical_commitment_isSome execution.native.application owner event payload
      outputEq codeEq viewNode ready timely resources nonce)

/-- Every matching pending resolution packet from a prescribed owner is the
current cached-action submission and is locally acceptable while timely. -/
theorem matching_resolution_packets_accepted
    (runtime : EventGraphRuntime graph) (owner : Player)
    (execution : runtime.application.PolicyExecution)
    (origins : ResolutionOrigins runtime execution owner)
    (invariant : execution.native.application.BindingInvariant)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event) :
    ∀ message ∈ execution.native.pool.pending, Payload.Matches event owner message →
      ∃ next, runtime.handle execution.native.application message = some next := by
  rintro message pending ⟨sender, addressed⟩
  obtain ⟨action, cached, submission⟩ :=
    origins.pending_resolutionSubmission runtime execution owner event payload owner binding checks
      outputEq codeEq viewNode ready message pending sender addressed
  rcases message with ⟨⟨actualOwner, nonce⟩, packet⟩
  change actualOwner = owner at sender
  subst actualOwner
  obtain ⟨result, actual, resolved, actualSubmission, accepted⟩ :=
    runtime.handle_resolutionSubmission_eq execution.native event owner payload binding checks
      outputEq codeEq viewNode ready timely action cached invariant nonce
  have same : actual = packet :=
    MessageInterface.PlayerCommand.submit.inj (actualSubmission.symm.trans submission)
  subst actual
  exact ⟨_, accepted⟩

private theorem withinDeadline_serviceStep_zero
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution) (event : graph.EventId)
    (invariant : before.native.application.Invariant inputs)
    (timely : before.native.application.WithinDeadline runtime event)
    (unfinished : event ∉ after.native.application.config.cut.completed)
    (zero : instruction.ticks = 0)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.application.WithinDeadline runtime event := by
  have progress := runtime.serviceStep_facts inputs players wire instruction before after
    invariant member
  have clock : after.native.application.clock = before.native.application.clock := by
    rw [progress.clock, zero]
    omega
  unfold State.WithinDeadline at timely ⊢
  cases activated : before.native.application.activatedAt event with
  | none => simp [activated] at timely
  | some entered =>
      have afterActivated := progress.activated event entered activated unfinished
      rw [afterActivated, clock]
      simpa [activated] using timely

private theorem withinDeadline_runServicePlan_zero
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution) (event : graph.EventId)
    (invariant : before.native.application.Invariant inputs)
    (timely : before.native.application.WithinDeadline runtime event)
    (unfinished : event ∉ after.native.application.config.cut.completed)
    (zero : serviceTicks plan = 0)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    after.native.application.WithinDeadline runtime event := by
  have progress := runtime.runServicePlan_facts inputs players wire plan before after invariant
    member
  have clock : after.native.application.clock = before.native.application.clock := by
    rw [progress.clock, zero]
    omega
  unfold State.WithinDeadline at timely ⊢
  cases activated : before.native.application.activatedAt event with
  | none => simp [activated] at timely
  | some entered =>
      have afterActivated := progress.activated event entered activated unfinished
      rw [afterActivated, clock]
      simpa [activated] using timely

/-- Live state carried by a canonical binding packet through clock-free
reactions. -/
structure BindingProtectionState (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (execution : runtime.application.PolicyExecution) (owner : Player)
    (event : graph.EventId) : Prop where
  invariant : execution.native.application.Invariant inputs
  ready : execution.native.application.config.cut.Ready event
  timely : execution.native.application.WithinDeadline runtime event
  authorship : runtime.application.Authorship execution
  canonical : execution.native.pool.Satisfies
    (CanonicalCommitments (graph := graph) owner)
  resources : execution.native.application.CanonicalResources owner
  submissions : execution.native.pool.Satisfies
    (PrescribedBindingSubmissions (graph := graph) owner)
  pending : ∃ message ∈ execution.native.pool.pending, Payload.Matches event owner message

/-- Live state carried by a cached-action resolution packet through clock-free
reactions. -/
structure ResolutionProtectionState (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) : Prop where
  invariant : execution.native.application.Invariant inputs
  coherent : PolicyCoherentAll runtime execution owner
  ready : execution.native.application.config.cut.Ready event
  timely : execution.native.application.WithinDeadline runtime event
  authorship : runtime.application.Authorship execution
  origins : ResolutionOrigins runtime execution owner
  bindingInvariant : execution.native.application.BindingInvariant
  pending : ∃ message ∈ execution.native.pool.pending, Payload.Matches event owner message

/-- One zero-tick reaction either completes a protected binding event or
retains its entire live inclusion state. -/
theorem serviceStep_bindingProtection
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (holds : BindingProtectionState runtime inputs before owner event)
    (zero : instruction.ticks = 0)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    event ∈ after.native.application.config.cut.completed ∨
      BindingProtectionState runtime inputs after owner event := by
  obtain ⟨message, pending, packetMatches⟩ := holds.pending
  obtain ⟨acceptedState, accepted⟩ :=
    runtime.matching_binding_packets_accepted owner before holds.submissions
      holds.resources event payload outputEq codeEq viewNode holds.ready holds.timely
      message pending packetMatches
  have packetProgress := runtime.serviceStep_pending_or_completed players wire instruction before
    after message event acceptedState pending packetMatches.2 accepted member
  rcases packetProgress with completed | retained
  · exact Or.inl completed
  · have progress := runtime.serviceStep_facts inputs players wire instruction before after
      holds.invariant member
    have readyAfter := progress.ready_or_completed event holds.ready
    rcases readyAfter with completed | readyAfter
    · exact Or.inl completed
    right
    refine ⟨progress.invariant, readyAfter, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact withinDeadline_serviceStep_zero runtime inputs players wire instruction before after
        event holds.invariant holds.timely readyAfter.1 zero member
    · exact runtime.serviceStep_authorship players wire instruction before after
        holds.authorship member
    · apply runtime.runServicePlan_canonicalCommitments owner policy players prescribed wire
        [instruction] before after holds.canonical
      simpa [runServicePlan] using member
    · exact runtime.serviceStep_canonicalResources owner players wire instruction before after
        holds.canonical holds.resources member
    · exact runtime.serviceStep_prescribedBindingSubmissions owner policy players prescribed wire
        instruction before after holds.submissions member
    · exact ⟨message, retained, packetMatches⟩

/-- One zero-tick reaction either completes a protected resolution event or
retains its cached-action inclusion state. -/
theorem serviceStep_resolutionProtection
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (holds : ResolutionProtectionState runtime inputs before owner event)
    (zero : instruction.ticks = 0)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    event ∈ after.native.application.config.cut.completed ∨
      ResolutionProtectionState runtime inputs after owner event := by
  obtain ⟨message, pending, packetMatches⟩ := holds.pending
  obtain ⟨acceptedState, accepted⟩ :=
    runtime.matching_resolution_packets_accepted owner before holds.origins
      holds.bindingInvariant event payload binding checks outputEq codeEq viewNode
      holds.ready holds.timely message pending packetMatches
  have packetProgress := runtime.serviceStep_pending_or_completed players wire instruction before
    after message event acceptedState pending packetMatches.2 accepted member
  rcases packetProgress with completed | retained
  · exact Or.inl completed
  · have progress := runtime.serviceStep_facts inputs players wire instruction before after
      holds.invariant member
    rcases progress.ready_or_completed event holds.ready with completed | readyAfter
    · exact Or.inl completed
    right
    refine ⟨progress.invariant, ?_, readyAfter, ?_, ?_, ?_, ?_, ?_⟩
    · exact runtime.serviceStep_policyCoherentAll owner policy players wire instruction before after
        prescribed holds.coherent member
    · exact withinDeadline_serviceStep_zero runtime inputs players wire instruction before after
        event holds.invariant holds.timely readyAfter.1 zero member
    · exact runtime.serviceStep_authorship players wire instruction before after
        holds.authorship member
    · exact runtime.serviceStep_resolutionOrigins inputs ordered owner policy players prescribed
        wire instruction before after holds.invariant holds.coherent holds.origins member
    · exact serviceStep_bindingInvariant runtime players wire instruction before after
        holds.bindingInvariant member
    · exact ⟨message, retained, packetMatches⟩

theorem runServicePlan_bindingProtection
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (holds : BindingProtectionState runtime inputs before owner event)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    event ∈ after.native.application.config.cut.completed ∨
      BindingProtectionState runtime inputs after owner event := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      exact Or.inr holds
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, first, tail⟩ := member
      have zero := clockFree instruction List.mem_cons_self
      have restFree : ∀ current ∈ rest, current.ticks = 0 := fun current currentMem =>
        clockFree current (List.mem_cons_of_mem instruction currentMem)
      rcases runtime.serviceStep_bindingProtection inputs owner policy players prescribed wire
          instruction before middle event payload outputEq codeEq viewNode holds zero first with
        completed | middleHolds
      · left
        have middleInvariant :=
          (runtime.serviceStep_facts inputs players wire instruction before middle holds.invariant
            first).invariant
        exact (runtime.runServicePlan_facts inputs players wire rest middle after middleInvariant
          tail).completed completed
      · exact ih middle middleHolds restFree tail

theorem runServicePlan_resolutionProtection
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (holds : ResolutionProtectionState runtime inputs before owner event)
    (clockFree : ∀ instruction ∈ plan, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    event ∈ after.native.application.config.cut.completed ∨
      ResolutionProtectionState runtime inputs after owner event := by
  induction plan generalizing before with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst after
      exact Or.inr holds
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, first, tail⟩ := member
      have zero := clockFree instruction List.mem_cons_self
      have restFree : ∀ current ∈ rest, current.ticks = 0 := fun current currentMem =>
        clockFree current (List.mem_cons_of_mem instruction currentMem)
      rcases runtime.serviceStep_resolutionProtection inputs ordered owner policy players prescribed
          wire instruction before middle event payload binding checks outputEq codeEq viewNode holds
          zero first with completed | middleHolds
      · left
        have middleInvariant :=
          (runtime.serviceStep_facts inputs players wire instruction before middle holds.invariant
            first).invariant
        exact (runtime.runServicePlan_facts inputs players wire rest middle after middleInvariant
          tail).completed completed
      · exact ih middle middleHolds restFree tail

theorem runServicePlan_bindingProtection_includeLatest
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (holds : BindingProtectionState runtime inputs before owner event)
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (reactions ++ [.includeLatest event owner]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  rw [runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨middle, reactionMem, inclusionMem⟩ := member
  have middleInvariant :=
    (runtime.runServicePlan_facts inputs players wire reactions before middle holds.invariant
      reactionMem).invariant
  rcases runtime.runServicePlan_bindingProtection inputs owner policy players prescribed wire
      reactions before middle event payload outputEq codeEq viewNode holds clockFree
      reactionMem with completed | middleHolds
  · have inclusionProgress := runtime.runServicePlan_facts inputs players wire
      [.includeLatest event owner] middle after middleInvariant inclusionMem
    exact inclusionProgress.completed completed
  · simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion,
      FinDist.mem_support_pure] at inclusionMem
    obtain ⟨included, includeMem, rfl⟩ := inclusionMem
    apply runtime.serviceStep_includeLatest_completes players wire event owner middle after
      middleHolds.authorship middleHolds.pending
    · exact runtime.matching_binding_packets_accepted owner middle middleHolds.submissions
        middleHolds.resources event payload outputEq codeEq viewNode middleHolds.ready
        middleHolds.timely
    · exact includeMem

theorem runServicePlan_resolutionProtection_includeLatest
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (holds : ResolutionProtectionState runtime inputs before owner event)
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (reactions ++ [.includeLatest event owner]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  rw [runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨middle, reactionMem, inclusionMem⟩ := member
  have middleInvariant :=
    (runtime.runServicePlan_facts inputs players wire reactions before middle holds.invariant
      reactionMem).invariant
  rcases runtime.runServicePlan_resolutionProtection inputs ordered owner policy players prescribed
      wire reactions before middle event payload binding checks outputEq codeEq viewNode holds
      clockFree reactionMem with completed | middleHolds
  · have inclusionProgress := runtime.runServicePlan_facts inputs players wire
      [.includeLatest event owner] middle after middleInvariant inclusionMem
    exact inclusionProgress.completed completed
  · simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion,
      FinDist.mem_support_pure] at inclusionMem
    obtain ⟨included, includeMem, rfl⟩ := inclusionMem
    apply runtime.serviceStep_includeLatest_completes players wire event owner middle after
      middleHolds.authorship middleHolds.pending
    · exact runtime.matching_resolution_packets_accepted owner middle middleHolds.origins
        middleHolds.bindingInvariant event payload binding checks outputEq codeEq viewNode
        middleHolds.ready middleHolds.timely
    · exact includeMem

/-- From any coherent, unfinished binding stage, the actual three owner calls,
arbitrary clock-free reactions, and reserved inclusion complete the event. -/
theorem runServicePlan_bind_partial_reactions_complete
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : before.native.application.serviceGrant = some event)
    (ready : before.native.application.config.cut.Ready event)
    (timely : before.native.application.WithinDeadline runtime event)
    (coherent : BindingPolicyCoherent runtime before owner event payload outputEq)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (invariant : before.native.application.Invariant inputs)
    (authorship : runtime.application.Authorship before)
    (canonical : before.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (resources : before.native.application.CanonicalResources owner)
    (submissions : before.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (List.replicate 3 (.player owner) ++ reactions ++ [.includeLatest event owner])
      before).support) :
    event ∈ after.native.application.config.cut.completed := by
  rw [List.append_assoc, runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨submitted, blockMem, tailMem⟩ := member
  have actualSubmission := runtime.runServicePlan_compiled_bind_partial_submitted owner policy
    players wire before submitted event payload outputEq codeEq viewNode prescribed grant ready
    coherent notSubmitted blockMem
  have blockProgress := runtime.runServicePlan_facts inputs players wire
    (List.replicate 3 (.player owner)) before submitted invariant blockMem
  rcases blockProgress.ready_or_completed event ready with completed | submittedReady
  · have tailProgress := runtime.runServicePlan_facts inputs players wire
      (reactions ++ [.includeLatest event owner]) submitted after blockProgress.invariant tailMem
    exact tailProgress.completed completed
  · have submittedTimely := withinDeadline_runServicePlan_zero runtime inputs players wire
      (List.replicate 3 (.player owner)) before submitted event invariant timely submittedReady.1
      (by simp [serviceTicks, ServiceInstruction.ticks]) blockMem
    have submittedAuthorship := runtime.runServicePlan_authorship players wire
      (List.replicate 3 (.player owner)) before submitted authorship blockMem
    have submittedCanonical := runtime.runServicePlan_canonicalCommitments owner policy players
      prescribed wire (List.replicate 3 (.player owner)) before submitted canonical blockMem
    have submittedResources := runtime.runServicePlan_canonicalResources owner policy players
      prescribed wire (List.replicate 3 (.player owner)) before submitted canonical resources
      blockMem
    have submittedShapes := runtime.runServicePlan_prescribedBindingSubmissions owner policy players
      prescribed wire (List.replicate 3 (.player owner)) before submitted submissions blockMem
    have pending : ∃ message ∈ submitted.native.pool.pending,
        Payload.Matches event owner message := by
      refine ⟨⟨(owner, before.native.pool.nextSerial owner),
        .commitment event (owner, eventSlot event)⟩, actualSubmission.2, ?_⟩
      exact ⟨rfl, rfl⟩
    let holds : BindingProtectionState runtime inputs submitted owner event :=
      ⟨blockProgress.invariant, submittedReady, submittedTimely, submittedAuthorship,
        submittedCanonical, submittedResources, submittedShapes, pending⟩
    exact runtime.runServicePlan_bindingProtection_includeLatest inputs owner policy players
      prescribed wire reactions submitted after event payload outputEq codeEq viewNode holds
      clockFree tailMem

/-- From any coherent, unfinished resolution stage, the actual three owner
calls, arbitrary clock-free reactions, and reserved inclusion complete the event. -/
theorem runServicePlan_resolve_partial_reactions_complete
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (grant : before.native.application.serviceGrant = some event)
    (ready : before.native.application.config.cut.Ready event)
    (timely : before.native.application.WithinDeadline runtime event)
    (coherent : PolicyCoherent runtime before owner event)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (originHolds : ResolutionOriginInvariant runtime inputs before owner)
    (authorship : runtime.application.Authorship before)
    (bindingInvariant : before.native.application.BindingInvariant)
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (List.replicate 3 (.player owner) ++ reactions ++ [.includeLatest event owner])
      before).support) :
    event ∈ after.native.application.config.cut.completed := by
  rw [List.append_assoc, runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨submitted, blockMem, tailMem⟩ := member
  have actualSubmission := runtime.runServicePlan_compiled_resolve_partial_submitted owner policy
    players wire before submitted event owner payload binding checks outputEq codeEq viewNode
    prescribed grant ready coherent notSubmitted blockMem
  have blockProgress := runtime.runServicePlan_facts inputs players wire
    (List.replicate 3 (.player owner)) before submitted originHolds.1 blockMem
  rcases blockProgress.ready_or_completed event ready with completed | submittedReady
  · have tailProgress := runtime.runServicePlan_facts inputs players wire
      (reactions ++ [.includeLatest event owner]) submitted after blockProgress.invariant tailMem
    exact tailProgress.completed completed
  · have submittedTimely := withinDeadline_runServicePlan_zero runtime inputs players wire
      (List.replicate 3 (.player owner)) before submitted event originHolds.1 timely
      submittedReady.1 (by simp [serviceTicks, ServiceInstruction.ticks]) blockMem
    have submittedOrigin := runtime.runServicePlan_resolutionOriginInvariant inputs ordered owner
      policy players prescribed wire (List.replicate 3 (.player owner)) before submitted originHolds
      blockMem
    have submittedAuthorship := runtime.runServicePlan_authorship players wire
      (List.replicate 3 (.player owner)) before submitted authorship blockMem
    have submittedBindingInvariant := runServicePlan_bindingInvariant runtime players wire
      (List.replicate 3 (.player owner)) before submitted bindingInvariant blockMem
    obtain ⟨action, packet, cached, submission, packetPending⟩ := actualSubmission.2
    have addressed : packet.event? graph = some event := by
      obtain ⟨actual, actualSubmission, actualAddress⟩ :=
        runtime.resolutionSubmission_address owner event payload binding checks outputEq action
          (MessageApplication.State.observe runtime.application submitted.native owner)
      have same : actual = packet :=
        MessageInterface.PlayerCommand.submit.inj (actualSubmission.symm.trans submission)
      subst actual
      exact actualAddress
    have pending : ∃ message ∈ submitted.native.pool.pending,
        Payload.Matches event owner message := by
      exact ⟨⟨(owner, before.native.pool.nextSerial owner), packet⟩, packetPending,
        ⟨rfl, addressed⟩⟩
    let holds : ResolutionProtectionState runtime inputs submitted owner event :=
      ⟨submittedOrigin.1, submittedOrigin.2.1, submittedReady, submittedTimely,
        submittedAuthorship, submittedOrigin.2.2, submittedBindingInvariant, pending⟩
    exact runtime.runServicePlan_resolutionProtection_includeLatest inputs ordered owner policy
      players prescribed wire reactions submitted after event payload binding checks outputEq codeEq
      viewNode holds clockFree tailMem

theorem runServicePlan_bind_partial_reactions_sample_complete
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : before.native.application.serviceGrant = some event)
    (ready : before.native.application.config.cut.Ready event)
    (timely : before.native.application.WithinDeadline runtime event)
    (coherent : BindingPolicyCoherent runtime before owner event payload outputEq)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (invariant : before.native.application.Invariant inputs)
    (authorship : runtime.application.Authorship before)
    (canonical : before.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (resources : before.native.application.CanonicalResources owner)
    (submissions : before.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (List.replicate 3 (.player owner) ++ reactions ++
        [.includeLatest event owner, .sample event]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  have split : List.replicate 3 (.player owner) ++ reactions ++
      [.includeLatest event owner, .sample event] =
      (List.replicate 3 (.player owner) ++ reactions ++ [.includeLatest event owner]) ++
        [.sample event] := by simp
  rw [split, runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨included, prefixMem, sampleMem⟩ := member
  have completed := runtime.runServicePlan_bind_partial_reactions_complete inputs owner policy
    players prescribed wire reactions before included event payload outputEq codeEq viewNode grant
    ready timely coherent notSubmitted invariant authorship canonical resources submissions
    clockFree prefixMem
  have includedInvariant := (runtime.runServicePlan_facts inputs players wire
    (List.replicate 3 (.player owner) ++ reactions ++ [.includeLatest event owner]) before included
    invariant prefixMem).invariant
  exact (runtime.runServicePlan_facts inputs players wire [.sample event] included after
    includedInvariant sampleMem).completed completed

theorem runServicePlan_resolve_partial_reactions_sample_complete
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (owner : Player) (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (reactions : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (grant : before.native.application.serviceGrant = some event)
    (ready : before.native.application.config.cut.Ready event)
    (timely : before.native.application.WithinDeadline runtime event)
    (coherent : PolicyCoherent runtime before owner event)
    (notSubmitted : submittedAt (before.principalHistory owner) event = false)
    (originHolds : ResolutionOriginInvariant runtime inputs before owner)
    (authorship : runtime.application.Authorship before)
    (bindingInvariant : before.native.application.BindingInvariant)
    (clockFree : ∀ instruction ∈ reactions, instruction.ticks = 0)
    (member : after ∈ (runtime.runServicePlan players wire
      (List.replicate 3 (.player owner) ++ reactions ++
        [.includeLatest event owner, .sample event]) before).support) :
    event ∈ after.native.application.config.cut.completed := by
  have split : List.replicate 3 (.player owner) ++ reactions ++
      [.includeLatest event owner, .sample event] =
      (List.replicate 3 (.player owner) ++ reactions ++ [.includeLatest event owner]) ++
        [.sample event] := by simp
  rw [split, runtime.runServicePlan_append, FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨included, prefixMem, sampleMem⟩ := member
  have completed := runtime.runServicePlan_resolve_partial_reactions_complete inputs ordered owner
    policy players prescribed wire reactions before included event payload binding checks outputEq
    codeEq viewNode grant ready timely coherent notSubmitted originHolds authorship bindingInvariant
    clockFree prefixMem
  have includedInvariant := (runtime.runServicePlan_facts inputs players wire
    (List.replicate 3 (.player owner) ++ reactions ++ [.includeLatest event owner]) before included
    originHolds.1 prefixMem).invariant
  exact (runtime.runServicePlan_facts inputs players wire [.sample event] included after
    includedInvariant sampleMem).completed completed

end Vegas.EventGraphRuntime
