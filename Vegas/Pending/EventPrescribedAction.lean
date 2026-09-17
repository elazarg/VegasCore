/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingPolicyService
import Vegas.Pending.EventCanonicalResources
import Vegas.Pending.EventDeviationAction
import Vegas.Pending.EventDeviationPotential
import Vegas.Pending.EventResolutionOrigin
import Vegas.Pending.EventServiceLaw
import Interaction.MessageApplicationAuthorship

/-! # Effective actions of prescribed retained packets -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A submission emitted by the compiled policy at a binding event is the
canonical commitment for that event. -/
theorem compilePlayerPolicy_binding_submission
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (payloadTy : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payloadTy)
    (packet : Payload graph)
    (supported : (.submit packet : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy history view).support)
    (addressed : packet.event? graph = some event) :
    packet = .commitment event (owner, eventSlot event) := by
  cases viewNode : nodeView graph event with
  | bind actualOwner actualPayload actualOutput codeEq =>
      have sameOutput : EventField.binding owner payloadTy =
          .binding actualOwner actualPayload := outputEq.symm.trans actualOutput
      injection sameOutput with ownerEq payloadEq
      subst actualOwner
      subst actualPayload
      have proofEq : actualOutput = outputEq := Subsingleton.elim _ _
      cases proofEq
      cases grant : view.application.publicView.serviceGrant with
      | none =>
          unfold compilePlayerPolicy at supported
          rw [grant] at supported
          simp only [FinDist.mem_support_pure, reduceCtorEq] at supported
      | some granted =>
          have atEvent := runtime.compilePlayerPolicy_commandAt owner policy history view
            granted grant (.submit packet) supported
          rcases atEvent with wait | staged | ⟨actual, commandEq, actualAddress⟩
          · simp at wait
          · simp [stagesEvent] at staged
          · have packetEq : packet = actual :=
              MessageInterface.PlayerCommand.submit.inj commandEq
            subst actual
            have same : granted = event :=
              Option.some.inj (actualAddress.symm.trans addressed)
            subst granted
            unfold compilePlayerPolicy at supported
            rw [grant] at supported
            simp only at supported
            rw [viewNode] at supported
            repeat' first | split at supported
            all_goals subst_vars
            all_goals try simp only [FinDist.mem_support_pure] at supported
            all_goals try { cases supported }
            all_goals try {
              rw [FinDist.support_map, Set.mem_image] at supported
              obtain ⟨action, _, impossible⟩ := supported
              cases impossible }
            all_goals simp_all [Payload.event?]
  | resolve actualOwner actualPayload binding checks actualOutput codeEq =>
      have impossible : EventField.binding owner payloadTy = .publication actualPayload :=
        outputEq.symm.trans actualOutput
      cases impossible
  | sample actualPayload law actualOutput codeEq =>
      have impossible : EventField.binding owner payloadTy = .publicData actualPayload :=
        outputEq.symm.trans actualOutput
      cases impossible

/-- Retained packets authored by one prescribed owner and addressed to one of
that owner's binding events have the unique canonical commitment shape. -/
def PrescribedBindingSubmissions (owner : Player)
    (message : Message Player (Payload graph)) : Prop :=
  message.sender = owner → ∀ event payloadTy,
    graph.outputLayout event = .binding owner payloadTy →
    message.payload.event? graph = some event →
    message.payload = .commitment event (owner, eventSlot event)

/-- The pool invariant classifies an actual pending owner packet at a binding
address as the canonical commitment. -/
theorem pending_prescribedBindingSubmission
    (runtime : EventGraphRuntime graph) (owner : Player)
    (execution : runtime.application.PolicyExecution)
    (safe : execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (sender : message.sender = owner)
    (event : graph.EventId) (payloadTy : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payloadTy)
    (addressed : message.payload.event? graph = some event) :
    message.payload = .commitment event (owner, eventSlot event) :=
  safe.1 message pending sender event payloadTy outputEq addressed

/-- Membership among the submitted payloads witnesses the event-addressed
submission bit used by policy coherence. -/
theorem submittedAt_eq_true_of_mem_submittedPayloads
    (runtime : EventGraphRuntime graph) (history : List (Entry runtime))
    (packet : Payload graph) (event : graph.EventId)
    (member : packet ∈ runtime.application.submittedPayloads history)
    (addressed : packet.event? graph = some event) :
    submittedAt history event = true := by
  induction history with
  | nil => simp [MessageApplication.submittedPayloads] at member
  | cons entry rest ih =>
      cases command : entry.command with
      | privateCommand privateCommand =>
          have tail : packet ∈ runtime.application.submittedPayloads rest := by
            simpa [MessageApplication.submittedPayloads, command] using member
          simpa [submittedAt, command] using ih tail
      | submit payload =>
          have hereOrTail : packet = payload ∨
              packet ∈ runtime.application.submittedPayloads rest := by
            simpa [MessageApplication.submittedPayloads, command] using member
          rcases hereOrTail with here | tail
          · subst payload
            simp [submittedAt, command, addressed]
          · unfold submittedAt
            rw [List.any_cons, command]
            change (decide (payload.event? graph = some event) || submittedAt rest event) = true
            simp [ih tail]
      | replay id =>
          have tail : packet ∈ runtime.application.submittedPayloads rest := by
            simpa [MessageApplication.submittedPayloads, command] using member
          simpa [submittedAt, command] using ih tail
      | wait =>
          have tail : packet ∈ runtime.application.submittedPayloads rest := by
            simpa [MessageApplication.submittedPayloads, command] using member
          simpa [submittedAt, command] using ih tail

/-- Authorship turns a retained envelope into an authenticated occurrence in
the sender's actual submission history. -/
theorem submittedAt_eq_true_of_mem_pending
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship execution)
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (event : graph.EventId) (addressed : message.payload.event? graph = some event) :
    submittedAt (execution.principalHistory message.sender) event = true := by
  have indexed := authorship.2.1 message pending
  have submitted : message.payload ∈ runtime.application.submittedPayloads
      (execution.principalHistory message.sender) := by
    change (runtime.application.submittedPayloads
      (execution.principalHistory message.id.1))[message.id.2]? = some message.payload at indexed
    rw [List.getElem?_eq_some_iff] at indexed
    rw [List.mem_iff_getElem]
    exact ⟨message.id.2, indexed.1, indexed.2⟩
  exact runtime.submittedAt_eq_true_of_mem_submittedPayloads _ _ event submitted addressed

/-- A retained canonical commitment from a coherent prescribed owner fixes
the canonical candidate's typed meaning to the owner's cached action. -/
theorem bindingResult_eq_cached_of_pending
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player)
    (authorship : runtime.application.Authorship execution)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (event : graph.EventId) (payloadTy : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payloadTy)
    (actor : graph.actor? event = some owner)
    (unfinished : event ∉ execution.native.application.config.cut.completed)
    (action : graph.Action event)
    (cached : execution.native.application.remembered event = some action)
    (nonce : Nat)
    (pending : (⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ :
      Message Player (Payload graph)) ∈ execution.native.pool.pending) :
    execution.native.application.bindingResult (owner, eventSlot event) payloadTy =
      cast (congrArg EventField.Action outputEq) action := by
  let message : Message Player (Payload graph) :=
    ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩
  have submitted : submittedAt (execution.principalHistory owner) event = true := by
    have authenticated := runtime.submittedAt_eq_true_of_mem_pending execution authorship
      message pending event rfl
    exact authenticated
  have current := coherent event payloadTy outputEq actor unfinished
  exact current.2.2 (current.1.submitted_stage submitted) action cached

/-- Accepting a retained canonical commitment from the unchanged prescribed
owner performs exactly the graph step selected by that owner's cached action.
The effective-action readout retains the dependent action itself, including
binding failure. -/
theorem handle_canonical_commitment_cached_action
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (authorship : runtime.application.Authorship execution)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (resources : execution.native.application.CanonicalResources owner)
    (event : graph.EventId) (payloadTy : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payloadTy)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payloadTy)
    (view : nodeView graph event = .bind owner payloadTy outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (cached : execution.native.application.remembered event = some action)
    (nonce : Nat)
    (pending : (⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ :
      Message Player (Payload graph)) ∈ execution.native.pool.pending)
    (next : State graph)
    (accepted : runtime.handle execution.native.application
      ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ = some next) :
    next.config ∈
        (execution.native.application.config.step event ready action).support ∧
      effectiveCompletion? execution.native.application next = some ⟨event, action⟩ ∧
      next.remembered = execution.native.application.remembered := by
  let state := execution.native.application
  have result : state.bindingResult (owner, eventSlot event) payloadTy =
      cast (congrArg EventField.Action outputEq) action := by
    apply runtime.bindingResult_eq_cached_of_pending execution owner authorship coherent
      event payloadTy outputEq actor ready.1 action cached nonce pending
  obtain ⟨vacant, unused⟩ := resources event ready.1
  obtain ⟨exactHandle, effective⟩ :=
    runtime.handle_commitment_effectiveCompletion state (owner, nonce) event
      (owner, eventSlot event) owner payloadTy outputEq codeEq view ready timely rfl rfl
      vacant unused
  let expected : State graph :=
      { (state.complete event ready
          (cast (congrArg EventField.Action outputEq.symm)
            (state.bindingResult (owner, eventSlot event) payloadTy))
          (cast (congrArg EventField.Value outputEq.symm)
            (state.bindingResult (owner, eventSlot event) payloadTy))) with
        accepted := Function.update state.accepted (.inr event)
          (some (owner, eventSlot event))
        candidates := state.candidates.accept (owner, eventSlot event) }
  have exactLaw : runtime.handle state
      ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ = some expected := by
    simpa [expected] using exactHandle
  have effectiveLaw : effectiveCompletion? state expected = some ⟨event,
      cast (congrArg EventField.Action outputEq.symm)
        (state.bindingResult (owner, eventSlot event) payloadTy)⟩ := by
    simpa [expected] using effective
  have selected : cast (congrArg EventField.Action outputEq.symm)
      (state.bindingResult (owner, eventSlot event) payloadTy) = action := by
    simp [result]
  have effectiveCached : effectiveCompletion? state expected = some ⟨event, action⟩ := by
    simpa only [selected] using effectiveLaw
  change runtime.handle state
      ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ = some next at accepted
  have nextEq : next = expected := Option.some.inj (accepted.symm.trans exactLaw)
  obtain ⟨actualEvent, actualAddress, actualReady, actualAction, actualMember⟩ :=
    runtime.handle_config_mem_step state next
      ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ accepted
  have eventEq : actualEvent = event :=
    Option.some.inj (actualAddress.symm.trans rfl)
  subst actualEvent
  have actualEffective := effectiveCompletion?_eq_of_mem_step state next event actualReady
    actualAction actualMember
  have nextEffective : effectiveCompletion? state next = some ⟨event, action⟩ := by
    rw [nextEq]
    exact effectiveCached
  have completionEq : (⟨event, actualAction⟩ : graph.Completion) = ⟨event, action⟩ :=
    Option.some.inj (actualEffective.symm.trans nextEffective)
  cases completionEq
  refine ⟨?_, nextEffective, ?_⟩
  · simpa only [state, Subsingleton.elim actualReady ready] using actualMember
  · exact runtime.handle_remembered state next _ accepted

/-- The prescribed cached-action identification immediately conserves the
focal-erased continuation when the accepted binding belongs to an unchanged
opponent. -/
theorem handle_canonical_commitment_deviationContinuation
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (focal owner : Player)
    (other : owner ≠ focal)
    (execution : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship execution)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (resources : execution.native.application.CanonicalResources owner)
    (event : graph.EventId) (payloadTy : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payloadTy)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payloadTy)
    (view : nodeView graph event = .bind owner payloadTy outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (cached : execution.native.application.remembered event = some action)
    (nonce : Nat)
    (pending : (⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ :
      Message Player (Payload graph)) ∈ execution.native.pool.pending)
    (next : State graph)
    (accepted : runtime.handle execution.native.application
      ⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ = some next) :
    next.deviationContinuation profile focal =
      execution.native.application.deviationContinuation profile focal := by
  obtain ⟨member, _, memory⟩ := runtime.handle_canonical_commitment_cached_action
    execution owner authorship coherent resources event payloadTy outputEq codeEq view ready
    timely actor action cached nonce pending next accepted
  apply State.deviationContinuation_eq_of_effective_step execution.native.application next
    ordered profile focal owner event ready actor action member memory
  · intro same
    exact False.elim (other same)
  · intro _
    exact cached

/-- A pending resolution packet with sound current origin executes exactly
the remembered action from which the prescribed owner formed it. This keeps
the original `true` action even when guard rejection sends a withholding
packet with a failure result. -/
theorem handle_prescribed_resolution_cached_action
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (origins : ResolutionOrigins runtime execution owner)
    (invariant : execution.native.application.BindingInvariant)
    (event : graph.EventId) (payloadTy : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payloadTy))
    (checks : List (GuardCheck graph.layout payloadTy))
    (outputEq : graph.outputLayout event = .publication payloadTy)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payloadTy binding checks)
    (view : nodeView graph event =
      .resolve owner payloadTy binding checks outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (sender : message.sender = owner)
    (addressed : message.payload.event? graph = some event)
    (next : State graph)
    (accepted : runtime.handle execution.native.application message = some next) :
    ∃ action, execution.native.application.remembered event = some action ∧
      next.config ∈
          (execution.native.application.config.step event ready action).support ∧
        effectiveCompletion? execution.native.application next = some ⟨event, action⟩ ∧
        next.remembered = execution.native.application.remembered := by
  obtain ⟨action, cached, submission⟩ := origins.pending_resolutionSubmission runtime
    execution owner event payloadTy owner binding checks outputEq codeEq view ready message pending
    sender addressed
  rcases message with ⟨⟨messageOwner, nonce⟩, packet⟩
  simp only [Message.sender] at sender
  subst messageOwner
  obtain ⟨result, selected, _, selectedSubmission, selectedHandle⟩ :=
    runtime.handle_resolutionSubmission_eq execution.native event owner payloadTy binding checks
      outputEq codeEq view ready timely action cached invariant nonce
  have packetEq : packet = selected :=
    MessageInterface.PlayerCommand.submit.inj (submission.symm.trans selectedSubmission)
  subst selected
  have nextEq : next = execution.native.application.complete event ready action
      (cast (congrArg EventField.Value outputEq.symm) result) :=
    Option.some.inj (accepted.symm.trans selectedHandle)
  have nextEffective : effectiveCompletion? execution.native.application next =
      some ⟨event, action⟩ := by
    rw [nextEq]
    simp [effectiveCompletion?, State.complete, EventGraph.Config.complete_history]
  obtain ⟨actualEvent, actualAddress, actualReady, actualAction, actualMember⟩ :=
    runtime.handle_config_mem_step execution.native.application next
      ⟨(owner, nonce), packet⟩ accepted
  have eventEq : actualEvent = event :=
    Option.some.inj (actualAddress.symm.trans addressed)
  subst actualEvent
  have actualEffective := effectiveCompletion?_eq_of_mem_step
    execution.native.application next event actualReady actualAction actualMember
  have completionEq : (⟨event, actualAction⟩ : graph.Completion) = ⟨event, action⟩ :=
    Option.some.inj (actualEffective.symm.trans nextEffective)
  cases completionEq
  refine ⟨action, cached, ?_, nextEffective, ?_⟩
  · simpa only [Subsingleton.elim actualReady ready] using actualMember
  · exact runtime.handle_remembered execution.native.application next _ accepted

/-- Every accepted pending packet authenticated as an unchanged prescribed
owner realizes that owner's remembered action at its strategic event. Binding
packets are forced to the canonical commitment; resolution packets retain
their current-origin equation, including rejected disclosures. -/
theorem handle_prescribed_owner_cached_action
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (authorship : runtime.application.Authorship execution)
    (coherent : PolicyCoherentAll runtime execution owner)
    (bindingCoherent : BindingPolicyCoherentAll runtime execution owner)
    (resources : execution.native.application.CanonicalResources owner)
    (bindingShape : execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (origins : ResolutionOrigins runtime execution owner)
    (invariant : execution.native.application.BindingInvariant)
    (event : graph.EventId)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner)
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (sender : message.sender = owner)
    (addressed : message.payload.event? graph = some event)
    (next : State graph)
    (accepted : runtime.handle execution.native.application message = some next) :
    ∃ action, execution.native.application.remembered event = some action ∧
      next.config ∈
          (execution.native.application.config.step event ready action).support ∧
        effectiveCompletion? execution.native.application next = some ⟨event, action⟩ ∧
        next.remembered = execution.native.application.remembered := by
  cases view : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have impossible : graph.actor? event = none := by
        unfold EventGraph.actor?
        exact (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [impossible] at actor
      contradiction
  | bind eventOwner payloadTy outputEq codeEq =>
      have eventOwnerEq : eventOwner = owner := by
        unfold EventGraph.actor? at actor
        have transformed :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        exact Option.some.inj (transformed.symm.trans actor)
      subst eventOwner
      have packetEq := runtime.pending_prescribedBindingSubmission owner execution bindingShape
        message pending sender event payloadTy outputEq addressed
      rcases message with ⟨⟨messageOwner, nonce⟩, packet⟩
      simp only [Message.sender] at sender
      subst messageOwner
      simp only at packetEq
      subst packet
      have submitted := runtime.submittedAt_eq_true_of_mem_pending execution authorship
        (⟨(owner, nonce), .commitment event (owner, eventSlot event)⟩ :
          Message Player (Payload graph)) pending event rfl
      have current := coherent event actor
      have stage : stagingCount (execution.principalHistory owner) event = 2 :=
        current.submitted_stage submitted
      obtain ⟨action, cached⟩ := current.cached_of_stage (by omega)
      obtain ⟨member, effective, memory⟩ :=
        runtime.handle_canonical_commitment_cached_action execution owner authorship
          bindingCoherent resources event payloadTy outputEq codeEq view ready timely actor action
          cached nonce pending next accepted
      exact ⟨action, cached, member, effective, memory⟩
  | resolve eventOwner payloadTy binding checks outputEq codeEq =>
      have eventOwnerEq : eventOwner = owner := by
        unfold EventGraph.actor? at actor
        have transformed :=
          (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
        exact Option.some.inj (transformed.symm.trans actor)
      subst eventOwner
      exact runtime.handle_prescribed_resolution_cached_action execution owner origins invariant
        event payloadTy binding checks outputEq codeEq view ready timely message pending sender
        addressed next accepted

theorem serviceStep_prescribedBindingSubmissions
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    after.native.pool.Satisfies (PrescribedBindingSubmissions (graph := graph) owner) := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, commandMem, step⟩ := member
      apply runtime.application.playerStep_pool_satisfies _ who before after command safe _ step
      intro packet commandEq
      subst command
      intro sender event payloadTy outputEq addressed
      have same : who = owner := sender
      subst who
      rw [ownerPolicy] at commandMem
      exact runtime.compilePlayerPolicy_binding_submission owner policy
        (before.principalHistory owner)
        (MessageApplication.State.observe runtime.application before.native owner)
        event payloadTy outputEq packet commandMem addressed
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.application.environmentPolicyStep_pool_satisfies _ before after command safe
        step
  | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.application.environmentPolicyStep_pool_satisfies _ before after _ safe member

/-- Prescribed binding-packet shape lifts through a concrete service plan. -/
theorem runServicePlan_prescribedBindingSubmissions
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    after.native.pool.Satisfies (PrescribedBindingSubmissions (graph := graph) owner) := by
  exact runtime.runServicePlan_invariant players wire _
    (runtime.serviceStep_prescribedBindingSubmissions owner policy players ownerPolicy wire)
    plan before after safe member

/-- Prescribed binding-packet shape lifts through adaptive finite service. -/
theorem runService_prescribedBindingSubmissions
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (before after : runtime.application.PolicyExecution)
    (safe : before.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner))
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count before).support) :
    after.native.pool.Satisfies (PrescribedBindingSubmissions (graph := graph) owner) := by
  exact runtime.runService_invariant roster reactionRounds players wire order _
    (runtime.serviceStep_prescribedBindingSubmissions owner policy players ownerPolicy wire)
    count before after safe member

/-- Authenticated-message provenance is invariant under one actual service
instruction, independently of every player and wire policy. -/
theorem serviceStep_authorship
    (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship before)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    runtime.application.Authorship after := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.application.playerStep_authorship who before after command authorship step
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      exact runtime.application.environmentStep_authorship before after command authorship step
  | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.application.environmentStep_authorship before after _ authorship member

/-- Authorship lifts through a finite concrete service plan. -/
theorem runServicePlan_authorship
    (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship before)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    runtime.application.Authorship after := by
  exact runtime.runServicePlan_invariant players wire _
    (runtime.serviceStep_authorship players wire) plan before after authorship member

/-- Authorship lifts through adaptive finite service. -/
theorem runService_authorship
    (runtime : EventGraphRuntime graph) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (before after : runtime.application.PolicyExecution)
    (authorship : runtime.application.Authorship before)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count before).support) :
    runtime.application.Authorship after := by
  exact runtime.runService_invariant roster reactionRounds players wire order _
    (runtime.serviceStep_authorship players wire) count before after authorship member

/-- Initialized adaptive service has authenticated histories and retained
message provenance. -/
theorem runService_initial_authorship
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (after : runtime.application.PolicyExecution)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial inputs)))).support) :
    runtime.application.Authorship after := by
  exact runtime.runService_authorship roster reactionRounds players wire order count _ after
    (MessageApplication.PolicyExecution.initial_authorship runtime.application _) member

/-- Prescribed binding-submission shape and authorship lift together through
adaptive service from the native empty pool. -/
theorem runService_initial_prescribedBindingSubmissions
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerPolicy : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (after : runtime.application.PolicyExecution)
    (member : after ∈
      (runtime.runService roster reactionRounds players wire order count
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial inputs)))).support) :
    after.native.pool.Satisfies (PrescribedBindingSubmissions (graph := graph) owner) := by
  apply runtime.runService_invariant roster reactionRounds players wire order _
    (runtime.serviceStep_prescribedBindingSubmissions owner policy players ownerPolicy wire)
    count _ after MessagePool.Satisfies.empty member

end Vegas.EventGraphRuntime
