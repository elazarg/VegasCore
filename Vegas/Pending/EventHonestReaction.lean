/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInclusion
import Vegas.Pending.EventPolicyBlock

/-! # Quiet prescribed reactions around one submitted event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Once the owner has submitted, every prescribed player reaction at the
same grant waits: the owner is already submitted and every other player is
not the event actor. -/
theorem compileProfile_wait_of_owner_submitted
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner who : Player)
    (grant : execution.native.application.serviceGrant = some event)
    (actor : graph.actor? event = some owner)
    (ownerSubmitted : submittedAt (execution.principalHistory owner) event = true) :
    runtime.compileProfile profile who (execution.principalHistory who)
        (MessageApplication.State.observe runtime.application execution.native who) =
      FinDist.pure .wait := by
  unfold compileProfile compilePlayerPolicy
  have observedGrant : (MessageApplication.State.observe runtime.application
      execution.native who).application.publicView.serviceGrant = some event := by
    exact grant
  rw [observedGrant]
  by_cases same : who = owner
  · subst who
    simp [ownerSubmitted]
  · have notActor : graph.actor? event ≠ some who := by
      rw [actor]
      simpa only [ne_eq, Option.some.injEq] using Ne.symm same
    simp [notActor]

/-- The corresponding service instruction only appends a wait entry to the
invoked player's history and leaves the complete native state unchanged. -/
theorem serviceStep_compileProfile_wait_of_owner_submitted
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner who : Player)
    (grant : execution.native.application.serviceGrant = some event)
    (actor : graph.actor? event = some owner)
    (ownerSubmitted : submittedAt (execution.principalHistory owner) event = true) :
    runtime.serviceStep (runtime.compileProfile profile) wire (.player who) execution =
      FinDist.pure
        { execution with
          principalHistory := fun other =>
            if other = who then execution.principalHistory who ++
              [⟨MessageApplication.State.observe runtime.application execution.native who,
                .wait⟩]
            else execution.principalHistory other } := by
  simp only [serviceStep, MessageApplication.invoke]
  rw [runtime.compileProfile_wait_of_owner_submitted profile execution event owner who grant
    actor ownerSubmitted, FinDist.pure_bind]
  exact runtime.application.playerStep_wait who execution

def HonestReactionState (runtime : EventGraphRuntime graph)
    (event : graph.EventId) (owner : Player)
    (before accepted : State graph) (message : Message Player (Payload graph))
    (execution : runtime.application.PolicyExecution) : Prop :=
  submittedAt (execution.principalHistory owner) event = true ∧
    ((execution.native.application = before ∧ execution.native.pool.pending = [message]) ∨
      (execution.native.application = accepted ∧ execution.native.pool.pending = []))

theorem serviceStep_wire_honestReactionState
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy)
    (event : graph.EventId) (owner : Player)
    (before accepted : State graph) (message : Message Player (Payload graph))
    (handled : handle runtime before message = some accepted)
    (execution next : runtime.application.PolicyExecution)
    (state : runtime.HonestReactionState event owner before accepted message execution)
    (member : next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire .wire
      execution).support) :
    runtime.HonestReactionState event owner before accepted message next := by
  rcases state with ⟨submitted, pending | included⟩
  · simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
      FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
    obtain ⟨command, _, step⟩ := member
    have ownerHistory : next.principalHistory owner = execution.principalHistory owner := by
      exact congrFun (runtime.application.environmentStep_principalHistory execution
        (command.toEnvironmentCommand runtime.application) next step
        ) owner
    refine ⟨by rw [ownerHistory]; exact submitted, ?_⟩
    have nativeMem : next.native ∈
        ((runtime.application.environmentPolicyStep execution
          (command.toEnvironmentCommand runtime.application)).map
            MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨next, step, rfl⟩
    rw [runtime.application.environmentStep_native] at nativeMem
    cases command with
    | deliver observer id | wait =>
        left
        simp only [WireCommand.toEnvironmentCommand,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at nativeMem
        rw [nativeMem]
        exact ⟨pending.1, by simpa [MessagePool.deliver_preserves_pending] using pending.2⟩
    | «include» id =>
        simp only [WireCommand.toEnvironmentCommand,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at nativeMem
        cases lookup : execution.native.pool.lookup id with
        | none =>
            rw [runtime.application.includePending_missing execution.native id lookup] at nativeMem
            left
            rw [nativeMem]
            exact pending
        | some found =>
            have foundEq : found = message := by
              have pair : message.id = id ∧ message = found := by
                simpa [MessagePool.lookup, pending.2] using lookup
              exact pair.2.symm
            subst found
            have handledExec : handle runtime execution.native.application message =
                some accepted := by rw [pending.1]; exact handled
            rw [runtime.application.includePending_accept execution.native id message accepted
                lookup handledExec] at nativeMem
            right
            constructor
            · simpa using congrArg (fun native : runtime.application.State => native.application)
                nativeMem
            · have poolEq := congrArg
                (fun native : runtime.application.State => native.pool.pending) nativeMem
              have removed := MessagePool.include_pending_of_lookup execution.native.pool id
                message lookup
              rw [removed] at poolEq
              unfold MessagePool.lookup at lookup
              rw [pending.2] at lookup
              simp at lookup
              simpa [pending.2, MessagePool.removeFirst, lookup] using poolEq
  · simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
      FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
    obtain ⟨command, _, step⟩ := member
    have ownerHistory : next.principalHistory owner = execution.principalHistory owner := by
      exact congrFun (runtime.application.environmentStep_principalHistory execution
        (command.toEnvironmentCommand runtime.application) next step
        ) owner
    refine ⟨by rw [ownerHistory]; exact submitted, Or.inr ?_⟩
    have nativeMem : next.native ∈
        ((runtime.application.environmentPolicyStep execution
          (command.toEnvironmentCommand runtime.application)).map
            MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨next, step, rfl⟩
    rw [runtime.application.environmentStep_native] at nativeMem
    cases command with
    | deliver observer id | wait =>
        simp only [WireCommand.toEnvironmentCommand,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at nativeMem
        rw [nativeMem]
        exact ⟨included.1, by simpa [MessagePool.deliver_preserves_pending] using included.2⟩
    | «include» id =>
        simp only [WireCommand.toEnvironmentCommand,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at nativeMem
        have missing : execution.native.pool.lookup id = none := by
          simp [MessagePool.lookup, included.2]
        rw [runtime.application.includePending_missing execution.native id missing] at nativeMem
        rw [nativeMem]
        exact included

theorem serviceStep_player_honestReactionState
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy) (event : graph.EventId) (owner who : Player)
    (before accepted : State graph) (message : Message Player (Payload graph))
    (actor : graph.actor? event = some owner)
    (execution next : runtime.application.PolicyExecution)
    (state : runtime.HonestReactionState event owner before accepted message execution)
    (grantBefore : before.serviceGrant = some event)
    (grantAccepted : accepted.serviceGrant = some event)
    (member : next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire (.player who)
      execution).support) :
    runtime.HonestReactionState event owner before accepted message next := by
  rcases state with ⟨submitted, branch⟩
  have grant : execution.native.application.serviceGrant = some event := by
    rcases branch with h | h <;> simp [h.1, grantBefore, grantAccepted]
  rw [runtime.serviceStep_compileProfile_wait_of_owner_submitted profile wire execution event
    owner who grant actor submitted, FinDist.mem_support_pure] at member
  subst next
  refine ⟨?_, branch⟩
  by_cases same : owner = who
  · subst who
    simp only [ite_eq_left]
    change submittedAt (execution.principalHistory owner ++ [_]) event = true
    simpa [submittedAt] using submitted
  · simp [same]
    simpa only [ite_eq_right (Ne.symm same)] using submitted

/-- The reaction interval contains only prescribed player calls and ordinary
wire calls.  In particular, its endpoint is not another reserved event slot. -/
def HonestReactionInstruction : ServiceInstruction graph → Prop
  | .player _ | .wire => True
  | _ => False

private theorem serviceStep_honestReaction_history
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (allowed : HonestReactionInstruction instruction)
    (member : next ∈ (runtime.serviceStep (runtime.compileProfile profile) wire instruction
      execution).support)
    (quiet : ∀ who, runtime.compileProfile profile who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure .wait) :
    ∀ who query,
      stagingCount (next.principalHistory who) query =
          stagingCount (execution.principalHistory who) query ∧
        submittedAt (next.principalHistory who) query =
          submittedAt (execution.principalHistory who) query := by
  cases instruction with
  | player selected =>
      simp only [serviceStep, MessageApplication.invoke] at member
      rw [quiet selected, FinDist.pure_bind, runtime.application.playerStep_wait,
        FinDist.mem_support_pure] at member
      subst next
      intro who query
      by_cases same : who = selected
      · subst who
        simp [stagingCount, submittedAt, stagesEvent]
      · simp [same]
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      intro who query
      rw [runtime.application.environmentStep_principalHistory execution
        (command.toEnvironmentCommand runtime.application) next step]
      exact ⟨rfl, rfl⟩
  | grant | includeLatest | sample | tick | expire =>
      simp [HonestReactionInstruction] at allowed

/-- Any finite reaction interval preserves the submitted-event normal form and
does not change any player's staging or submission counters. -/
theorem runServicePlan_honestReaction
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy)
    (event : graph.EventId) (owner : Player)
    (before accepted : State graph) (message : Message Player (Payload graph))
    (handled : handle runtime before message = some accepted)
    (actor : graph.actor? event = some owner)
    (grantBefore : before.serviceGrant = some event)
    (grantAccepted : accepted.serviceGrant = some event)
    (plan : List (ServiceInstruction graph))
    (allowed : ∀ instruction ∈ plan, HonestReactionInstruction instruction)
    (execution next : runtime.application.PolicyExecution)
    (state : runtime.HonestReactionState event owner before accepted message execution)
    (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire plan
      execution).support) :
    runtime.HonestReactionState event owner before accepted message next ∧
      ∀ who query,
        stagingCount (next.principalHistory who) query =
            stagingCount (execution.principalHistory who) query ∧
          submittedAt (next.principalHistory who) query =
            submittedAt (execution.principalHistory who) query := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at member
      subst next
      exact ⟨state, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at member
      obtain ⟨middle, head, tail⟩ := member
      have middleState : runtime.HonestReactionState event owner before accepted message middle :=
          by
        cases instruction with
        | wire =>
            exact runtime.serviceStep_wire_honestReactionState profile wire event owner before
              accepted message handled execution middle state head
        | player who =>
            exact runtime.serviceStep_player_honestReactionState profile wire event owner who before
              accepted message actor execution middle state grantBefore grantAccepted head
        | grant | includeLatest | sample | tick | expire =>
            simp [HonestReactionInstruction] at allowed
      have grant : execution.native.application.serviceGrant = some event := by
        rcases state.2 with branch | branch <;> simp [branch.1, grantBefore, grantAccepted]
      have quiet : ∀ who, runtime.compileProfile profile who (execution.principalHistory who)
          (MessageApplication.State.observe runtime.application execution.native who) =
            FinDist.pure .wait := fun who =>
        runtime.compileProfile_wait_of_owner_submitted profile execution event owner who grant actor
          state.1
      have headHistory := serviceStep_honestReaction_history runtime profile wire instruction
        execution middle (allowed instruction List.mem_cons_self) head quiet
      obtain ⟨finalState, tailHistory⟩ := ih
        (allowed := fun selected selectedMem =>
          allowed selected (List.mem_cons_of_mem _ selectedMem))
        (execution := middle) middleState tail
      refine ⟨finalState, fun who query => ⟨?_, ?_⟩⟩
      · exact (tailHistory who query).1.trans (headHistory who query).1
      · exact (tailHistory who query).2.trans (headHistory who query).2

/-- The reserved slot following an honest reaction interval consumes the sole
matching message (or harmlessly waits if a wire call already consumed it). -/
theorem runServicePlan_honestReaction_includeLatest
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (wire : runtime.application.WirePolicy)
    (event : graph.EventId) (owner : Player)
    (before accepted : State graph) (message : Message Player (Payload graph))
    (handled : handle runtime before message = some accepted)
    (actor : graph.actor? event = some owner)
    (authored : message.sender = owner)
    (addressed : message.payload.event? graph = some event)
    (grantBefore : before.serviceGrant = some event)
    (grantAccepted : accepted.serviceGrant = some event)
    (plan : List (ServiceInstruction graph))
    (allowed : ∀ instruction ∈ plan, HonestReactionInstruction instruction)
    (execution next : runtime.application.PolicyExecution)
    (state : runtime.HonestReactionState event owner before accepted message execution)
    (member : next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      (plan ++ [.includeLatest event owner]) execution).support) :
    next.native.application = accepted ∧ next.native.pool.pending = [] ∧
      ∀ who query,
        stagingCount (next.principalHistory who) query =
            stagingCount (execution.principalHistory who) query ∧
          submittedAt (next.principalHistory who) query =
            submittedAt (execution.principalHistory who) query := by
  rw [runtime.runServicePlan_append] at member
  simp only [FinDist.support_bind, Set.mem_iUnion] at member
  obtain ⟨middle, prefixMem, suffixMem⟩ := member
  obtain ⟨middleState, prefixHistory⟩ := runtime.runServicePlan_honestReaction profile wire
    event owner before accepted message handled actor grantBefore grantAccepted plan allowed
    execution middle state prefixMem
  simp only [runServicePlan, FinDist.bind_pure] at suffixMem
  rcases middleState with ⟨_, pending | included⟩
  · have selected : latestEventSubmission? middle.native.pool event owner = some message := by
      unfold latestEventSubmission?
      rw [pending.2]
      simpa only [latestEventSubmission?, List.nil_append] using
        latestEventSubmission?_append_matching
        { middle.native.pool with pending := [] } event owner message ⟨authored, addressed⟩
    change next ∈ (runtime.application.environmentPolicyStep middle
      (runtime.latestEventSubmissionCommand event owner
        (MessageApplication.State.environmentView runtime.application middle.native))).support
          at suffixMem
    have command : runtime.latestEventSubmissionCommand event owner
        (MessageApplication.State.environmentView runtime.application middle.native) =
          .include message.id := by
      unfold latestEventSubmissionCommand
      change (match latestEventSubmission? middle.native.pool event owner with
        | some found => MessageInterface.EnvironmentPolicyCommand.include found.id
        | none => .wait) = _
      rw [selected]
    rw [command] at suffixMem
    have nativeMem : next.native ∈
        ((runtime.application.environmentPolicyStep middle (.include message.id)).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨next, suffixMem, rfl⟩
    rw [runtime.application.environmentStep_native] at nativeMem
    simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at nativeMem
    have lookup : middle.native.pool.lookup message.id = some message := by
      simp [MessagePool.lookup, pending.2]
    have handledMiddle : handle runtime middle.native.application message = some accepted := by
      rw [pending.1]
      exact handled
    rw [runtime.application.includePending_accept middle.native message.id message accepted lookup
      handledMiddle] at nativeMem
    have nativeEq := nativeMem
    rw [nativeEq]
    refine ⟨rfl, ?_, ?_⟩
    · simpa [pending.2, MessagePool.removeFirst] using
        MessagePool.include_pending_of_lookup middle.native.pool message.id message lookup
    · intro who query
      rw [runtime.application.environmentStep_principalHistory middle (.include message.id) next
        suffixMem]
      exact prefixHistory who query
  · change next ∈ (runtime.application.environmentPolicyStep middle
      (runtime.latestEventSubmissionCommand event owner
        (MessageApplication.State.environmentView runtime.application middle.native))).support
          at suffixMem
    have absent : runtime.latestEventSubmissionCommand event owner
        (MessageApplication.State.environmentView runtime.application middle.native) = .wait := by
      unfold latestEventSubmissionCommand
      change (match latestEventSubmission? middle.native.pool event owner with
        | some found => MessageInterface.EnvironmentPolicyCommand.include found.id
        | none => .wait) = _
      unfold latestEventSubmission?
      rw [included.2]
      rfl
    rw [absent, runtime.application.environmentStep_wait, FinDist.mem_support_pure] at suffixMem
    subst next
    exact ⟨included.1, included.2, prefixHistory⟩

end Vegas.EventGraphRuntime
