/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyService
import Vegas.Pending.EventPrescribedSubmission
import Vegas.Pending.EventResolutionBlock
import Vegas.Pending.EventPublicBarrier
import Vegas.Pending.EventServiceLaw

/-! # Origin soundness for retained resolution packets -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A resolution packet authenticated as the prescribed owner is either for an
already completed event, or is exactly the submission generated from the
immutable cached action while that event remains ready. -/
def ResolutionPacketValid (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (message : Message Player (Payload graph)) : Prop :=
  ∀ (event : graph.EventId) (payload : L.Ty)
      (bindingOwner : Player)
      (binding : FieldRef graph.layout (.binding bindingOwner payload))
      (checks : List (DeferredCheck graph.layout payload))
      (outputEq : graph.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
        (graph.nodes event) = .resolve bindingOwner payload binding checks)
      (_viewNode : nodeView graph event =
        .resolve bindingOwner payload binding checks outputEq codeEq),
    message.sender = owner → message.payload.event? graph = some event →
      event ∈ execution.native.application.config.cut.completed ∨
        ∃ action, execution.native.application.config.cut.Ready event ∧
          execution.native.application.remembered event = some action ∧
          runtime.resolutionSubmission owner event payload binding checks outputEq action
              (MessageApplication.State.observe runtime.application execution.native owner) =
            .submit message.payload

/-- Every retained envelope satisfies resolution origin soundness.  Quantifying
over all four native retention locations makes replay preservation immediate. -/
def ResolutionOrigins (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player) : Prop :=
  ∀ message, runtime.application.Retained execution.native.pool message →
    ResolutionPacketValid runtime execution owner message

theorem resolutionSubmission_eq_of_config_accepted
    (runtime : EventGraphRuntime graph) (left right : runtime.application.State)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    {bindingOwner : Player}
    (binding : FieldRef graph.layout (.binding bindingOwner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event)
    (config : left.application.config = right.application.config)
    (accepted : left.application.accepted = right.application.accepted) :
    runtime.resolutionSubmission owner event payload binding checks outputEq action
        (MessageApplication.State.observe runtime.application left owner) =
      runtime.resolutionSubmission owner event payload binding checks outputEq action
        (MessageApplication.State.observe runtime.application right owner) := by
  have observation : (State.playerView left.application owner).observation =
      (State.playerView right.application owner).observation := by
    simp only [State.playerView]
    rw [config]
  have acceptedView : (State.playerView left.application owner).publicView.accepted =
      (State.playerView right.application owner).publicView.accepted := by
    simp only [State.playerView, State.publicView]
    exact accepted
  unfold resolutionSubmission resolutionPayload
  simp only [MessageApplication.State.observe, EventGraphRuntime.application]
  rw [observation, acceptedView]

/-- Dynamic resolution validity transports across any step which either
completes the ready event or preserves its public semantic inputs and cached
action. -/
theorem ResolutionPacketValid.copy
    (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution) (owner : Player)
    (message : Message Player (Payload graph))
    (valid : ResolutionPacketValid runtime before owner message)
    (completed : before.native.application.config.cut.completed ⊆
      after.native.application.config.cut.completed)
    (frame : ∀ event, (graph.outputLayout event).IsPublic →
      before.native.application.config.cut.Ready event →
      event ∉ after.native.application.config.cut.completed →
        after.native.application.config.cut.Ready event ∧
        before.native.application.config = after.native.application.config ∧
        before.native.application.accepted = after.native.application.accepted ∧
        ∀ action, before.native.application.remembered event = some action →
          after.native.application.remembered event = some action) :
    ResolutionPacketValid runtime after owner message := by
  intro event payload bindingOwner binding checks outputEq codeEq viewNode sender addressed
  rcases valid event payload bindingOwner binding checks outputEq codeEq viewNode sender
      addressed with done | ⟨action, ready, remembered, submission⟩
  · exact Or.inl (completed done)
  · by_cases done : event ∈ after.native.application.config.cut.completed
    · exact Or.inl done
    · have isPublic : (graph.outputLayout event).IsPublic := by
        rw [outputEq]
        trivial
      obtain ⟨readyAfter, config, accepted, rememberedAfter⟩ :=
        frame event isPublic ready done
      right
      refine ⟨action, readyAfter, rememberedAfter action remembered, ?_⟩
      rw [← submission]
      exact (runtime.resolutionSubmission_eq_of_config_accepted before.native after.native owner
        event payload binding checks outputEq action config accepted).symm

theorem resolutionOrigins_initial (runtime : EventGraphRuntime graph)
    (inputs : graph.Inputs) (owner : Player) :
    ResolutionOrigins runtime
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs))) owner := by
  intro message retained
  rcases retained with pending | ledger | ⟨who, inbox⟩ | ⟨who, sent⟩ <;>
    simp [MessageApplication.PolicyExecution.initial, MessageApplication.State.initial,
      MessagePool.empty] at *

/-- At a ready resolution grant, every supported compiled submission is the
one generated from the coherent cached action. -/
theorem compilePlayerPolicy_resolution_submission
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty) (bindingOwner : Player)
    (binding : FieldRef graph.layout (.binding bindingOwner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve bindingOwner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve bindingOwner payload binding checks outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (notSubmitted : submittedAt (execution.principalHistory owner) event = false)
    (coherent : PolicyCoherent runtime execution owner event)
    (packet : Payload graph)
    (member : (.submit packet : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)).support) :
    ∃ action, execution.native.application.remembered event = some action ∧
      runtime.resolutionSubmission owner event payload binding checks outputEq action
          (MessageApplication.State.observe runtime.application execution.native owner) =
        .submit packet := by
  have stageAtLeast := runtime.compilePlayerPolicy_submit_stage owner policy execution event
    grant packet member
  have stageExactly : stagingCount (execution.principalHistory owner) event = 2 := by
    have stageLe := coherent.stage_le
    omega
  obtain ⟨action, cached⟩ := coherent.cached_of_stage (by omega)
  have publicReady : execution.native.application.publicView.EventReady event :=
    (State.publicView_eventReady execution.native.application event).2 ready
  have policyEq := runtime.compilePlayerPolicy_resolve_stage_two owner policy
    (execution.principalHistory owner)
    (MessageApplication.State.observe runtime.application execution.native owner)
    event bindingOwner payload binding checks outputEq codeEq viewNode action (by
      change execution.native.application.serviceGrant = some event
      exact grant) notSubmitted rfl publicReady coherent.actor (by omega) (by
      change (State.playerView execution.native.application owner).remembered event = some action
      simpa [State.playerView, coherent.actor] using cached)
  rw [policyEq, FinDist.mem_support_pure] at member
  exact ⟨action, cached, member.symm⟩

/-- The address of every supported compiled submission is exactly its current
service grant. -/
theorem compilePlayerPolicy_submit_grant
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (packet : Payload graph) (event : graph.EventId)
    (member : (.submit packet : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy history view).support)
    (addressed : packet.event? graph = some event) :
    view.application.publicView.serviceGrant = some event := by
  cases grantEq : view.application.publicView.serviceGrant with
  | none =>
      unfold compilePlayerPolicy at member
      rw [grantEq] at member
      simp at member
  | some query =>
      have atQuery := runtime.compilePlayerPolicy_commandAt owner policy history view query
        grantEq (.submit packet) member
      rcases atQuery with wait | staged | ⟨actual, commandEq, actualAddress⟩
      · contradiction
      · simp [stagesEvent] at staged
      · have payloadEq := MessageInterface.PlayerCommand.submit.inj commandEq
        subst actual
        rw [addressed] at actualAddress
        have same := Option.some.inj actualAddress
        subst query
        rfl

/-- A supported compiled submission is emitted only while its grant is ready
and has no earlier submission entry. -/
theorem compilePlayerPolicy_submit_ready_notSubmitted
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (packet : Payload graph)
    (grant : view.application.publicView.serviceGrant = some event)
    (member : (.submit packet : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy history view).support) :
    view.application.publicView.EventReady event ∧ submittedAt history event = false := by
  unfold compilePlayerPolicy at member
  rw [grant] at member
  repeat' first | split at member
  all_goals subst_vars
  all_goals simp_all only [FinDist.mem_support_pure, FinDist.support_map,
    Set.mem_image, reduceCtorEq, MessageInterface.PlayerCommand.submit.injEq,
    Option.some.injEq, submit_ne_bindingStageCommand]
  all_goals try { rcases member with ⟨_, _, impossible⟩; contradiction }
  all_goals aesop

theorem ResolutionPacketValid.serviceStep
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution) (owner : Player)
    (message : Message Player (Payload graph))
    (invariant : before.native.application.Invariant inputs)
    (valid : ResolutionPacketValid runtime before owner message)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    ResolutionPacketValid runtime after owner message := by
  have progress := runtime.serviceStep_facts inputs players wire instruction before after
    invariant member
  obtain ⟨suffix, _, native⟩ :=
    runtime.serviceStep_native_support players wire instruction before after member
  apply valid.copy runtime before after owner message progress.completed
  intro event isPublic ready unfinished
  have frame := runtime.applicationRun_ready_public_frame ordered before.native after.native
    event isPublic ready unfinished suffix native
  refine ⟨?_, frame.1.symm, frame.2.1.symm, frame.2.2⟩
  simpa only [frame.1] using ready

private theorem satisfies_retained_elim
    {runtime : EventGraphRuntime graph} {safe : Message Player (Payload graph) → Prop}
    {pool : MessagePool Player (Payload graph)}
    (all : pool.Satisfies safe) {message : Message Player (Payload graph)}
    (retained : runtime.application.Retained pool message) : safe message := by
  rcases retained with pending | ledger | ⟨who, inbox⟩ | ⟨who, sent⟩
  · exact all.1 message pending
  · exact all.2.1 message ledger
  · exact all.2.2.1 who message inbox
  · exact all.2.2.2 who message sent

private theorem satisfies_retained_all
    (runtime : EventGraphRuntime graph) (pool : MessagePool Player (Payload graph)) :
    pool.Satisfies (runtime.application.Retained pool) := by
  exact ⟨fun _ member => Or.inl member,
    fun _ member => Or.inr (Or.inl member),
    fun who _ member => Or.inr (Or.inr (Or.inl ⟨who, member⟩)),
    fun who _ member => Or.inr (Or.inr (Or.inr ⟨who, member⟩))⟩

private theorem ResolutionOrigins.of_retained
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution) (owner : Player)
    (invariant : before.native.application.Invariant inputs)
    (origins : ResolutionOrigins runtime before owner)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support)
    (old : ∀ message, runtime.application.Retained after.native.pool message →
      runtime.application.Retained before.native.pool message) :
    ResolutionOrigins runtime after owner := by
  intro message retained
  exact (origins message (old message retained)).serviceStep runtime inputs ordered players wire
    instruction before after owner message invariant member

/-- One concrete service instruction preserves resolution-packet origin
soundness. Only a prescribed owner's fresh submission is new; every replayed or
transported envelope is reduced to the prior retained invariant. -/
theorem serviceStep_resolutionOrigins
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (invariant : before.native.application.Invariant inputs)
    (coherent : PolicyCoherentAll runtime before owner)
    (origins : ResolutionOrigins runtime before owner)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    ResolutionOrigins runtime after owner := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, commandMem, step⟩ := member
      cases command with
      | privateCommand privateCommand | replay privateCommand | wait =>
          apply ResolutionOrigins.of_retained runtime inputs ordered players wire (.player who)
            before after owner invariant origins
            (by
              simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
                Set.mem_iUnion]
              exact ⟨_, commandMem, step⟩)
          intro message retained
          have safe := runtime.application.playerStep_pool_satisfies
            (runtime.application.Retained before.native.pool) who before after _
            (satisfies_retained_all runtime before.native.pool) (by
              intros
              contradiction) step
          exact satisfies_retained_elim safe retained
      | submit packet =>
          let newly : Message Player (Payload graph) :=
            ⟨(who, before.native.pool.nextSerial who), packet⟩
          let safe : Message Player (Payload graph) → Prop := fun message =>
            runtime.application.Retained before.native.pool message ∨ message = newly
          have prior : before.native.pool.Satisfies safe :=
            (satisfies_retained_all runtime before.native.pool).mono
              (fun _ retained => Or.inl retained)
          have afterSafe := runtime.application.playerStep_pool_satisfies safe who before after
            (.submit packet) prior (by
              intro payload commandEq
              injection commandEq with same
              subst payload
              exact Or.inr rfl) step
          intro message retained
          rcases satisfies_retained_elim afterSafe retained with old | rfl
          · exact (origins message old).serviceStep runtime inputs ordered players wire
              (.player who) before after owner message invariant (by
                simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
                  Set.mem_iUnion]
                exact ⟨_, commandMem, step⟩)
          · intro event payload bindingOwner binding checks outputEq codeEq viewNode sender
              addressed
            have sameOwner : who = owner := sender
            subst who
            rw [prescribed] at commandMem
            have observedGrant := runtime.compilePlayerPolicy_submit_grant owner policy
              (before.principalHistory owner)
              (MessageApplication.State.observe runtime.application before.native owner)
              packet event commandMem addressed
            have grant : before.native.application.serviceGrant = some event := by
              change (MessageApplication.State.observe runtime.application before.native
                owner).application.publicView.serviceGrant = some event
              exact observedGrant
            have context := runtime.compilePlayerPolicy_submit_ready_notSubmitted owner policy
              (before.principalHistory owner)
              (MessageApplication.State.observe runtime.application before.native owner)
              event packet observedGrant commandMem
            have ready :=
              (State.publicView_eventReady before.native.application event).mp context.1
            have actor := runtime.compilePlayerPolicy_nonwait_actor owner policy
              (before.principalHistory owner)
              (MessageApplication.State.observe runtime.application before.native owner)
              event observedGrant (.submit packet) (by simp) commandMem
            have origin := runtime.compilePlayerPolicy_resolution_submission owner policy before
              event payload bindingOwner binding checks outputEq codeEq viewNode grant ready
              context.2 (coherent event actor) packet commandMem
            obtain ⟨action, cached, submission⟩ := origin
            have stepEq : after = runtime.application.afterSubmit before owner packet := by
              simpa only [runtime.application.playerStep_submit_eq,
                FinDist.mem_support_pure] using step
            subst after
            right
            refine ⟨action, ready, cached, ?_⟩
            simpa [resolutionSubmission, resolutionPayload,
              MessageApplication.State.observe, MessageApplication.afterSubmit] using submission
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at member
      obtain ⟨command, _, step⟩ := member
      apply ResolutionOrigins.of_retained runtime inputs ordered players wire .wire before after
        owner invariant origins (by
          simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
            Set.mem_iUnion]
          exact ⟨_, by assumption, step⟩)
      intro message retained
      have safe := runtime.application.environmentPolicyStep_pool_satisfies
        (runtime.application.Retained before.native.pool) before after command
        (satisfies_retained_all runtime before.native.pool) step
      exact satisfies_retained_elim safe retained
  | grant event | includeLatest event who | sample event | tick | expire event =>
      apply ResolutionOrigins.of_retained runtime inputs ordered players wire _ before after owner
        invariant origins member
      intro message retained
      have safe := runtime.application.environmentPolicyStep_pool_satisfies
        (runtime.application.Retained before.native.pool) before after _
        (satisfies_retained_all runtime before.native.pool) member
      exact satisfies_retained_elim safe retained

/-- The three coupled facts needed by resolution provenance: native graph
well-formedness, owner cache/history coherence, and retained-packet origins. -/
def ResolutionOriginInvariant (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (execution : runtime.application.PolicyExecution) (owner : Player) : Prop :=
  execution.native.application.Invariant inputs ∧
    PolicyCoherentAll runtime execution owner ∧ ResolutionOrigins runtime execution owner

theorem serviceStep_resolutionOriginInvariant
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (before after : runtime.application.PolicyExecution)
    (holds : ResolutionOriginInvariant runtime inputs before owner)
    (member : after ∈ (runtime.serviceStep players wire instruction before).support) :
    ResolutionOriginInvariant runtime inputs after owner := by
  refine ⟨(runtime.serviceStep_facts inputs players wire instruction before after holds.1
    member).invariant, ?_, ?_⟩
  · exact runtime.serviceStep_policyCoherentAll owner policy players wire instruction before after
      prescribed holds.2.1 member
  · exact runtime.serviceStep_resolutionOrigins inputs ordered owner policy players prescribed wire
      instruction before after holds.1 holds.2.1 holds.2.2 member

theorem runServicePlan_resolutionOriginInvariant
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (plan : List (ServiceInstruction graph))
    (before after : runtime.application.PolicyExecution)
    (holds : ResolutionOriginInvariant runtime inputs before owner)
    (member : after ∈ (runtime.runServicePlan players wire plan before).support) :
    ResolutionOriginInvariant runtime inputs after owner := by
  exact runtime.runServicePlan_invariant players wire _
    (runtime.serviceStep_resolutionOriginInvariant inputs ordered owner policy players prescribed
      wire) plan before after holds member

/-- Actual adaptive service from initialization preserves sound provenance for
every retained resolution packet authenticated as the prescribed owner. All
other player and wire policies remain arbitrary. -/
theorem runService_initial_resolutionOrigins
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (ordered : graph.BarrierOrdered) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (after : runtime.application.PolicyExecution)
    (member : after ∈ (runtime.runService roster reactionRounds players wire order count
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial inputs)))).support) :
    ResolutionOrigins runtime after owner := by
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial inputs))
  have initialHolds : ResolutionOriginInvariant runtime inputs initial owner :=
    ⟨State.initial_invariant inputs, runtime.policyCoherentAll_initial inputs owner,
      runtime.resolutionOrigins_initial inputs owner⟩
  exact (runtime.runService_invariant roster reactionRounds players wire order _
    (runtime.serviceStep_resolutionOriginInvariant inputs ordered owner policy players prescribed
      wire) count initial after initialHolds member).2.2

/-- Pointwise pending-packet form used by reserved resolution inclusion. -/
theorem ResolutionOrigins.pending_resolutionSubmission
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (origins : ResolutionOrigins runtime execution owner)
    (event : graph.EventId) (payload : L.Ty) (bindingOwner : Player)
    (binding : FieldRef graph.layout (.binding bindingOwner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve bindingOwner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve bindingOwner payload binding checks outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (sender : message.sender = owner) (addressed : message.payload.event? graph = some event) :
    ∃ action, execution.native.application.remembered event = some action ∧
      runtime.resolutionSubmission owner event payload binding checks outputEq action
          (MessageApplication.State.observe runtime.application execution.native owner) =
        .submit message.payload := by
  have valid := origins message (Or.inl pending)
  rcases valid event payload bindingOwner binding checks outputEq codeEq viewNode sender addressed
    with completed | ⟨action, _, cached, submission⟩
  · exact (ready.1 completed).elim
  · exact ⟨action, cached, submission⟩

end Vegas.EventGraphRuntime
