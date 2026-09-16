/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventBindingPolicyService
import Vegas.Pending.EventBindingAcceptance
import Vegas.Pending.EventResolutionAcceptance

/-! # Prescribed owner blocks from coherent partial stages -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The exact envelope authored with the sender's pre-block serial remains in
the pending pool after a player-only reserved block. -/
def AuthoredPending (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution)
    (who : Player) (payload : Payload graph) : Prop :=
  (⟨(who, before.native.pool.nextSerial who), payload⟩ :
      Message Player (Payload graph)) ∈ after.native.pool.pending

/-- A resolution block retains the exact addressed packet generated from the
cached action by the prescribed resolution command. -/
def ResolutionAuthoredPending (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    {owner : Player} (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) : Prop :=
  ∃ action packet,
    after.native.application.remembered event = some action ∧
    runtime.resolutionSubmission who event payload binding checks outputEq action
        (MessageApplication.State.observe runtime.application after.native who) =
      .submit packet ∧
    AuthoredPending runtime before after who packet

/-- Once an owner submission is recorded, its compiled policy waits without
changing the native state. -/
theorem compilePlayerPolicy_wait_of_submitted
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId)
    (grant : view.application.publicView.serviceGrant = some event)
    (submitted : submittedAt history event = true) :
    runtime.compilePlayerPolicy owner policy history view = FinDist.pure .wait := by
  unfold compilePlayerPolicy
  rw [grant]
  simp [submitted]

/-- From any coherent, not-yet-submitted binding stage, the three reserved
owner calls record an addressed submission.  Stage zero samples once; stages
one and two reuse the existing cached action. -/
theorem runServicePlan_compiled_bind_partial_submitted
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (notSubmitted : submittedAt (execution.principalHistory owner) event = false)
    (supported : next ∈
      (runtime.runServicePlan players wire (List.replicate 3 (.player owner))
        execution).support) :
    submittedAt (next.principalHistory owner) event = true ∧
      AuthoredPending runtime execution next owner
        (.commitment event (owner, eventSlot event)) := by
  have actor := coherent.1.actor
  have publicReady : execution.native.application.publicView.EventReady event :=
    (State.publicView_eventReady execution.native.application event).2 ready
  change next ∈ (runtime.runServicePlan players wire
    [.player owner, .player owner, .player owner] execution).support at supported
  rcases Nat.eq_zero_or_pos
      (stagingCount (execution.principalHistory owner) event) with stageZero | stagePositive
  · have empty := coherent.1.empty_iff.mp stageZero
    have block := runtime.runServicePlan_compiled_bind_block owner policy players wire execution
      event owner payload outputEq codeEq viewNode ownerCompiled grant ready actor stageZero
      notSubmitted empty
    have block' : runtime.runServicePlan players wire
        [.player owner, .player owner, .player owner] execution =
        (graph.normalizePolicy owner policy event actor
          (graph.playerObserve owner execution.native.application.config)).bind
            (runtime.bindingBlockContinuation owner event payload outputEq execution) := by
      simpa using block
    rw [block'] at supported
    simp only [FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨action, _, continuation⟩ := supported
    obtain ⟨command, commandEq⟩ :=
      runtime.bindingStageCommand_is_private event payload outputEq action
    rw [runtime.bindingBlockContinuation_eq_pure owner event payload outputEq execution action
      command commandEq, FinDist.mem_support_pure] at continuation
    subst next
    constructor
    · simp [MessageApplication.afterSubmit, submittedAt, Payload.event?]
    · change (⟨(owner, execution.native.pool.nextSerial owner),
          .commitment event (owner, eventSlot event)⟩ : Message Player (Payload graph)) ∈
        execution.native.pool.pending ++
          [⟨(owner, execution.native.pool.nextSerial owner),
            .commitment event (owner, eventSlot event)⟩]
      simp
  · have stageLe := coherent.1.stage_le
    have stageOneOrTwo : stagingCount (execution.principalHistory owner) event = 1 ∨
        stagingCount (execution.principalHistory owner) event = 2 := by omega
    rcases stageOneOrTwo with stageOne | stageTwo
    · obtain ⟨action, cached⟩ := coherent.1.cached_of_stage (by omega)
      have viewCached :
          (MessageApplication.State.observe runtime.application execution.native
            owner).application.remembered event = some action := by
        change (State.playerView execution.native.application owner).remembered event = some action
        simpa [State.playerView, actor] using cached
      have firstPolicy := runtime.compilePlayerPolicy_bind_stage_one owner policy
        (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)
        event owner payload outputEq codeEq viewNode action (by
          change execution.native.application.serviceGrant = some event
          exact grant) notSubmitted rfl publicReady actor stageOne viewCached
      obtain ⟨privateCommand, commandEq⟩ :=
        runtime.bindingStageCommand_is_private event payload outputEq action
      let first := runtime.application.afterPrivate execution owner privateCommand
      have firstGrant : first.native.application.serviceGrant = some event := by
        simpa [first] using grant
      have firstReady : first.native.application.publicView.EventReady event := by
        apply (State.publicView_eventReady first.native.application event).2
        simpa [first] using ready
      have firstStage : 2 ≤ stagingCount (first.principalHistory owner) event := by
        change 2 ≤ stagingCount
          ((runtime.application.afterPrivate execution owner privateCommand).principalHistory
            owner) event
        rw [runtime.afterPrivate_history_self, ← commandEq,
          runtime.stagingCount_append_bindingStageCommand, stageOne]
      have firstNotSubmitted : submittedAt (first.principalHistory owner) event = false := by
        simpa [first] using runtime.submittedAt_afterPrivate execution owner privateCommand event
          |>.trans notSubmitted
      have secondPolicy := runtime.compilePlayerPolicy_bind_stage_two owner policy
        (first.principalHistory owner)
        (MessageApplication.State.observe runtime.application first.native owner)
        event owner payload outputEq codeEq viewNode (by
          change first.native.application.serviceGrant = some event
          exact firstGrant) firstNotSubmitted rfl firstReady actor firstStage
      simp only [runServicePlan, serviceStep, MessageApplication.invoke, ownerCompiled] at supported
      rw [firstPolicy, FinDist.pure_bind, commandEq,
        runtime.application.playerStep_private_eq, FinDist.pure_bind] at supported
      change next ∈
        (((runtime.compilePlayerPolicy owner policy (first.principalHistory owner)
          (MessageApplication.State.observe runtime.application first.native owner)).bind
            (runtime.application.playerStep owner first)).bind fun middle =>
              ((runtime.compilePlayerPolicy owner policy (middle.principalHistory owner)
                (MessageApplication.State.observe runtime.application middle.native owner)).bind
                  (runtime.application.playerStep owner middle)).bind fun final =>
                    FinDist.pure final).support at supported
      rw [secondPolicy, FinDist.pure_bind, runtime.application.playerStep_submit_eq,
        FinDist.pure_bind] at supported
      let second := runtime.application.afterSubmit first owner
        (.commitment event (owner, eventSlot event))
      have secondSubmitted : submittedAt (second.principalHistory owner) event = true := by
        simp [second, first, MessageApplication.afterSubmit, submittedAt, Payload.event?]
      have secondGrant :
          (MessageApplication.State.observe runtime.application second.native
            owner).application.publicView.serviceGrant = some event := by
        change first.native.application.serviceGrant = some event
        exact firstGrant
      rw [runtime.compilePlayerPolicy_wait_of_submitted owner policy
        (second.principalHistory owner)
        (MessageApplication.State.observe runtime.application second.native owner)
        event secondGrant secondSubmitted,
        FinDist.pure_bind, runtime.application.playerStep_wait,
        FinDist.pure_bind, FinDist.mem_support_pure] at supported
      subst next
      constructor
      · simp [second, first, MessageApplication.afterSubmit, submittedAt,
          Payload.event?] at secondSubmitted ⊢
      · change (⟨(owner, execution.native.pool.nextSerial owner),
            .commitment event (owner, eventSlot event)⟩ : Message Player (Payload graph)) ∈
          execution.native.pool.pending ++
            [⟨(owner, execution.native.pool.nextSerial owner),
              .commitment event (owner, eventSlot event)⟩]
        simp
    · obtain ⟨action, cached⟩ := coherent.1.cached_of_stage (by omega)
      have firstPolicy := runtime.compilePlayerPolicy_bind_stage_two owner policy
        (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)
        event owner payload outputEq codeEq viewNode (by
          change execution.native.application.serviceGrant = some event
          exact grant) notSubmitted rfl publicReady actor (by omega)
      simp only [runServicePlan, serviceStep, MessageApplication.invoke, ownerCompiled] at supported
      rw [firstPolicy, FinDist.pure_bind, runtime.application.playerStep_submit_eq,
        FinDist.pure_bind] at supported
      let first := runtime.application.afterSubmit execution owner
        (.commitment event (owner, eventSlot event))
      have firstSubmitted : submittedAt (first.principalHistory owner) event = true := by
        simp [first, MessageApplication.afterSubmit, submittedAt, Payload.event?]
      have firstGrant :
          (MessageApplication.State.observe runtime.application first.native
            owner).application.publicView.serviceGrant = some event := by
        change execution.native.application.serviceGrant = some event
        exact grant
      rw [runtime.compilePlayerPolicy_wait_of_submitted owner policy
        (first.principalHistory owner)
        (MessageApplication.State.observe runtime.application first.native owner)
        event firstGrant firstSubmitted,
        FinDist.pure_bind, runtime.application.playerStep_wait, FinDist.pure_bind] at supported
      let second : runtime.application.PolicyExecution :=
        { first with principalHistory := fun other =>
            if other = owner then first.principalHistory owner ++
              [⟨MessageApplication.State.observe runtime.application first.native owner, .wait⟩]
            else first.principalHistory other }
      have secondSubmitted : submittedAt (second.principalHistory owner) event = true := by
        simpa [second, submittedAt, stagesEvent] using firstSubmitted
      have secondGrant :
          (MessageApplication.State.observe runtime.application second.native
            owner).application.publicView.serviceGrant = some event := by
        change first.native.application.serviceGrant = some event
        exact firstGrant
      rw [runtime.compilePlayerPolicy_wait_of_submitted owner policy
        (second.principalHistory owner)
        (MessageApplication.State.observe runtime.application second.native owner)
        event secondGrant secondSubmitted,
        FinDist.pure_bind, runtime.application.playerStep_wait,
        FinDist.pure_bind, FinDist.mem_support_pure] at supported
      subst next
      constructor
      · simp [second, first, MessageApplication.afterSubmit, submittedAt,
          Payload.event?] at secondSubmitted ⊢
      · change (⟨(owner, execution.native.pool.nextSerial owner),
            .commitment event (owner, eventSlot event)⟩ : Message Player (Payload graph)) ∈
          execution.native.pool.pending ++
            [⟨(owner, execution.native.pool.nextSerial owner),
              .commitment event (owner, eventSlot event)⟩]
        simp

/-- From any coherent, not-yet-submitted resolution stage, the three reserved
owner calls record an addressed submission. -/
theorem runServicePlan_compiled_resolve_partial_submitted
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution next : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (whoCompiled : players who = runtime.compilePlayerPolicy who policy)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (coherent : PolicyCoherent runtime execution who event)
    (notSubmitted : submittedAt (execution.principalHistory who) event = false)
    (supported : next ∈
      (runtime.runServicePlan players wire (List.replicate 3 (.player who))
        execution).support) :
    submittedAt (next.principalHistory who) event = true ∧
      ResolutionAuthoredPending runtime execution next who event payload binding checks
        outputEq := by
  have actor := coherent.actor
  have publicReady : execution.native.application.publicView.EventReady event :=
    (State.publicView_eventReady execution.native.application event).2 ready
  change next ∈ (runtime.runServicePlan players wire
    [.player who, .player who, .player who] execution).support at supported
  rcases Nat.eq_zero_or_pos
      (stagingCount (execution.principalHistory who) event) with stageZero | stagePositive
  · have empty := coherent.empty_iff.mp stageZero
    have block := runtime.runServicePlan_compiled_resolve_block who policy players wire execution
      event owner payload binding checks outputEq codeEq viewNode whoCompiled grant ready actor
      stageZero notSubmitted empty
    have block' : runtime.runServicePlan players wire
        [.player who, .player who, .player who] execution =
        (graph.normalizePolicy who policy event actor
          (graph.playerObserve who execution.native.application.config)).bind
            (runtime.resolutionBlockContinuation who event payload binding checks outputEq
              execution) := by
      simpa using block
    rw [block'] at supported
    simp only [FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨action, _, continuation⟩ := supported
    let first := runtime.application.afterPrivate execution who (.remember event action)
    let second := runtime.application.afterPrivate first who (.remember event action)
    obtain ⟨packet, submission, addressed⟩ := runtime.resolutionSubmission_address who event
      payload binding checks outputEq action
      (MessageApplication.State.observe runtime.application second.native who)
    have firstRemembered : first.native.application.remembered event = some action :=
      runtime.afterPrivate_remembered_same execution who event action actor empty
    have secondRemembered : second.native.application.remembered event = some action := by
      change (privateStep first.native.application who
        (.remember event action)).remembered event = some action
      simp [privateStep, actor, firstRemembered]
    have continuationEq :
        runtime.resolutionBlockContinuation who event payload binding checks outputEq execution
            action = FinDist.pure (runtime.application.afterSubmit second who packet) := by
      simp only [resolutionBlockContinuation, runtime.application.playerStep_private_eq,
        FinDist.pure_bind]
      rw [submission, runtime.application.playerStep_submit_eq]
    rw [continuationEq, FinDist.mem_support_pure] at continuation
    subst next
    constructor
    · simp [second, first, MessageApplication.afterSubmit, submittedAt, addressed]
    · refine ⟨action, packet, ?_, ?_, ?_⟩
      · change second.native.application.remembered event = some action
        exact secondRemembered
      · simpa [resolutionSubmission, resolutionPayload, MessageApplication.State.observe,
          second, first, MessageApplication.afterSubmit] using submission
      · change (⟨(who, execution.native.pool.nextSerial who), packet⟩ :
            Message Player (Payload graph)) ∈
          execution.native.pool.pending ++
            [⟨(who, execution.native.pool.nextSerial who), packet⟩]
        simp
  · have stageOneOrTwo : stagingCount (execution.principalHistory who) event = 1 ∨
        stagingCount (execution.principalHistory who) event = 2 := by
      have stageLe := coherent.stage_le
      omega
    obtain ⟨action, cached⟩ := coherent.cached_of_stage stagePositive
    have viewCached :
        (MessageApplication.State.observe runtime.application execution.native
          who).application.remembered event = some action := by
      change (State.playerView execution.native.application who).remembered event = some action
      simpa [State.playerView, actor] using cached
    rcases stageOneOrTwo with stageOne | stageTwo
    · have firstPolicy := runtime.compilePlayerPolicy_resolve_stage_one who policy
        (execution.principalHistory who)
        (MessageApplication.State.observe runtime.application execution.native who)
        event owner payload binding checks outputEq codeEq viewNode action (by
          change execution.native.application.serviceGrant = some event
          exact grant) notSubmitted rfl publicReady actor stageOne viewCached
      let first := runtime.application.afterPrivate execution who (.remember event action)
      have firstGrant : first.native.application.serviceGrant = some event := by
        simpa [first] using grant
      have firstReady : first.native.application.publicView.EventReady event := by
        apply (State.publicView_eventReady first.native.application event).2
        simpa [first] using ready
      have firstStage : 2 ≤ stagingCount (first.principalHistory who) event := by
        simp [first, stageOne]
      have firstNotSubmitted : submittedAt (first.principalHistory who) event = false := by
        simpa [first] using runtime.submittedAt_afterPrivate execution who
          (.remember event action) event |>.trans notSubmitted
      have firstRemembered : first.native.application.remembered event = some action := by
        change (privateStep execution.native.application who
          (.remember event action)).remembered event = some action
        simp [privateStep, actor, cached]
      have secondPolicy := runtime.compilePlayerPolicy_resolve_stage_two who policy
        (first.principalHistory who)
        (MessageApplication.State.observe runtime.application first.native who)
        event owner payload binding checks outputEq codeEq viewNode action (by
          change first.native.application.serviceGrant = some event
          exact firstGrant) firstNotSubmitted rfl firstReady actor firstStage (by
          change (State.playerView first.native.application who).remembered event = some action
          simp [State.playerView, actor, firstRemembered])
      obtain ⟨packet, submission, addressed⟩ := runtime.resolutionSubmission_address who event
        payload binding checks outputEq action
        (MessageApplication.State.observe runtime.application first.native who)
      simp only [runServicePlan, serviceStep, MessageApplication.invoke, whoCompiled] at supported
      rw [firstPolicy, FinDist.pure_bind, runtime.application.playerStep_private_eq,
        FinDist.pure_bind] at supported
      change next ∈
        (((runtime.compilePlayerPolicy who policy (first.principalHistory who)
          (MessageApplication.State.observe runtime.application first.native who)).bind
            (runtime.application.playerStep who first)).bind fun middle =>
              ((runtime.compilePlayerPolicy who policy (middle.principalHistory who)
                (MessageApplication.State.observe runtime.application middle.native who)).bind
                  (runtime.application.playerStep who middle)).bind fun final =>
                    FinDist.pure final).support at supported
      rw [secondPolicy, FinDist.pure_bind, submission,
        runtime.application.playerStep_submit_eq, FinDist.pure_bind] at supported
      let second := runtime.application.afterSubmit first who packet
      have secondSubmitted : submittedAt (second.principalHistory who) event = true := by
        simp [second, first, MessageApplication.afterSubmit, submittedAt, addressed]
      have secondGrant :
          (MessageApplication.State.observe runtime.application second.native
            who).application.publicView.serviceGrant = some event := by
        change first.native.application.serviceGrant = some event
        exact firstGrant
      rw [runtime.compilePlayerPolicy_wait_of_submitted who policy
        (second.principalHistory who)
        (MessageApplication.State.observe runtime.application second.native who)
        event secondGrant secondSubmitted,
        FinDist.pure_bind, runtime.application.playerStep_wait,
        FinDist.pure_bind, FinDist.mem_support_pure] at supported
      subst next
      constructor
      · simp [first, MessageApplication.afterSubmit, submittedAt, addressed]
      · refine ⟨action, packet, ?_, ?_, ?_⟩
        · change first.native.application.remembered event = some action
          exact firstRemembered
        · simpa [resolutionSubmission, resolutionPayload, MessageApplication.State.observe,
            first, MessageApplication.afterSubmit] using submission
        · change (⟨(who, execution.native.pool.nextSerial who), packet⟩ :
              Message Player (Payload graph)) ∈
            execution.native.pool.pending ++
              [⟨(who, execution.native.pool.nextSerial who), packet⟩]
          simp
    · have firstPolicy := runtime.compilePlayerPolicy_resolve_stage_two who policy
        (execution.principalHistory who)
        (MessageApplication.State.observe runtime.application execution.native who)
        event owner payload binding checks outputEq codeEq viewNode action (by
          change execution.native.application.serviceGrant = some event
          exact grant) notSubmitted rfl publicReady actor (by omega) viewCached
      obtain ⟨packet, submission, addressed⟩ := runtime.resolutionSubmission_address who event
        payload binding checks outputEq action
        (MessageApplication.State.observe runtime.application execution.native who)
      simp only [runServicePlan, serviceStep, MessageApplication.invoke, whoCompiled] at supported
      rw [firstPolicy, FinDist.pure_bind, submission,
        runtime.application.playerStep_submit_eq, FinDist.pure_bind] at supported
      let first := runtime.application.afterSubmit execution who packet
      have firstSubmitted : submittedAt (first.principalHistory who) event = true := by
        simp [first, MessageApplication.afterSubmit, submittedAt, addressed]
      have firstGrant :
          (MessageApplication.State.observe runtime.application first.native
            who).application.publicView.serviceGrant = some event := by
        change execution.native.application.serviceGrant = some event
        exact grant
      rw [runtime.compilePlayerPolicy_wait_of_submitted who policy
        (first.principalHistory who)
        (MessageApplication.State.observe runtime.application first.native who)
        event firstGrant firstSubmitted,
        FinDist.pure_bind, runtime.application.playerStep_wait, FinDist.pure_bind] at supported
      let second : runtime.application.PolicyExecution :=
        { first with principalHistory := fun other =>
            if other = who then first.principalHistory who ++
              [⟨MessageApplication.State.observe runtime.application first.native who, .wait⟩]
            else first.principalHistory other }
      have secondSubmitted : submittedAt (second.principalHistory who) event = true := by
        simpa [second, submittedAt] using firstSubmitted
      have secondGrant :
          (MessageApplication.State.observe runtime.application second.native
            who).application.publicView.serviceGrant = some event := by
        change first.native.application.serviceGrant = some event
        exact firstGrant
      rw [runtime.compilePlayerPolicy_wait_of_submitted who policy
        (second.principalHistory who)
        (MessageApplication.State.observe runtime.application second.native who)
        event secondGrant secondSubmitted,
        FinDist.pure_bind, runtime.application.playerStep_wait,
        FinDist.pure_bind, FinDist.mem_support_pure] at supported
      subst next
      constructor
      · simp [MessageApplication.afterSubmit, submittedAt, addressed]
      · refine ⟨action, packet, ?_, ?_, ?_⟩
        · change execution.native.application.remembered event = some action
          exact cached
        · simpa [resolutionSubmission, resolutionPayload, MessageApplication.State.observe,
            MessageApplication.afterSubmit] using submission
        · change (⟨(who, execution.native.pool.nextSerial who), packet⟩ :
              Message Player (Payload graph)) ∈
            execution.native.pool.pending ++
              [⟨(who, execution.native.pool.nextSerial who), packet⟩]
          simp

end Vegas.EventGraphRuntime
