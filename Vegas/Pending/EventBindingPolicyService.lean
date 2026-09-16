/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyService
import Vegas.Pending.EventCandidateProtection

/-! # Binding-policy coherence through adaptive event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Strong policy coherence at every unfinished binding event owned by one
prescribed player.  Completed events are deliberately outside the predicate. -/
def BindingPolicyCoherentAll (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player) : Prop :=
  ∀ event payload (outputEq : graph.outputLayout event = .binding owner payload),
    graph.actor? event = some owner →
    event ∉ execution.native.application.config.cut.completed →
    BindingPolicyCoherent runtime execution owner event payload outputEq

theorem bindingPolicyCoherentAll_initial (runtime : EventGraphRuntime graph)
    (input : graph.Inputs) (owner : Player) :
    BindingPolicyCoherentAll runtime
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input))) owner := by
  intro event payload outputEq actor _
  exact runtime.bindingPolicyCoherent_initial input owner event payload outputEq actor

/-- The strong binding predicate depends only on owner history, remembered
action, and the canonical candidate slot. -/
theorem BindingPolicyCoherent.copy
    (runtime : EventGraphRuntime graph)
    (before after : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime before owner event payload outputEq)
    (history : after.principalHistory owner = before.principalHistory owner)
    (remembered : after.native.application.remembered event =
      before.native.application.remembered event)
    (candidate : after.native.application.candidates.lookup (owner, eventSlot event) =
      before.native.application.candidates.lookup (owner, eventSlot event)) :
    BindingPolicyCoherent runtime after owner event payload outputEq := by
  refine ⟨coherent.1.copy runtime before after owner event history remembered, ?_, ?_⟩
  · intro stage
    rw [candidate]
    apply coherent.2.1
    simpa only [history] using stage
  · intro stage action cached
    have beforeStage : stagingCount (before.principalHistory owner) event = 2 := by
      simpa only [history] using stage
    have beforeCached : before.native.application.remembered event = some action := by
      simpa only [remembered] using cached
    have meaning := coherent.2.2 beforeStage action beforeCached
    unfold State.bindingResult at meaning ⊢
    rw [candidate]
    exact meaning

/-- Waiting changes only the owner's history by an irrelevant entry. -/
theorem BindingPolicyCoherent.afterWait
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq) :
    BindingPolicyCoherent runtime
      { execution with principalHistory := fun other =>
          if other = owner then execution.principalHistory owner ++
            [⟨MessageApplication.State.observe runtime.application execution.native owner,
              .wait⟩]
          else execution.principalHistory other }
      owner event payload outputEq := by
  refine ⟨coherent.1.afterWait runtime execution owner event, ?_, ?_⟩
  · intro stage
    apply coherent.2.1
    simpa [stagingCount, stagesEvent] using stage
  · intro stage action cached
    apply coherent.2.2 (action := action)
    · simpa [stagingCount, stagesEvent] using stage
    · exact cached

/-- The first remember stage preserves freshness of the canonical candidate. -/
theorem BindingPolicyCoherent.afterRemember
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (stage : stagingCount (execution.principalHistory owner) event = 0)
    (action : graph.Action event) :
    BindingPolicyCoherent runtime
      (runtime.application.afterPrivate execution owner (.remember event action))
      owner event payload outputEq := by
  refine ⟨coherent.1.afterRemember runtime execution owner event stage action, ?_, ?_⟩
  · intro _
    have fresh := coherent.2.1 (by omega)
    change (privateStep execution.native.application owner
      (.remember event action)).candidates.lookup (owner, eventSlot event) = .fresh
    rw [show (privateStep execution.native.application owner
      (.remember event action)).candidates = execution.native.application.candidates from by
        simp only [privateStep]
        split
        · split <;> rfl
        · rfl]
    exact fresh
  · intro impossible
    have history := runtime.afterPrivate_history_self execution owner (.remember event action)
    rw [history, stagingCount_append_remember, stage] at impossible
    omega

/-- Staging one event cannot change another event's canonical candidate. -/
theorem privateStep_candidate_other_of_stagesEvent
    (runtime : EventGraphRuntime graph) (state : State graph) (owner : Player)
    (event query : graph.EventId) (command : PrivateCommand graph)
    (different : query ≠ event)
    (staged : stagesEvent (runtime := runtime) event (.privateCommand command) = true) :
    (privateStep state owner command).candidates.lookup (owner, eventSlot query) =
      state.candidates.lookup (owner, eventSlot query) := by
  cases command with
  | remember remembered action =>
      simp only [privateStep]
      split
      · split <;> rfl
      · rfl
  | prepare serial raw =>
      simp only [stagesEvent, decide_eq_true_eq] at staged
      subst serial
      apply CommitmentCandidates.lookup_prepare_other
      intro same
      apply different
      apply Fin.ext
      simpa [eventSlot] using Slot.prepared.inj (congrArg Prod.snd same)

theorem BindingPolicyCoherent.afterPrivate_irrelevant
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (command : PrivateCommand graph)
    (notStage : stagesEvent (runtime := runtime) event (.privateCommand command) = false)
    (memory : (privateStep execution.native.application owner command).remembered event =
      execution.native.application.remembered event)
    (candidate : (privateStep execution.native.application owner command).candidates.lookup
      (owner, eventSlot event) =
        execution.native.application.candidates.lookup (owner, eventSlot event)) :
    BindingPolicyCoherent runtime
      (runtime.application.afterPrivate execution owner command)
      owner event payload outputEq := by
  have history := runtime.afterPrivate_history_self execution owner command
  have count : stagingCount
      ((runtime.application.afterPrivate execution owner command).principalHistory owner) event =
        stagingCount (execution.principalHistory owner) event := by
    rw [history]
    simp [stagingCount, notStage]
  refine ⟨coherent.1.afterPrivate_irrelevant runtime execution owner event command notStage
    memory, ?_, ?_⟩
  · intro stage
    change (privateStep execution.native.application owner command).candidates.lookup
      (owner, eventSlot event) = .fresh
    rw [candidate]
    exact coherent.2.1 (by simpa only [count] using stage)
  · intro stage action cached
    have beforeStage : stagingCount (execution.principalHistory owner) event = 2 := by
      simpa only [count] using stage
    have beforeCached : execution.native.application.remembered event = some action := by
      change (privateStep execution.native.application owner command).remembered event =
        some action at cached
      exact memory.symm.trans cached
    have meaning := coherent.2.2 beforeStage action beforeCached
    change State.bindingResult (privateStep execution.native.application owner command)
      (owner, eventSlot event) payload = _
    unfold State.bindingResult at meaning ⊢
    rw [candidate]
    exact meaning

theorem BindingPolicyCoherent.afterSubmit_other
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (packet : Payload graph) (other : packet.event? graph ≠ some event) :
    BindingPolicyCoherent runtime (runtime.application.afterSubmit execution owner packet)
      owner event payload outputEq := by
  refine ⟨coherent.1.afterSubmit_other runtime execution owner event packet other, ?_, ?_⟩
  · intro stage
    apply coherent.2.1
    have history := runtime.afterSubmit_history_self execution owner packet
    rw [history] at stage
    simpa [stagingCount, stagesEvent] using stage
  · intro stage action cached
    apply coherent.2.2 (action := action)
    · have history := runtime.afterSubmit_history_self execution owner packet
      rw [history] at stage
      simpa [stagingCount, stagesEvent] using stage
    · simpa [MessageApplication.afterSubmit] using cached

/-- At stage one of a binding event, the supported compiled private command
is exactly the canonical binding-stage command for the cached action. -/
theorem compilePlayerPolicy_nonwait_ready
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId)
    (grant : view.application.publicView.serviceGrant = some event)
    (command : Command runtime) (notWait : command ≠ .wait)
    (member : command ∈ (runtime.compilePlayerPolicy owner policy history view).support) :
    view.application.publicView.EventReady event := by
  unfold compilePlayerPolicy at member
  rw [grant] at member
  repeat' first | split at member
  all_goals subst_vars
  all_goals
    simp_all only [FinDist.mem_support_pure, FinDist.support_map, Set.mem_image,
      reduceCtorEq, Option.some.injEq]

theorem compilePlayerPolicy_binding_stage_one_command
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (grant : execution.native.application.serviceGrant = some event)
    (stage : stagingCount (execution.principalHistory owner) event = 1)
    (coherent : BindingPolicyCoherent runtime execution owner event payload outputEq)
    (command : PrivateCommand graph)
    (member : (.privateCommand command : Command runtime) ∈
      (runtime.compilePlayerPolicy owner policy (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)).support) :
    ∃ action, execution.native.application.remembered event = some action ∧
      runtime.bindingStageCommand event payload outputEq action = .privateCommand command := by
  have viewGrant :
      (MessageApplication.State.observe runtime.application execution.native
        owner).application.publicView.serviceGrant = some event := by
    change execution.native.application.serviceGrant = some event
    exact grant
  have ready := runtime.compilePlayerPolicy_nonwait_ready owner policy
    (execution.principalHistory owner)
    (MessageApplication.State.observe runtime.application execution.native owner)
    event viewGrant (.privateCommand command) (by simp) member
  have notSubmitted : submittedAt (execution.principalHistory owner) event = false := by
    cases submitted : submittedAt (execution.principalHistory owner) event
    · rfl
    · have completed := coherent.1.submitted_stage submitted
      omega
  obtain ⟨action, cached⟩ := coherent.1.cached_of_stage (by omega)
  have viewCached :
      (MessageApplication.State.observe runtime.application execution.native
        owner).application.remembered event = some action := by
    change (State.playerView execution.native.application owner).remembered event = some action
    simpa [State.playerView, coherent.1.actor] using cached
  have observedGrant :
      (MessageApplication.State.observe runtime.application execution.native
        owner).application.publicView.serviceGrant = some event := by
    change execution.native.application.serviceGrant = some event
    exact grant
  cases viewEq : nodeView graph event with
  | bind actualOwner actualPayload actualOutput codeEq =>
      have sameOutput : EventField.binding owner payload =
          .binding actualOwner actualPayload := outputEq.symm.trans actualOutput
      injection sameOutput with ownerEq payloadEq
      subst actualOwner
      subst actualPayload
      have proofEq : actualOutput = outputEq := Subsingleton.elim _ _
      cases proofEq
      have policyEq := runtime.compilePlayerPolicy_bind_stage_one owner policy
        (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)
        event owner payload outputEq codeEq viewEq action observedGrant notSubmitted rfl ready
        coherent.1.actor stage viewCached
      rw [policyEq] at member
      simp only [FinDist.mem_support_pure] at member
      exact ⟨action, cached, member.symm⟩
  | resolve actualOwner actualPayload binding checks actualOutput codeEq =>
      have impossible : EventField.binding owner payload = .publication actualPayload :=
        outputEq.symm.trans actualOutput
      cases impossible
  | sample actualPayload law actualOutput codeEq =>
      have impossible : EventField.binding owner payload = .publicData actualPayload :=
        outputEq.symm.trans actualOutput
      cases impossible

/-- Other-player commands preserve strong coherence at all still-unfinished
binding events of the prescribed owner. -/
theorem playerStep_other_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph)
    (execution next : runtime.application.PolicyExecution)
    (focal owner : Player) (different : owner ≠ focal)
    (command : Command runtime)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.playerStep focal execution command).support) :
    BindingPolicyCoherentAll runtime next owner := by
  intro event payload outputEq actor unfinished
  cases command with
  | privateCommand privateCommand =>
      rw [runtime.application.playerStep_private_eq] at supported
      simp only [FinDist.mem_support_pure] at supported
      subst next
      have frame := runtime.afterPrivate_opponent_event execution focal owner different
        event actor privateCommand
      apply (coherent event payload outputEq actor
        (fun completed => unfinished (frame.2.2.2.2.mpr completed))
        ).copy runtime execution _ owner event payload outputEq frame.1 frame.2.1
      exact frame.2.2.1
  | submit packet =>
      rw [runtime.application.playerStep_submit_eq] at supported
      simp only [FinDist.mem_support_pure] at supported
      subst next
      have frame := runtime.afterSubmit_opponent_event execution focal owner different event packet
      apply (coherent event payload outputEq actor unfinished).copy runtime execution _ owner event
        payload outputEq frame.1 frame.2.1
      exact frame.2.2.1
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at supported
      subst next
      apply (coherent event payload outputEq actor unfinished).copy runtime execution _ owner event
        payload outputEq
      · simp [different]
      · rfl
      · rfl
  | wait =>
      rw [runtime.application.playerStep_wait] at supported
      simp only [FinDist.mem_support_pure] at supported
      subst next
      apply (coherent event payload outputEq actor unfinished).copy runtime execution _ owner event
        payload outputEq
      · simp [different]
      · rfl
      · rfl

/-- Environment transitions preserve the canonical candidate of every event
that remains unfinished, assuming retained owner commitments are canonical. -/
theorem environmentPolicyStep_candidate_of_unfinished
    (runtime : EventGraphRuntime graph) (owner : Player)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (safe : execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (event : graph.EventId)
    (unfinished : event ∉ next.native.application.config.cut.completed)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    next.native.application.candidates.lookup (owner, eventSlot event) =
      execution.native.application.candidates.lookup (owner, eventSlot event) := by
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      simpa only using congrArg
        (fun state : runtime.application.State =>
          state.application.candidates.lookup (owner, eventSlot event)) native
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at native
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup] at native
          simpa only using congrArg
            (fun state : runtime.application.State =>
              state.application.candidates.lookup (owner, eventSlot event)) native
      | some message =>
          have canonical : CanonicalCommitments owner message :=
            safe.1 message (List.mem_of_find?_eq_some lookup)
          cases accepted : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                lookup accepted] at native
              simpa only using congrArg
                (fun state : runtime.application.State =>
                  state.application.candidates.lookup (owner, eventSlot event)) native
          | some state =>
              rw [runtime.application.includePending_accept execution.native id message state
                lookup accepted] at native
              have nextEq : next.native.application = state := by
                simpa only using congrArg
                  (fun result : runtime.application.State => result.application) native
              have stateUnfinished : event ∉ state.config.cut.completed := by
                simpa only [nextEq] using unfinished
              rw [nextEq]
              exact (runtime.handle_unfinished_canonical_resources
                execution.native.application state message owner event canonical accepted
                stateUnfinished).1
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at native
      obtain ⟨state, stateMem, same⟩ := native
      have nextEq : next.native.application = state := by
        exact congrArg (fun result : runtime.application.State => result.application) same.symm
      rw [nextEq]
      exact congrArg
        (fun candidates => candidates.lookup (owner, eventSlot event))
        (environmentStep_tables runtime execution.native.application state applicationCommand
          stateMem).2

/-- Environment-policy execution preserves strong coherence for every
binding event that remains unfinished. -/
theorem environmentPolicyStep_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (safe : execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    BindingPolicyCoherentAll runtime next owner := by
  have histories := runtime.application.environmentStep_principalHistory execution command next
    supported
  have remembered := runtime.environmentPolicyStep_remembered execution next command supported
  have native : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  have completed : execution.native.application.config.cut.completed ⊆
      next.native.application.config.cut.completed := by
    cases actionEq : command.toAction with
    | none =>
        simp only [actionEq, FinDist.mem_support_pure] at native
        rw [native]
    | some action =>
        simp only [actionEq] at native
        exact applicationStep_completed_subset runtime execution.native next.native action native
  intro event payload outputEq actor unfinished
  apply (coherent event payload outputEq actor (fun prior => unfinished (completed prior))).copy
    runtime execution next owner event payload outputEq
  · exact congrFun histories owner
  · exact congrFun remembered event
  · exact runtime.environmentPolicyStep_candidate_of_unfinished owner execution next command
      safe event unfinished supported

/-- One supported command of the compiled owner preserves strong coherence
at every unfinished binding event. -/
theorem compilePlayerPolicy_playerStep_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (execution next : runtime.application.PolicyExecution)
    (event : graph.EventId)
    (grant : execution.native.application.serviceGrant = some event)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (command : Command runtime)
    (commandMem : command ∈
      (runtime.compilePlayerPolicy owner policy (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)).support)
    (stepMem : next ∈ (runtime.application.playerStep owner execution command).support) :
    BindingPolicyCoherentAll runtime next owner := by
  have atEvent := runtime.compilePlayerPolicy_commandAt owner policy
    (execution.principalHistory owner)
    (MessageApplication.State.observe runtime.application execution.native owner)
    event (by
      change execution.native.application.serviceGrant = some event
      exact grant) command commandMem
  cases command with
  | wait =>
      rw [runtime.application.playerStep_wait] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      intro query payload outputEq actor unfinished
      exact (coherent query payload outputEq actor unfinished).afterWait runtime execution owner
        query payload outputEq
  | replay id =>
      simp [CommandAt, stagesEvent] at atEvent
  | privateCommand privateCommand =>
      rw [runtime.application.playerStep_private_eq] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      obtain ⟨stagedEvent, stagedGrant, stageLt, staged⟩ :=
        runtime.compilePlayerPolicy_private_stage owner policy
          (execution.principalHistory owner)
          (MessageApplication.State.observe runtime.application execution.native owner)
          privateCommand commandMem
      have stagedEq : stagedEvent = event := by
        change execution.native.application.serviceGrant = some stagedEvent at stagedGrant
        rw [grant] at stagedGrant
        exact Option.some.inj stagedGrant.symm
      subst stagedEvent
      intro query payload outputEq actor unfinished
      have unfinishedBefore : query ∉ execution.native.application.config.cut.completed := by
        intro completed
        apply unfinished
        rw [runtime.afterPrivate_config]
        exact completed
      by_cases same : query = event
      · subst query
        have current := coherent event payload outputEq actor unfinishedBefore
        rcases Nat.eq_zero_or_pos
            (stagingCount (execution.principalHistory owner) event) with stageZero | stagePositive
        · obtain ⟨action, commandEq⟩ :=
            runtime.compilePlayerPolicy_private_zero_is_remember owner policy execution event
              grant stageZero privateCommand commandMem
          subst privateCommand
          exact current.afterRemember runtime execution owner event payload outputEq stageZero
            action
        · have stageOne : stagingCount (execution.principalHistory owner) event = 1 := by
            omega
          obtain ⟨action, cached, commandEq⟩ :=
            runtime.compilePlayerPolicy_binding_stage_one_command owner policy execution event
              payload outputEq grant stageOne current privateCommand commandMem
          exact current.afterBindingStage runtime execution owner event payload outputEq stageOne
            action cached privateCommand commandEq
      · have notStage := runtime.stagesEvent_other_of_stagesEvent event query privateCommand
          same staged
        have memory := runtime.privateStep_remembered_other_of_stagesEvent
          execution.native.application owner event query privateCommand
          (by
            have nonwait := runtime.compilePlayerPolicy_nonwait_actor owner policy
              (execution.principalHistory owner)
              (MessageApplication.State.observe runtime.application execution.native owner)
              event (by
                change execution.native.application.serviceGrant = some event
                exact grant) (.privateCommand privateCommand) (by simp) commandMem
            exact nonwait)
          same staged
        have candidate := runtime.privateStep_candidate_other_of_stagesEvent
          execution.native.application owner event query privateCommand same staged
        exact (coherent query payload outputEq actor unfinishedBefore).afterPrivate_irrelevant
          runtime execution owner query payload outputEq privateCommand notStage memory candidate
  | submit packet =>
      rw [runtime.application.playerStep_submit_eq] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      have eventActor := runtime.compilePlayerPolicy_nonwait_actor owner policy
        (execution.principalHistory owner)
        (MessageApplication.State.observe runtime.application execution.native owner)
        event (by
          change execution.native.application.serviceGrant = some event
          exact grant) (.submit packet) (by simp) commandMem
      have stageGe := runtime.compilePlayerPolicy_submit_stage owner policy execution event grant
        packet commandMem
      rcases atEvent with wait | stagedCommand | addressed
      · contradiction
      · simp [stagesEvent] at stagedCommand
      · obtain ⟨addressedPacket, packetEq, packetAddress⟩ := addressed
        injection packetEq with packetEq
        subst addressedPacket
        intro query payload outputEq actor unfinished
        by_cases same : query = event
        · subst query
          have current := coherent event payload outputEq eventActor unfinished
          have stage : stagingCount (execution.principalHistory owner) event = 2 := by
            have stageLe := current.1.stage_le
            omega
          exact current.afterSubmit runtime execution owner event payload outputEq stage packet
            packetAddress
        · apply (coherent query payload outputEq actor unfinished).afterSubmit_other
            runtime execution owner query payload outputEq packet
          intro queryAddress
          rw [packetAddress] at queryAddress
          exact same (Option.some.inj queryAddress.symm)

theorem compilePlayerPolicy_invoke_bindingPolicyCoherentAll_anyGrant
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.application.invoke players environment execution (.player owner)).support) :
    BindingPolicyCoherentAll runtime next owner := by
  cases grant : execution.native.application.serviceGrant with
  | some event =>
      simp only [MessageApplication.invoke, ownerCompiled, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, commandMem, stepMem⟩ := supported
      exact runtime.compilePlayerPolicy_playerStep_bindingPolicyCoherentAll owner policy execution
        next event grant coherent command commandMem stepMem
  | none =>
      simp only [MessageApplication.invoke, ownerCompiled, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, commandMem, stepMem⟩ := supported
      have observedGrant :
          (MessageApplication.State.observe runtime.application execution.native
            owner).application.publicView.serviceGrant = none := by
        change execution.native.application.serviceGrant = none
        exact grant
      unfold compilePlayerPolicy at commandMem
      rw [observedGrant] at commandMem
      simp only [FinDist.mem_support_pure] at commandMem
      subst command
      rw [runtime.application.playerStep_wait] at stepMem
      simp only [FinDist.mem_support_pure] at stepMem
      subst next
      intro event payload outputEq actor unfinished
      exact (coherent event payload outputEq actor unfinished).afterWait runtime execution owner
        event payload outputEq

theorem playerInvoke_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (who : Player)
    (supported : next ∈
      (runtime.application.invoke players environment execution (.player who)).support) :
    BindingPolicyCoherentAll runtime next owner := by
  by_cases same : who = owner
  · subst who
    exact runtime.compilePlayerPolicy_invoke_bindingPolicyCoherentAll_anyGrant owner policy
      players environment execution next ownerCompiled coherent supported
  · simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨command, _, stepMem⟩ := supported
    exact runtime.playerStep_other_bindingPolicyCoherentAll execution next who owner
      (Ne.symm same) command coherent stepMem

/-- One concrete service instruction preserves unfinished binding coherence.
The canonical-pool premise is needed only by possible environment inclusion. -/
theorem serviceStep_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (safe : execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    BindingPolicyCoherentAll runtime next owner := by
  cases instruction with
  | player who =>
      exact runtime.playerInvoke_bindingPolicyCoherentAll owner policy players
        (runtime.application.wireEnvironment wire) execution next ownerCompiled coherent who
        supported
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, _, stepMem⟩ := supported
      exact runtime.environmentPolicyStep_bindingPolicyCoherentAll owner execution next command
        safe coherent stepMem
  | grant event | includeLatest event who | sample event | tick | expire event =>
      exact runtime.environmentPolicyStep_bindingPolicyCoherentAll owner execution next _ safe
        coherent supported

/-- A finite concrete service plan preserves unfinished binding coherence and
uses canonical provenance at each intermediate inclusion. -/
theorem runServicePlan_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (plan : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (safe : execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈ (runtime.runServicePlan players wire plan execution).support) :
    BindingPolicyCoherentAll runtime next owner := by
  induction plan generalizing execution with
  | nil =>
      simp only [runServicePlan, FinDist.mem_support_pure] at supported
      subst next
      exact coherent
  | cons instruction rest ih =>
      simp only [runServicePlan, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, head, tail⟩ := supported
      have singleton : middle ∈
          (runtime.runServicePlan players wire [instruction] execution).support := by
        simpa [runServicePlan] using head
      have safeMiddle := runtime.runServicePlan_canonicalCommitments owner policy players
        ownerCompiled wire [instruction] execution middle safe singleton
      exact ih middle safeMiddle
        (runtime.serviceStep_bindingPolicyCoherentAll owner policy players wire instruction
          execution middle ownerCompiled safe coherent head) tail

theorem serviceEpoch_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (safe : execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.serviceEpoch roster reactionRounds players wire order execution).support) :
    BindingPolicyCoherentAll runtime next owner := by
  simp only [serviceEpoch, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨chosen, _, planMem⟩ := supported
  exact runtime.runServicePlan_bindingPolicyCoherentAll owner policy players wire
    (epochPlan chosen roster reactionRounds) execution next ownerCompiled safe coherent planMem

/-- Actual adaptive service preserves strong prescribed binding coherence,
while all other player policies remain unrestricted. -/
theorem runService_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (execution next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (safe : execution.native.pool.Satisfies
      (CanonicalCommitments (graph := graph) owner))
    (coherent : BindingPolicyCoherentAll runtime execution owner)
    (supported : next ∈
      (runtime.runService roster reactionRounds players wire order count execution).support) :
    BindingPolicyCoherentAll runtime next owner := by
  induction count generalizing execution with
  | zero =>
      simp only [runService, FinDist.mem_support_pure] at supported
      subst next
      exact coherent
  | succ count ih =>
      simp only [runService, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, epochMem, tail⟩ := supported
      have safeMiddle := runtime.serviceEpoch_canonicalCommitments owner policy roster
        reactionRounds players ownerCompiled wire order execution middle safe epochMem
      exact ih middle safeMiddle
        (runtime.serviceEpoch_bindingPolicyCoherentAll owner policy roster reactionRounds players
          wire order execution middle ownerCompiled safe coherent epochMem) tail

/-- From the native empty-pool initialization, every unfinished prescribed
binding event remains coherent throughout the actual adaptive service. -/
theorem runService_initial_bindingPolicyCoherentAll
    (runtime : EventGraphRuntime graph) (input : graph.Inputs) (owner : Player)
    (policy : graph.BehavioralPolicy owner)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (count : Nat) (next : runtime.application.PolicyExecution)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner policy)
    (supported : next ∈
      (runtime.runService roster reactionRounds players wire order count
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input)))).support) :
    BindingPolicyCoherentAll runtime next owner := by
  exact runtime.runService_bindingPolicyCoherentAll owner policy roster reactionRounds players wire
    order count _ next ownerCompiled MessagePool.Satisfies.empty
    (runtime.bindingPolicyCoherentAll_initial input owner) supported

end Vegas.EventGraphRuntime
