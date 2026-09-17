/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventHonestBoundary
import Vegas.Pending.EventBindingAcceptance
import Vegas.Pending.EventResolutionAcceptance
import Vegas.Pending.EventHonestReaction
import Vegas.EventGraph.StateCongruence

/-! # Strategic owner blocks from clean honest boundaries -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem privateStep_serviceGrant_eq (state : State graph) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).serviceGrant = state.serviceGrant := by
  cases command with
  | prepare serial raw => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · rw [privateStep, dif_pos owned]
        cases state.remembered event <;> rfl
      · rw [privateStep, dif_neg owned]

private theorem bindingStageCommand_remembered_other (runtime : EventGraphRuntime graph)
    (state : State graph) (owner : Player) (event query : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (command : PrivateCommand graph)
    (stage : runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command) (actor : graph.actor? event = some owner)
    (different : query ≠ event) :
    (privateStep (privateStep state owner (.remember event action)) owner command).remembered
      query = state.remembered query := by
  unfold bindingStageCommand at stage
  generalize cast (congrArg EventField.Action outputEq) action = result at stage
  cases result with
  | failure =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      cases remembered : state.remembered event <;>
        simp [privateStep, actor, remembered, Function.update, different]
  | success value =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      cases remembered : state.remembered event <;>
        simp [privateStep, actor, remembered, Function.update, different]

private theorem bindingStageCommand_stages_other (runtime : EventGraphRuntime graph)
    (event query : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (command : PrivateCommand graph)
    (stage : runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command) (different : query ≠ event) :
    stagesEvent (runtime := runtime) query (.privateCommand command) = false := by
  unfold bindingStageCommand at stage
  generalize cast (congrArg EventField.Action outputEq) action = result at stage
  cases result with
  | failure =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      simp [stagesEvent, different.symm]
  | success value =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      simp only [stagesEvent, decide_eq_false_iff_not]
      intro equal
      exact different (Fin.ext equal.symm)

private theorem bindingStageCommand_candidates_other (runtime : EventGraphRuntime graph)
    (state : State graph) (owner who : Player) (event query : graph.EventId)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (command : PrivateCommand graph)
    (stage : runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command) (actor : graph.actor? event = some owner)
    (different : query ≠ event) :
    (privateStep (privateStep state owner (.remember event action)) owner command).candidates.lookup
      (who, eventSlot query) = state.candidates.lookup (who, eventSlot query) := by
  unfold bindingStageCommand at stage
  generalize cast (congrArg EventField.Action outputEq) action = result at stage
  cases result with
  | failure =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      cases remembered : state.remembered event <;>
        simp [privateStep, actor, remembered]
  | success value =>
      simp only [MessageInterface.PlayerCommand.privateCommand.injEq] at stage
      subst command
      cases remembered : state.remembered event <;>
        simp only [privateStep, dif_pos actor, remembered, eventSlot]
      all_goals
        apply CommitmentCandidates.lookup_prepare_other
        intro same
        have slotEq := congrArg Prod.snd same
        apply different
        apply Fin.ext
        simpa [eventSlot] using Slot.prepared.inj slotEq

private theorem normalizedPolicyStep_of_actor (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (owner : Player) (actor : graph.actor? event = some owner) :
    graph.normalizedPolicyStep profile config event ready =
      (graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner config)).bind (config.step event ready) := by
  unfold EventGraph.normalizedPolicyStep
  split
  · rename_i who actual
    have same : who = owner := Option.some.inj (actual.symm.trans actor)
    subst who
    have proofEq : actual = actor := Subsingleton.elim _ _
    rw [proofEq]
  · rename_i impossible
    rw [actor] at impossible
    contradiction

omit [DecidableEq Player] in
theorem honestReactionPlan_allowed (roster : List Player) (reactionRounds : Nat) :
    ∀ instruction ∈
      (List.replicate reactionRounds (.wire :: roster.map .player)).flatten,
      HonestReactionInstruction (graph := graph) instruction := by
  intro instruction member
  rw [List.mem_flatten] at member
  obtain ⟨round, roundMem, instructionMem⟩ := member
  have roundEq : round = .wire :: roster.map .player :=
    List.eq_of_mem_replicate roundMem
  subst round
  simp only [List.mem_cons, List.mem_map] at instructionMem
  rcases instructionMem with rfl | ⟨who, _, rfl⟩ <;> trivial

/-- Honest reactions may randomize histories and receipts, but reserved
inclusion makes their final application configuration deterministic. -/
theorem runServicePlan_honestReaction_includeLatest_config
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
    (execution : runtime.application.PolicyExecution)
    (state : runtime.HonestReactionState event owner before accepted message execution) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (plan ++ [.includeLatest event owner]) execution).map
        (fun next => next.native.application.config) = FinDist.pure accepted.config := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro config configMem
  rw [FinDist.support_map, Set.mem_image] at configMem
  obtain ⟨next, nextMem, rfl⟩ := configMem
  have final := runtime.runServicePlan_honestReaction_includeLatest profile wire event owner
    before accepted message handled actor authored addressed grantBefore grantAccepted plan allowed
    execution next state nextMem
  simp [final.1]

/-- Pointwise state frames needed to restore a clean boundary after one
strategic completion. -/
structure StrategicCompletionFrames (before after : State graph)
    (event : graph.EventId) : Prop where
  completed : event ∈ after.config.cut.completed
  completedSubset : before.config.cut.completed ⊆ after.config.cut.completed
  remembered : ∀ query, query ≠ event → after.remembered query = before.remembered query
  accepted : ∀ query, query ≠ event →
    after.accepted (.inr query) = before.accepted (.inr query)
  candidate : ∀ query owner, query ≠ event →
    after.candidates.lookup (owner, eventSlot query) =
      before.candidates.lookup (owner, eventSlot query)
  unused : ∀ query owner, query ≠ event →
    before.HandleUnused (owner, eventSlot query) →
      after.HandleUnused (owner, eventSlot query)

omit [DecidableEq Player] in
theorem State.complete_strategicCompletionFrames (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    StrategicCompletionFrames state (state.complete event ready action value) event := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [State.complete]
  · exact state.config.cut.completed_subset_complete event ready
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro query owner different unused
    change state.HandleUnused (owner, eventSlot query)
    exact unused

/-- Installing the current binding handle frames every other event's clean
canonical slot and acceptance cell. -/
theorem State.acceptedBinding_strategicCompletionFrames (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (currentHandle : Handle graph)
    (handleSlot : currentHandle.2 = eventSlot event) :
    StrategicCompletionFrames state
      { (state.complete event ready action value) with
        accepted := Function.update state.accepted (.inr event) (some currentHandle)
        candidates := state.candidates.accept currentHandle } event := by
  have base := state.complete_strategicCompletionFrames event ready action value
  refine ⟨base.completed, base.completedSubset, base.remembered, ?_, ?_, ?_⟩
  · intro query different
    simp [Function.update, different]
  · intro query owner different
    apply CommitmentCandidates.lookup_accept_other
    intro same
    have slotEq := congrArg Prod.snd same
    rw [handleSlot] at slotEq
    apply different
    apply Fin.ext
    simpa [eventSlot] using Slot.prepared.inj slotEq
  · intro query owner different unused field accepted
    by_cases current : field = .inr event
    · subst field
      change Function.update state.accepted (.inr event) (some currentHandle) (.inr event) =
        some (owner, eventSlot query) at accepted
      have handleEq : currentHandle = (owner, eventSlot query) := by
        simpa [Function.update] using accepted
      have slotEq := congrArg Prod.snd handleEq
      rw [handleSlot] at slotEq
      apply different
      apply Fin.ext
      simpa [eventSlot] using (Slot.prepared.inj slotEq).symm
    · apply unused field
      simpa [Function.update, current] using accepted

/-- At a clean boundary, the prescribed binding owner block and its reserved
inclusion realize exactly the normalized graph step. -/
theorem HonestBoundary.bind_ownerBlock_law
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (List.replicate 3 (.player owner) ++ [.includeLatest event owner]) execution).map
        (fun next => next.native.application.config) =
      graph.normalizedPolicyStep profile execution.native.application.config event ready := by
  have unfinished := ready.1
  rw [runtime.runServicePlan_compiled_bind_includeLatest owner (profile owner)
    (runtime.compileProfile profile) wire execution event payload outputEq codeEq viewNode
    rfl grant ready actor
    (boundary.history_unfinished owner event unfinished).1
    (boundary.history_unfinished owner event unfinished).2
    (boundary.remembered_unfinished event unfinished) timely
    (boundary.canonical_fresh_unfinished event owner unfinished actor)
    (boundary.accepted_unfinished event unfinished)
    (boundary.canonical_unused_unfinished event owner unfinished actor)
    (boundary.lookup_eq_none (owner, execution.native.pool.nextSerial owner))]
  exact (normalizedPolicyStep_of_actor profile _ event ready owner actor).symm

/-- The actual binding owner block remains the normalized graph step with any
number of honest wire/player reaction rounds before reserved inclusion. -/
theorem HonestBoundary.bind_ownerBlock_reactions_law
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (roster : List Player) (reactionRounds : Nat)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (List.replicate 3 (.player owner) ++
        (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
        [.includeLatest event owner]) execution).map
        (fun next => next.native.application.config) =
      graph.normalizedPolicyStep profile execution.native.application.config event ready := by
  have unfinished := ready.1
  let reactions : List (ServiceInstruction graph) :=
    (List.replicate reactionRounds (.wire :: roster.map .player)).flatten
  change (runtime.runServicePlan (runtime.compileProfile profile) wire
    (List.replicate 3 (.player owner) ++
      (reactions ++ [.includeLatest event owner])) execution).map
        (fun next => next.native.application.config) = _
  rw [runtime.runServicePlan_append]
  rw [runtime.runServicePlan_compiled_bind_block owner (profile owner)
    (runtime.compileProfile profile) wire execution event owner payload outputEq codeEq viewNode
    rfl grant ready actor
    (boundary.history_unfinished owner event unfinished).1
    (boundary.history_unfinished owner event unfinished).2
    (boundary.remembered_unfinished event unfinished)]
  rw [FinDist.bind_bind, FinDist.map_bind]
  rw [normalizedPolicyStep_of_actor profile _ event ready owner actor]
  apply FinDist.bind_congr
  intro action actionMem
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  let staged := runtime.application.afterPrivate
    (runtime.application.afterPrivate execution owner (.remember event action)) owner command
  let submitted := runtime.application.afterSubmit staged owner
    (.commitment event (owner, eventSlot event))
  have block : runtime.bindingBlockContinuation owner event payload outputEq execution action =
      FinDist.pure submitted :=
    runtime.bindingBlockContinuation_eq_pure owner event payload outputEq execution action
      command stage
  rw [block, FinDist.pure_bind]
  have acceptedProjection := runtime.bindingBlockContinuation_handle owner event payload
    outputEq codeEq viewNode execution submitted action ready timely
    (boundary.canonical_fresh_unfinished event owner unfinished actor)
    (boundary.accepted_unfinished event unfinished)
    (boundary.canonical_unused_unfinished event owner unfinished actor)
    (by rw [block]; exact FinDist.mem_support_pure.mpr rfl)
    (execution.native.pool.nextSerial owner)
  change (handle runtime staged.native.application
    ⟨(owner, staged.native.pool.nextSerial owner),
      .commitment event (owner, eventSlot event)⟩).map State.config = _ at acceptedProjection
  cases handled : handle runtime staged.native.application
      ⟨(owner, staged.native.pool.nextSerial owner),
        .commitment event (owner, eventSlot event)⟩ with
  | none => simp [handled] at acceptedProjection
  | some accepted =>
      have configEq : accepted.config = execution.native.application.config.complete event ready
          action (cast (congrArg EventField.Value outputEq.symm)
            (cast (congrArg EventField.Action outputEq) action)) := Option.some.inj (by
        simpa only [handled, Option.map_some] using acceptedProjection)
      have initialState : runtime.HonestReactionState event owner staged.native.application
          accepted ⟨(owner, staged.native.pool.nextSerial owner),
            .commitment event (owner, eventSlot event)⟩ submitted := by
        refine ⟨?_, Or.inl ⟨rfl, ?_⟩⟩
        · have addressed :
              (Payload.commitment event (owner, eventSlot event)).event? graph = some event := rfl
          simp [submitted, MessageApplication.afterSubmit, submittedAt, addressed]
        · change execution.native.pool.pending ++ [_] = [_]
          rw [boundary.pending_empty, List.nil_append]
      have firstFacts := privateStep_facts execution.native.application owner
        (.remember event action)
      have secondFacts := privateStep_facts
        (privateStep execution.native.application owner (.remember event action)) owner command
      have stagedReady : staged.native.application.config.cut.Ready event := by
        change (privateStep
          (privateStep execution.native.application owner (.remember event action)) owner
            command).config.cut.Ready event
        rw [secondFacts.1, firstFacts.1]
        exact ready
      have stagedTimely : staged.native.application.WithinDeadline runtime event := by
        have clockEq : staged.native.application.clock =
            execution.native.application.clock := secondFacts.2.1.trans firstFacts.2.1
        have activatedEq : staged.native.application.activatedAt =
            execution.native.application.activatedAt := secondFacts.2.2.trans firstFacts.2.2
        simpa only [State.WithinDeadline, clockEq, activatedEq] using timely
      have acceptedFields : staged.native.application.accepted =
          execution.native.application.accepted := by
        exact (privateStep_accepted _ owner command).trans
          (privateStep_accepted _ owner (.remember event action))
      have stagedVacant : staged.native.application.accepted (.inr event) = none := by
        simpa only [acceptedFields] using
          boundary.accepted_unfinished event unfinished
      have stagedUnused : staged.native.application.HandleUnused
          (owner, eventSlot event) := by
        simpa only [State.HandleUnused, acceptedFields] using
          boundary.canonical_unused_unfinished event owner unfinished actor
      have exactHandle := runtime.handle_commitment_eq staged.native.application
        (owner, staged.native.pool.nextSerial owner) event (owner, eventSlot event)
        owner payload outputEq codeEq viewNode stagedReady stagedTimely rfl rfl
        stagedVacant stagedUnused
      rw [handled] at exactHandle
      have acceptedEq := Option.some.inj exactHandle
      have grantBefore : staged.native.application.serviceGrant = some event := by
        rw [show staged.native.application.serviceGrant =
          execution.native.application.serviceGrant from
            (privateStep_serviceGrant_eq _ owner command).trans
              (privateStep_serviceGrant_eq _ owner (.remember event action))]
        exact grant
      have grantAccepted : accepted.serviceGrant = some event := by
        rw [acceptedEq]
        simpa only [State.complete] using grantBefore
      have reactionLaw := runtime.runServicePlan_honestReaction_includeLatest_config profile wire
        event owner staged.native.application accepted
        ⟨(owner, staged.native.pool.nextSerial owner),
          .commitment event (owner, eventSlot event)⟩ handled actor rfl rfl
        grantBefore grantAccepted
        reactions (honestReactionPlan_allowed roster reactionRounds) submitted initialState
      change (runtime.runServicePlan (runtime.compileProfile profile) wire
        (reactions ++ [.includeLatest event owner]) submitted).map
          (fun next => next.native.application.config) = _
      rw [reactionLaw, configEq]
      have graphLaw := execution.native.application.config.step_eq_map_of_code event ready
        outputEq (.bind owner payload) codeEq
        (cast (congrArg EventField.Action outputEq) action)
        (FinDist.pure (cast (congrArg EventField.Action outputEq) action)) rfl
      simpa only [cast_cast, cast_eq, FinDist.map_pure] using graphLaw.symm

/-- Every execution supported by the reacted binding owner block restores the
clean honest boundary. -/
theorem HonestBoundary.bind_ownerBlock_reactions_boundary
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (roster : List Player) (reactionRounds : Nat)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner) :
    ∀ next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
      (List.replicate 3 (.player owner) ++
        (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
        [.includeLatest event owner]) execution).support,
      HonestBoundary runtime inputs next := by
  intro next member
  have unfinished := ready.1
  let reactions : List (ServiceInstruction graph) :=
    (List.replicate reactionRounds (.wire :: roster.map .player)).flatten
  change next ∈ (runtime.runServicePlan (runtime.compileProfile profile) wire
    (List.replicate 3 (.player owner) ++
      (reactions ++ [.includeLatest event owner])) execution).support at member
  rw [runtime.runServicePlan_append,
    runtime.runServicePlan_compiled_bind_block owner (profile owner)
      (runtime.compileProfile profile) wire execution event owner payload outputEq codeEq
      viewNode rfl grant ready actor
      (boundary.history_unfinished owner event unfinished).1
      (boundary.history_unfinished owner event unfinished).2
      (boundary.remembered_unfinished event unfinished), FinDist.bind_bind,
    FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨action, actionMem, supported⟩ := member
  obtain ⟨command, stage⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  let staged := runtime.application.afterPrivate
    (runtime.application.afterPrivate execution owner (.remember event action)) owner command
  let submitted := runtime.application.afterSubmit staged owner
    (.commitment event (owner, eventSlot event))
  have block : runtime.bindingBlockContinuation owner event payload outputEq execution action =
      FinDist.pure submitted :=
    runtime.bindingBlockContinuation_eq_pure owner event payload outputEq execution action
      command stage
  rw [block, FinDist.pure_bind] at supported
  have acceptedProjection := runtime.bindingBlockContinuation_handle owner event payload
    outputEq codeEq viewNode execution submitted action ready timely
    (boundary.canonical_fresh_unfinished event owner unfinished actor)
    (boundary.accepted_unfinished event unfinished)
    (boundary.canonical_unused_unfinished event owner unfinished actor)
    (by rw [block]; exact FinDist.mem_support_pure.mpr rfl)
    (execution.native.pool.nextSerial owner)
  change (handle runtime staged.native.application
    ⟨(owner, staged.native.pool.nextSerial owner),
      .commitment event (owner, eventSlot event)⟩).map State.config = _ at acceptedProjection
  cases handled : handle runtime staged.native.application
      ⟨(owner, staged.native.pool.nextSerial owner),
        .commitment event (owner, eventSlot event)⟩ with
  | none => simp [handled] at acceptedProjection
  | some accepted =>
      have firstInvariant := privateStep_invariant execution.native.application
        boundary.invariant owner (.remember event action)
      have stagedInvariant := privateStep_invariant _ firstInvariant owner command
      have firstBinding := privateStep_bindingInvariant execution.native.application
        boundary.bindingInvariant owner (.remember event action)
      have stagedBinding := privateStep_bindingInvariant _ firstBinding owner command
      have firstFacts := privateStep_facts execution.native.application owner
        (.remember event action)
      have secondFacts := privateStep_facts
        (privateStep execution.native.application owner (.remember event action)) owner command
      have stagedReady : staged.native.application.config.cut.Ready event := by
        change (privateStep
          (privateStep execution.native.application owner (.remember event action)) owner
            command).config.cut.Ready event
        rw [secondFacts.1, firstFacts.1]
        exact ready
      have stagedTimely : staged.native.application.WithinDeadline runtime event := by
        have clockEq : staged.native.application.clock =
            execution.native.application.clock := secondFacts.2.1.trans firstFacts.2.1
        have activatedEq : staged.native.application.activatedAt =
            execution.native.application.activatedAt := secondFacts.2.2.trans firstFacts.2.2
        simpa only [State.WithinDeadline, clockEq, activatedEq] using timely
      have acceptedFields : staged.native.application.accepted =
          execution.native.application.accepted :=
        (privateStep_accepted _ owner command).trans
          (privateStep_accepted _ owner (.remember event action))
      have stagedVacant : staged.native.application.accepted (.inr event) = none := by
        simpa only [acceptedFields] using boundary.accepted_unfinished event unfinished
      have stagedUnused : staged.native.application.HandleUnused
          (owner, eventSlot event) := by
        simpa only [State.HandleUnused, acceptedFields] using
          boundary.canonical_unused_unfinished event owner unfinished actor
      have exactHandle := runtime.handle_commitment_eq staged.native.application
        (owner, staged.native.pool.nextSerial owner) event (owner, eventSlot event)
        owner payload outputEq codeEq viewNode stagedReady stagedTimely rfl rfl
        stagedVacant stagedUnused
      rw [handled] at exactHandle
      have acceptedEq := Option.some.inj exactHandle
      have grantBefore : staged.native.application.serviceGrant = some event := by
        rw [show staged.native.application.serviceGrant =
          execution.native.application.serviceGrant from
            (privateStep_serviceGrant_eq _ owner command).trans
              (privateStep_serviceGrant_eq _ owner (.remember event action))]
        exact grant
      have grantAccepted : accepted.serviceGrant = some event := by
        rw [acceptedEq]
        simpa only [State.complete] using grantBefore
      have reactionState : runtime.HonestReactionState event owner
          staged.native.application accepted
          ⟨(owner, staged.native.pool.nextSerial owner),
            .commitment event (owner, eventSlot event)⟩ submitted := by
        refine ⟨?_, Or.inl ⟨rfl, ?_⟩⟩
        · have addressed :
              (Payload.commitment event (owner, eventSlot event)).event? graph = some event := rfl
          simp [submitted, MessageApplication.afterSubmit, submittedAt, addressed]
        · change execution.native.pool.pending ++ [_] = [_]
          rw [boundary.pending_empty, List.nil_append]
      have reacted := runtime.runServicePlan_honestReaction_includeLatest profile wire event
        owner staged.native.application accepted
        ⟨(owner, staged.native.pool.nextSerial owner),
          .commitment event (owner, eventSlot event)⟩ handled actor rfl rfl grantBefore
        grantAccepted reactions (honestReactionPlan_allowed roster reactionRounds)
        submitted next reactionState supported
      obtain ⟨nextState, nextEmpty, nextHistory⟩ := reacted
      have afterInvariant : next.native.application.Invariant inputs := by
        rw [nextState]
        exact handle_invariant runtime staged.native.application accepted _ stagedInvariant handled
      have afterBinding : next.native.application.BindingInvariant := by
        rw [nextState]
        exact handle_bindingInvariant runtime staged.native.application accepted _
          stagedBinding handled
      apply boundary.after_completed_event event afterInvariant afterBinding nextEmpty
      · rw [nextState, acceptedEq]
        simp [State.complete]
      · rw [nextState, acceptedEq]
        have configEq : staged.native.application.config =
            execution.native.application.config := secondFacts.1.trans firstFacts.1
        rw [← configEq]
        exact staged.native.application.config.cut.completed_subset_complete event stagedReady
      · intro query different
        rw [nextState, acceptedEq]
        change staged.native.application.remembered query = _
        exact bindingStageCommand_remembered_other runtime execution.native.application
          owner event query payload outputEq action command stage actor different
      · intro who query different
        rw [(nextHistory who query).1, (nextHistory who query).2]
        by_cases same : who = owner
        · subst who
          have stageOther := bindingStageCommand_stages_other runtime event query owner payload
            outputEq action command stage different
          have addressedOther :
              (Payload.commitment event (owner, eventSlot event)).event? graph ≠ some query := by
            intro same
            apply different
            change some event = some query at same
            exact (Option.some.inj same).symm
          simp only [stagingCount, stagesEvent, MessageApplication.afterSubmit,
            MessageApplication.afterPrivate, ↓reduceIte, List.append_assoc,
            List.cons_append, List.nil_append, List.filter_append, different.symm,
            decide_false, Bool.false_eq_true, not_false_eq_true,
            List.filter_cons_of_neg, List.length_append, Nat.add_eq_left,
            List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_cons,
            List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp,
            forall_eq, and_true, submittedAt, List.any_append, List.any_cons,
            addressedOther, List.any_nil, Bool.or_self, Bool.or_false, submitted, staged]
          exact stageOther
        · simp [submitted, staged, MessageApplication.afterSubmit,
            MessageApplication.afterPrivate, same]
      · intro query different
        rw [nextState, acceptedEq]
        rw [(staged.native.application.acceptedBinding_strategicCompletionFrames event
          stagedReady _ _ (owner, eventSlot event) rfl).accepted query different]
        exact congrFun acceptedFields (.inr query)
      · intro query who different
        rw [nextState, acceptedEq]
        rw [(staged.native.application.acceptedBinding_strategicCompletionFrames event
          stagedReady _ _ (owner, eventSlot event) rfl).candidate query who different]
        exact bindingStageCommand_candidates_other runtime execution.native.application owner who
          event query payload outputEq action command stage actor different
      · intro query who different unused
        rw [nextState, acceptedEq]
        apply (staged.native.application.acceptedBinding_strategicCompletionFrames event
          stagedReady _ _ (owner, eventSlot event) rfl).unused query who different
        simpa only [State.HandleUnused, acceptedFields] using unused

/-- At a clean boundary, the prescribed resolution owner block and its
reserved inclusion realize exactly the normalized graph step. -/
theorem HonestBoundary.resolve_ownerBlock_law
    (runtime : EventGraphRuntime graph) (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (boundary : HonestBoundary runtime inputs execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (actor : graph.actor? event = some owner) :
    (runtime.runServicePlan (runtime.compileProfile profile) wire
      (List.replicate 3 (.player owner) ++ [.includeLatest event owner]) execution).map
        (fun next => next.native.application.config) =
      graph.normalizedPolicyStep profile execution.native.application.config event ready := by
  have unfinished := ready.1
  rw [runtime.runServicePlan_compiled_resolve_includeLatest owner (profile owner)
    (runtime.compileProfile profile) wire execution event payload binding checks outputEq codeEq
    viewNode rfl grant ready timely boundary.bindingInvariant actor
    (boundary.history_unfinished owner event unfinished).1
    (boundary.history_unfinished owner event unfinished).2
    (boundary.remembered_unfinished event unfinished)
    (boundary.lookup_eq_none (owner, execution.native.pool.nextSerial owner))]
  exact (normalizedPolicyStep_of_actor profile _ event ready owner actor).symm

end Vegas.EventGraphRuntime
