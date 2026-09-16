/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicies
import Vegas.Pending.EventService

/-! # Reserved owner blocks for prescribed event policies -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Private candidate preparation and remembering expose no application data
to the environment. Authentication restricts whose catalogue can be changed. -/
theorem privateStep_publicView (state : State graph) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).publicView = state.publicView := by
  cases command with
  | prepare => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · rw [privateStep, dif_pos owned]
        cases state.remembered event <;> rfl
      · rw [privateStep, dif_neg owned]

/-- The full environment observation, including the pending pool and receipts,
is unchanged by an actual private policy command. -/
@[simp] theorem afterPrivate_environmentView (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (command : PrivateCommand graph) :
    MessageApplication.State.environmentView runtime.application
        (runtime.application.afterPrivate execution who command).native =
      MessageApplication.State.environmentView runtime.application execution.native := by
  change MessageInterface.EnvironmentObservation.mk execution.native.pool
    (privateStep execution.native.application who command).publicView execution.native.receipts = _
  rw [privateStep_publicView]
  rfl

/-- Private commands by one player do not change another player's application
observation, including its authenticated candidate catalogue and choice cache. -/
theorem privateStep_playerView_other (state : State graph) (who observer : Player)
    (different : observer ≠ who) (command : PrivateCommand graph) :
    (privateStep state who command).playerView observer = state.playerView observer := by
  cases command with
  | prepare serial raw =>
      change { state.playerView observer with candidates := (fun slot =>
        (state.candidates.prepare who (.prepared serial) raw).lookup (observer, slot)) } =
          state.playerView observer
      have candidates : (fun slot =>
          (state.candidates.prepare who (.prepared serial) raw).lookup (observer, slot)) =
          fun slot => state.candidates.lookup (observer, slot) := by
        funext slot
        apply CommitmentCandidates.lookup_prepare_other
        intro same
        exact different (congrArg Prod.fst same)
      rw [candidates]
      rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · rw [privateStep, dif_pos owned]
        cases cached : state.remembered event with
        | some prior => rfl
        | none =>
            have memory : (fun query =>
                if graph.actor? query = some observer then
                  Function.update state.remembered event (some action) query else none) =
                fun query => if graph.actor? query = some observer then
                  state.remembered query else none := by
              funext query
              by_cases same : query = event
              · subst query
                have other : graph.actor? event ≠ some observer := by
                  rw [owned]
                  simpa only [ne_eq, Option.some.injEq] using different.symm
                simp only [other, ↓reduceIte]
              · rw [Function.update_of_ne same]
            dsimp only [State.playerView, State.publicView]
            rw [memory]
      · rw [privateStep, dif_neg owned]

/-- The complete native view of another player is unchanged by a private
policy command; pending-message observations remain included in the view. -/
@[simp] theorem afterPrivate_observe_other (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who observer : Player)
    (different : observer ≠ who) (command : PrivateCommand graph) :
    MessageApplication.State.observe runtime.application
        (runtime.application.afterPrivate execution who command).native observer =
      MessageApplication.State.observe runtime.application execution.native observer := by
  change MessageInterface.View.mk (execution.native.pool.observe observer)
    ((privateStep execution.native.application who command).playerView observer)
      execution.native.receipts = _
  rw [privateStep_playerView_other _ _ _ different]
  rfl

@[simp] theorem afterPrivate_history_self (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (command : PrivateCommand graph) :
    (runtime.application.afterPrivate execution who command).principalHistory who =
      execution.principalHistory who ++
        [⟨MessageApplication.State.observe runtime.application execution.native who,
          .privateCommand command⟩] := by
  simp [MessageApplication.afterPrivate]

@[simp] theorem afterSubmit_history_self (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (payload : Payload graph) :
    (runtime.application.afterSubmit execution who payload).principalHistory who =
      execution.principalHistory who ++
        [⟨MessageApplication.State.observe runtime.application execution.native who,
          .submit payload⟩] := by
  simp [MessageApplication.afterSubmit]

@[simp] theorem submittedAt_afterPrivate (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (command : PrivateCommand graph) (event : graph.EventId) :
    submittedAt ((runtime.application.afterPrivate execution who command).principalHistory who)
      event =
      submittedAt (execution.principalHistory who) event := by
  simp [submittedAt, MessageApplication.afterPrivate]

@[simp] theorem afterPrivate_config (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (command : PrivateCommand graph) :
    (runtime.application.afterPrivate execution who command).native.application.config =
      execution.native.application.config := by
  change (privateStep execution.native.application who command).config = _
  cases command with
  | prepare => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · rw [privateStep, dif_pos owned]
        cases execution.native.application.remembered event <;> rfl
      · rw [privateStep, dif_neg owned]

@[simp] theorem afterPrivate_serviceGrant (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (command : PrivateCommand graph) :
    (runtime.application.afterPrivate execution who command).native.application.serviceGrant =
      execution.native.application.serviceGrant := by
  change (privateStep execution.native.application who command).serviceGrant = _
  cases command with
  | prepare => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · rw [privateStep, dif_pos owned]
        cases execution.native.application.remembered event <;> rfl
      · rw [privateStep, dif_neg owned]

theorem afterPrivate_remembered_same (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (event : graph.EventId) (action : graph.Action event)
    (actor : graph.actor? event = some who)
    (empty : execution.native.application.remembered event = none) :
    (runtime.application.afterPrivate execution who
      (.remember event action)).native.application.remembered event = some action := by
  change (privateStep execution.native.application who
    (.remember event action)).remembered event = some action
  simp [privateStep, actor, empty]

/-- At the first opportunity for a ready binding event, the compiled policy
samples its normalized graph kernel and remembers exactly that action. -/
theorem compilePlayerPolicy_bind_stage_zero
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : view.application.publicView.serviceGrant = some event)
    (notSubmitted : submittedAt history event = false)
    (viewOwner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (stage : stagingCount history event = 0) :
    runtime.compilePlayerPolicy who policy history view =
      (graph.normalizePolicy who policy event actor
        (viewOwner ▸ view.application.observation)).map fun action =>
          .privateCommand (.remember event action) := by
  unfold compilePlayerPolicy
  rw [grant]
  simp [notSubmitted, viewOwner, ready, actor, viewNode, stage]

/-- At the second opportunity, the immutable remembered binding action alone
determines private preparation. No graph policy is sampled again. -/
theorem compilePlayerPolicy_bind_stage_one
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event)
    (grant : view.application.publicView.serviceGrant = some event)
    (notSubmitted : submittedAt history event = false)
    (viewOwner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (stage : stagingCount history event = 1)
    (remembered : view.application.remembered event = some action) :
    runtime.compilePlayerPolicy who policy history view =
      FinDist.pure (bindingStageCommand runtime event payload outputEq action) := by
  unfold compilePlayerPolicy
  rw [grant]
  simp [notSubmitted, viewOwner, ready, actor, viewNode, stage, remembered]

/-- At the third opportunity, a binding event emits the uniform opaque
commitment packet, independent of whether its remembered action succeeds. -/
theorem compilePlayerPolicy_bind_stage_two
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (grant : view.application.publicView.serviceGrant = some event)
    (notSubmitted : submittedAt history event = false)
    (viewOwner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (stage : 2 ≤ stagingCount history event) :
    runtime.compilePlayerPolicy who policy history view =
      FinDist.pure (.submit (.commitment event (who, eventSlot event))) := by
  obtain ⟨extra, countEq⟩ := Nat.exists_eq_add_of_le stage
  have countEq' : stagingCount history event = extra + 2 := by omega
  unfold compilePlayerPolicy
  rw [grant]
  simp [notSubmitted, viewOwner, ready, actor, viewNode, countEq']

/-- The exact three-command continuation after the unique graph-policy sample
has chosen a binding action. It uses the shared player transition throughout. -/
def bindingBlockContinuation (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    {owner : Player} (outputEq : graph.outputLayout event = .binding owner payload)
    (execution : runtime.application.PolicyExecution)
    (action : graph.Action event) : FinDist runtime.application.PolicyExecution :=
  (runtime.application.playerStep who execution
      (.privateCommand (.remember event action))).bind fun first =>
    (runtime.application.playerStep who first
      (bindingStageCommand runtime event payload outputEq action)).bind fun second =>
        runtime.application.playerStep who second
          (.submit (.commitment event (who, eventSlot event)))

/-- The actual three owner invocations draw the normalized binding action once
and then execute its deterministic private-stage and submission continuation. -/
theorem runServicePlan_compiled_bind_block
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewNode : nodeView graph event = .bind owner payload outputEq codeEq)
    (playersWho : players who = runtime.compilePlayerPolicy who policy)
    (grant : execution.native.application.serviceGrant = some event)
    (ready : execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (stage : stagingCount (execution.principalHistory who) event = 0)
    (notSubmitted : submittedAt (execution.principalHistory who) event = false)
    (emptyCache : execution.native.application.remembered event = none) :
    runtime.runServicePlan players wire (List.replicate 3 (.player who)) execution =
      (graph.normalizePolicy who policy event actor
        (graph.playerObserve who execution.native.application.config)).bind
          (runtime.bindingBlockContinuation who event payload outputEq execution) := by
  change runtime.runServicePlan players wire
    [.player who, .player who, .player who] execution = _
  simp only [runServicePlan, serviceStep, MessageApplication.invoke, playersWho]
  have initialReady : execution.native.application.publicView.EventReady event :=
    (State.publicView_eventReady execution.native.application event).2 ready
  rw [runtime.compilePlayerPolicy_bind_stage_zero who policy
    (execution.principalHistory who)
    (MessageApplication.State.observe runtime.application execution.native who)
    event owner payload outputEq codeEq viewNode (by
      change execution.native.application.serviceGrant = some event
      exact grant) notSubmitted rfl
    initialReady actor stage]
  rw [FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro action _
  rw [runtime.application.playerStep_private_eq execution who (.remember event action),
    FinDist.pure_bind]
  let first := runtime.application.afterPrivate execution who (.remember event action)
  have firstReady : first.native.application.publicView.EventReady event := by
    apply (State.publicView_eventReady first.native.application event).2
    simpa [first] using ready
  have firstRemembered : first.native.application.remembered event = some action := by
    exact runtime.afterPrivate_remembered_same execution who event action actor emptyCache
  have firstStage : stagingCount (first.principalHistory who) event = 1 := by
    simp [first, stage]
  have firstNotSubmitted : submittedAt (first.principalHistory who) event = false := by
    change submittedAt
      ((runtime.application.afterPrivate execution who
        (.remember event action)).principalHistory who)
      event = false
    rw [runtime.submittedAt_afterPrivate execution who (.remember event action) event]
    exact notSubmitted
  have firstPolicy := runtime.compilePlayerPolicy_bind_stage_one who policy
    (first.principalHistory who)
    (MessageApplication.State.observe runtime.application first.native who)
    event owner payload outputEq codeEq viewNode action (by
      change first.native.application.serviceGrant = some event
      simpa [first] using grant)
    firstNotSubmitted rfl firstReady actor firstStage (by
      simp only [MessageApplication.State.observe]
      change (State.playerView first.native.application who).remembered event = some action
      simp [State.playerView, actor, firstRemembered])
  rw [firstPolicy, FinDist.pure_bind]
  unfold bindingBlockContinuation
  rw [runtime.application.playerStep_private_eq execution who (.remember event action),
    FinDist.pure_bind]
  obtain ⟨command, commandEq⟩ :=
    runtime.bindingStageCommand_is_private event payload outputEq action
  rw [commandEq, runtime.application.playerStep_private_eq, FinDist.pure_bind]
  let second := runtime.application.afterPrivate first who command
  have secondReady : second.native.application.publicView.EventReady event := by
    apply (State.publicView_eventReady second.native.application event).2
    simpa [second, first] using ready
  have secondStage : 2 ≤ stagingCount (second.principalHistory who) event := by
    change 2 ≤ stagingCount
      ((runtime.application.afterPrivate first who command).principalHistory who) event
    rw [afterPrivate_history_self, ← commandEq,
      stagingCount_append_bindingStageCommand, firstStage]
  have secondNotSubmitted : submittedAt (second.principalHistory who) event = false := by
    change submittedAt
      ((runtime.application.afterPrivate first who command).principalHistory who) event = false
    rw [runtime.submittedAt_afterPrivate first who command event]
    exact firstNotSubmitted
  rw [runtime.compilePlayerPolicy_bind_stage_two who policy
    (second.principalHistory who)
    (MessageApplication.State.observe runtime.application second.native who)
    event owner payload outputEq codeEq viewNode (by
      change second.native.application.serviceGrant = some event
      simpa [second, first] using grant) secondNotSubmitted rfl secondReady actor secondStage]
  simp [runtime.application.playerStep_submit_eq]

end Vegas.EventGraphRuntime
