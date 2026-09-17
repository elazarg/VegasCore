/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicyBlock

/-! # Reserved owner blocks for prescribed resolution policies -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

theorem compilePlayerPolicy_resolve_stage_zero
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
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

theorem compilePlayerPolicy_resolve_stage_one
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event)
    (grant : view.application.publicView.serviceGrant = some event)
    (notSubmitted : submittedAt history event = false)
    (viewOwner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (stage : stagingCount history event = 1)
    (remembered : view.application.remembered event = some action) :
    runtime.compilePlayerPolicy who policy history view =
      FinDist.pure (.privateCommand (.remember event action)) := by
  unfold compilePlayerPolicy
  rw [grant]
  simp [notSubmitted, viewOwner, ready, actor, viewNode, stage, remembered]

theorem compilePlayerPolicy_resolve_stage_two
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event)
    (grant : view.application.publicView.serviceGrant = some event)
    (notSubmitted : submittedAt history event = false)
    (viewOwner : view.application.who = who)
    (ready : view.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (stage : 2 ≤ stagingCount history event)
    (remembered : view.application.remembered event = some action) :
    runtime.compilePlayerPolicy who policy history view =
      FinDist.pure (runtime.resolutionSubmission who event payload binding checks
        outputEq action view) := by
  obtain ⟨extra, countEq⟩ := Nat.exists_eq_add_of_le stage
  have countEq' : stagingCount history event = extra + 2 := by omega
  unfold compilePlayerPolicy
  rw [grant]
  simp [notSubmitted, viewOwner, ready, actor, viewNode, countEq', remembered]

def resolutionBlockContinuation (runtime : EventGraphRuntime graph) (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    {owner : Player} (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (execution : runtime.application.PolicyExecution)
    (action : graph.Action event) : FinDist runtime.application.PolicyExecution :=
  (runtime.application.playerStep who execution
      (.privateCommand (.remember event action))).bind fun first =>
    (runtime.application.playerStep who first
      (.privateCommand (.remember event action))).bind fun second =>
        runtime.application.playerStep who second
          (runtime.resolutionSubmission who event payload binding checks outputEq action
            (MessageApplication.State.observe runtime.application second.native who))

theorem runServicePlan_compiled_resolve_block
    (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (execution : runtime.application.PolicyExecution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
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
          (runtime.resolutionBlockContinuation who event payload binding checks outputEq
            execution) := by
  change runtime.runServicePlan players wire
    [.player who, .player who, .player who] execution = _
  simp only [runServicePlan, serviceStep, MessageApplication.invoke, playersWho]
  have initialReady : execution.native.application.publicView.EventReady event :=
    (State.publicView_eventReady execution.native.application event).2 ready
  rw [runtime.compilePlayerPolicy_resolve_stage_zero who policy
    (execution.principalHistory who)
    (MessageApplication.State.observe runtime.application execution.native who)
    event owner payload binding checks outputEq codeEq viewNode (by
      change execution.native.application.serviceGrant = some event
      exact grant) notSubmitted rfl initialReady actor stage]
  rw [FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro action _
  rw [runtime.application.playerStep_private_eq execution who (.remember event action),
    FinDist.pure_bind]
  let first := runtime.application.afterPrivate execution who (.remember event action)
  have firstReady : first.native.application.publicView.EventReady event := by
    apply (State.publicView_eventReady first.native.application event).2
    simpa [first] using ready
  have firstRemembered : first.native.application.remembered event = some action :=
    runtime.afterPrivate_remembered_same execution who event action actor emptyCache
  have firstStage : stagingCount (first.principalHistory who) event = 1 := by
    simp [first, stage]
  have firstNotSubmitted : submittedAt (first.principalHistory who) event = false := by
    change submittedAt
      ((runtime.application.afterPrivate execution who
        (.remember event action)).principalHistory who) event = false
    rw [runtime.submittedAt_afterPrivate execution who (.remember event action) event]
    exact notSubmitted
  have firstPolicy := runtime.compilePlayerPolicy_resolve_stage_one who policy
    (first.principalHistory who)
    (MessageApplication.State.observe runtime.application first.native who)
    event owner payload binding checks outputEq codeEq viewNode action (by
      change first.native.application.serviceGrant = some event
      simpa [first] using grant) firstNotSubmitted rfl firstReady actor firstStage (by
      simp only [MessageApplication.State.observe]
      change (State.playerView first.native.application who).remembered event = some action
      simp [State.playerView, actor, firstRemembered])
  rw [firstPolicy, FinDist.pure_bind]
  unfold resolutionBlockContinuation
  rw [runtime.application.playerStep_private_eq execution who (.remember event action),
    FinDist.pure_bind]
  rw [runtime.application.playerStep_private_eq first who (.remember event action),
    FinDist.pure_bind]
  let second := runtime.application.afterPrivate first who (.remember event action)
  have secondReady : second.native.application.publicView.EventReady event := by
    apply (State.publicView_eventReady second.native.application event).2
    simpa [second, first] using ready
  have secondRemembered : second.native.application.remembered event = some action := by
    change (privateStep first.native.application who
      (.remember event action)).remembered event = some action
    simp [privateStep, actor, firstRemembered]
  have secondStage : 2 ≤ stagingCount (second.principalHistory who) event := by
    simp [second, firstStage]
  have secondNotSubmitted : submittedAt (second.principalHistory who) event = false := by
    change submittedAt
      ((runtime.application.afterPrivate first who
        (.remember event action)).principalHistory who) event = false
    rw [runtime.submittedAt_afterPrivate first who (.remember event action) event]
    exact firstNotSubmitted
  rw [runtime.compilePlayerPolicy_resolve_stage_two who policy
    (second.principalHistory who)
    (MessageApplication.State.observe runtime.application second.native who)
    event owner payload binding checks outputEq codeEq viewNode action (by
      change second.native.application.serviceGrant = some event
      simpa [second, first] using grant) secondNotSubmitted rfl secondReady actor secondStage (by
      simp only [MessageApplication.State.observe]
      change (State.playerView second.native.application who).remembered event = some action
      simp [State.playerView, actor, secondRemembered])]
  simp [second]

end Vegas.EventGraphRuntime
