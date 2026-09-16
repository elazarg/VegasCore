/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayLocality

/-! # Replay at a focal event's completion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Player invocations can stage or publish messages but cannot themselves
complete a graph event. Inclusion is an environment operation. -/
theorem serviceStep_player_config (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (owner : Player)
    (before after : runtime.application.PolicyExecution)
    (supported : after ∈ (runtime.serviceStep players wire (.player owner) before).support) :
    after.native.application.config = before.native.application.config := by
  simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
    Set.mem_iUnion] at supported
  obtain ⟨command, _, step⟩ := supported
  have native : after.native ∈ ((runtime.application.playerStep owner before command).map
      MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, step, rfl⟩
  rw [runtime.application.playerStep_native] at native
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      exact privateStep_config before.native.application owner command
  | submit packet | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]

/-- A newly completed event in a sample instruction belongs to chance,
never to a strategic player. -/
theorem serviceStep_sample_completed_actor (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (query event : graph.EventId)
    (before after : runtime.application.PolicyExecution)
    (supported : after ∈ (runtime.serviceStep players wire (.sample query) before).support)
    (unfinished : event ∉ before.native.application.config.cut.completed)
    (completed : event ∈ after.native.application.config.cut.completed) :
    graph.actor? event = none := by
  have native : after.native ∈ ((runtime.application.environmentPolicyStep before
      (.application (.executeSample query))).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at native
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_map, Set.mem_image] at native
  obtain ⟨next, nextMem, nativeEq⟩ := native
  have applicationEq : after.native.application = next := by rw [← nativeEq]
  change next ∈ (environmentStep runtime before.native.application (.executeSample query)).support
    at nextMem
  rw [applicationEq] at completed
  obtain ⟨_, stutter | ⟨ready, action, step, _⟩⟩ :=
    runtime.environmentStep_executeSample_config_activated before.native.application next query
      nextMem
  · rw [stutter.1] at completed
    exact (unfinished completed).elim
  · have same : event = query := by
      rw [before.native.application.config.step_cut query ready action next.config step,
        EventOrder.Cut.mem_complete] at completed
      exact completed.resolve_right unfinished
    subst event
    by_contra notSample
    have nonsample : ∀ (payload : L.Ty) (law : PublicDist graph.layout payload)
        (outputEq : graph.outputLayout query = .publicData payload)
        (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
          (graph.nodes query) = .sample payload law),
        nodeView graph query = .sample payload law outputEq codeEq → False := by
      intro payload law outputEq codeEq _
      apply notSample
      exact (EventCode.actor_cast outputEq (graph.nodes query)).symm.trans
        (congrArg EventCode.actor codeEq)
    rw [runtime.environmentStep_executeSample_of_nonsample before.native.application query ready
      nonsample, FinDist.mem_support_pure] at nextMem
    rw [nextMem] at completed
    exact unfinished completed

private theorem serviceControlStep_instruction_support (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ServiceControl runtime)
    (instruction : ServiceInstruction graph) (rest : List (ServiceInstruction graph))
    (plan : before.plan = instruction :: rest)
    (supported : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support) :
    after.execution ∈ (runtime.serviceStep players wire instruction before.execution).support := by
  simp only [serviceControlStep, plan, FinDist.support_map, Set.mem_image] at supported
  obtain ⟨execution, executionMem, equal⟩ := supported
  rw [← equal]
  exact executionMem

/-- At an actual focal completion, the endpoint-dependent branches of the
paired transition theorem cannot occur: player calls do not complete events,
and samples complete only chance events. -/
theorem ServiceReplay.completionPaired
    (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (ordered : graph.BarrierOrdered) (focal : Player)
    (focalResponse : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixedFocal : players focal = fun history view => FinDist.pure (focalResponse history view))
    (wireResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → WireCommand Player)
    (fixedWire : wire = fun history view => FinDist.pure (wireResponse history view))
    (orderResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → ServiceOrder graph)
    (fixedOrder : order = fun history view => FinDist.pure (orderResponse history view))
    (prescribedOthers : ∀ who, who ≠ focal →
      ∃ policy : graph.BehavioralPolicy who, players who = runtime.compilePlayerPolicy who policy)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    {left right leftNext rightNext : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : ServiceReplay runtime focal left right)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support)
    (completion :
      (∃ (ready : left.execution.native.application.config.cut.Ready event)
          (action : graph.Action event),
          leftNext.execution.native.application.config ∈
            (left.execution.native.application.config.step event ready action).support) ∨
        ∃ (ready : right.execution.native.application.config.cut.Ready event)
          (action : graph.Action event),
          rightNext.execution.native.application.config ∈
            (right.execution.native.application.config.step event ready action).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have newlyCompleted {before after : ServiceControl runtime}
      (stepped : ∃ (ready : before.execution.native.application.config.cut.Ready event)
          (action : graph.Action event),
          after.execution.native.application.config ∈
            (before.execution.native.application.config.step event ready action).support) :
      event ∉ before.execution.native.application.config.cut.completed ∧
        event ∈ after.execution.native.application.config.cut.completed := by
    obtain ⟨ready, action, step⟩ := stepped
    refine ⟨ready.1, ?_⟩
    rw [before.execution.native.application.config.step_cut event ready action
      after.execution.native.application.config step, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  apply replay.pairedControlStep runtime inputs roster reactionRounds players wire order ordered
    focal focalResponse fixedFocal wireResponse fixedWire orderResponse fixedOrder prescribedOthers
    leftReachable rightReachable leftSupported rightSupported
  · intro owner _ policy _ rest query plan _
    exfalso
    have impossible {before after : ServiceControl runtime}
        (plan : before.plan = .player owner :: rest)
        (supported : after ∈
          (runtime.serviceControlStep roster reactionRounds players wire order before).support)
        (facts : event ∉ before.execution.native.application.config.cut.completed ∧
          event ∈ after.execution.native.application.config.cut.completed) : False := by
      have same := runtime.serviceStep_player_config players wire owner before.execution
        after.execution (serviceControlStep_instruction_support runtime roster reactionRounds
          players wire order before after (.player owner) rest plan supported)
      rw [same] at facts
      exact facts.1 facts.2
    rcases completion with leftStep | rightStep
    · exact impossible plan leftSupported (newlyCompleted leftStep)
    · exact impossible (replay.plan.symm.trans plan) rightSupported (newlyCompleted rightStep)
  · intro query rest plan
    exfalso
    have impossible {before after : ServiceControl runtime}
        (plan : before.plan = .sample query :: rest)
        (supported : after ∈
          (runtime.serviceControlStep roster reactionRounds players wire order before).support)
        (facts : event ∉ before.execution.native.application.config.cut.completed ∧
          event ∈ after.execution.native.application.config.cut.completed) : False := by
      have ownerless := runtime.serviceStep_sample_completed_actor players wire query event
        before.execution after.execution (serviceControlStep_instruction_support runtime roster
          reactionRounds players wire order before after (.sample query) rest plan supported)
        facts.1 facts.2
      rw [actor] at ownerless
      contradiction
    rcases completion with leftStep | rightStep
    · exact impossible plan leftSupported (newlyCompleted leftStep)
    · exact impossible (replay.plan.symm.trans plan) rightSupported (newlyCompleted rightStep)

end Vegas.EventGraphRuntime
