/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayInitialization
import Vegas.Pending.EventServiceReachability
import Vegas.Pending.EventExpiryObservation
import Vegas.Pending.EventResolutionEndpoint

/-! # Structural locality of reached focal actions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Endpoint-aware lockstep comparison retaining actual reachability of every
intermediate pair. -/
inductive ReachableServicePathComparison (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (leftEnd rightEnd : ServiceControl runtime) : Prop
  | same (replay : ServiceReplay runtime focal leftEnd rightEnd)
      (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
        leftEnd)
      (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
        rightEnd)
  | leftShort (rightAt rightNext : ServiceControl runtime)
      (replay : ServiceReplay runtime focal leftEnd rightAt)
      (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
        leftEnd)
      (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
        rightAt)
      (step : rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        rightAt).support)
      (suffix : ServiceControlPath runtime roster reactionRounds players wire order
        rightNext rightEnd)
  | rightShort (leftAt leftNext : ServiceControl runtime)
      (replay : ServiceReplay runtime focal leftAt rightEnd)
      (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
        leftAt)
      (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
        rightEnd)
      (step : leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        leftAt).support)
      (suffix : ServiceControlPath runtime roster reactionRounds players wire order
        leftNext leftEnd)

/-- Endpoint-aware comparison whose semantic step receives actual reachability
proofs for the two current controls. -/
theorem ServiceControlPath.compareEndpointReachable (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) {leftEnd rightEnd : ServiceControl runtime}
    (paired : ∀ {left right leftNext rightNext : ServiceControl runtime},
      ServiceReachable runtime inputs roster reactionRounds players wire order left →
      ServiceReachable runtime inputs roster reactionRounds players wire order right →
      ServiceReplay runtime focal left right →
      leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        left).support →
      rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        right).support →
      ServiceControlPath runtime roster reactionRounds players wire order leftNext leftEnd →
      ServiceControlPath runtime roster reactionRounds players wire order rightNext rightEnd →
      ServiceReplay runtime focal leftNext rightNext)
    {left right : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (initial : ServiceReplay runtime focal left right)
    (leftPath : ServiceControlPath runtime roster reactionRounds players wire order
      left leftEnd)
    (rightPath : ServiceControlPath runtime roster reactionRounds players wire order
      right rightEnd) :
    ReachableServicePathComparison runtime inputs roster reactionRounds players wire order focal
      leftEnd rightEnd := by
  induction leftPath generalizing right with
  | nil =>
      cases rightPath with
      | nil => exact .same initial leftReachable rightReachable
      | cons rightStep rightTail =>
          exact .leftShort _ _ initial leftReachable rightReachable rightStep rightTail
  | cons leftStep leftTail ih =>
      cases rightPath with
      | nil =>
          exact .rightShort _ _ initial leftReachable rightReachable leftStep leftTail
      | cons rightStep rightTail =>
          apply ih paired
          · exact .step leftReachable leftStep
          · exact .step rightReachable rightStep
          · exact paired leftReachable rightReachable initial leftStep rightStep leftTail
              rightTail
          · exact rightTail

namespace NativeReplay

/-- An arbitrary common include command at reachable prefixes preserves
replay when every foreign sender uses its prescribed policy. -/
theorem environmentInclude_reachable (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (ordered : graph.BarrierOrdered) (focal : Player)
    (prescribedOthers : ∀ who, who ≠ focal →
      ∃ policy : graph.BehavioralPolicy who,
        players who = runtime.compilePlayerPolicy who policy)
    {left right : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : NativeReplay runtime focal left.execution right.execution)
    (id : MessageId Player)
    {leftNext rightNext : runtime.application.PolicyExecution}
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left.execution (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right.execution (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  cases lookup : left.execution.native.pool.lookup id with
  | none =>
      have authored : ∀ message, left.execution.native.pool.lookup id = some message →
          message.sender = focal := by
        intro message impossible
        rw [lookup] at impossible
        contradiction
      exact replay.environmentInclude_focal runtime focal id authored leftSupported rightSupported
  | some message =>
      rcases message with ⟨⟨sender, nonce⟩, payload⟩
      cases payload with
      | commitment event candidate =>
          exact replay.environmentInclude_commitment runtime focal id
            ⟨(sender, nonce), .commitment event candidate⟩ event candidate lookup rfl
            leftSupported rightSupported
      | withhold event =>
          exact replay.environmentInclude_withhold runtime focal id (sender, nonce) event lookup
            leftSupported rightSupported
      | malformed raw =>
          exact replay.environmentInclude_malformed runtime focal id (sender, nonce) raw lookup
            leftSupported rightSupported
      | opening event candidate raw =>
          by_cases same : sender = focal
          · subst sender
            have authored : ∀ query,
                left.execution.native.pool.lookup id = some query → query.sender = focal := by
              intro query queryLookup
              rw [lookup] at queryLookup
              exact congrArg Message.sender (Option.some.inj queryLookup.symm)
            exact replay.environmentInclude_focal runtime focal id authored leftSupported
              rightSupported
          · obtain ⟨policy, prescribed⟩ := prescribedOthers sender same
            have leftOrigins := leftReachable.resolutionOrigins runtime inputs roster
              reactionRounds players wire order ordered sender policy prescribed
            have rightOrigins := rightReachable.resolutionOrigins runtime inputs roster
              reactionRounds players wire order ordered sender policy prescribed
            have leftBinding := leftReachable.bindingInvariant runtime inputs roster
              reactionRounds players wire order
            have rightBinding := rightReachable.bindingInvariant runtime inputs roster
              reactionRounds players wire order
            exact replay.environmentInclude_prescribedOpening runtime focal sender same id nonce
              event candidate raw leftOrigins rightOrigins leftBinding rightBinding lookup
              leftSupported rightSupported

/-- A paired sample command needs only equality of the resulting focal graph
observation. Public application metadata is then forced by the incoming replay
and the sample transition frame. -/
theorem environmentExecuteSample_of_observation
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (.executeSample event))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (.executeSample event))).support)
    (focalResult : graph.playerObserve focal leftNext.native.application.config =
      graph.playerObserve focal rightNext.native.application.config) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftNative : leftNext.native ∈
      ((runtime.application.environmentPolicyStep left
        (.application (.executeSample event))).map
          MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨leftNext, leftSupported, rfl⟩
  have rightNative : rightNext.native ∈
      ((runtime.application.environmentPolicyStep right
        (.application (.executeSample event))).map
          MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨rightNext, rightSupported, rfl⟩
  rw [runtime.application.environmentStep_native] at leftNative rightNative
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.support_map, Set.mem_image] at leftNative rightNative
  obtain ⟨leftApplication, leftApplicationMem, leftStateEq⟩ := leftNative
  obtain ⟨rightApplication, rightApplicationMem, rightStateEq⟩ := rightNative
  have leftApplicationEq : leftNext.native.application = leftApplication := by
    rw [← leftStateEq]
  have rightApplicationEq : rightNext.native.application = rightApplication := by
    rw [← rightStateEq]
  have leftTables := environmentStep_tables runtime left.native.application leftApplication
    (.executeSample event) leftApplicationMem
  have rightTables := environmentStep_tables runtime right.native.application rightApplication
    (.executeSample event) rightApplicationMem
  have leftFrame := environmentStep_executeSample_config_activated runtime
    left.native.application leftApplication event leftApplicationMem
  have rightFrame := environmentStep_executeSample_config_activated runtime
    right.native.application rightApplication event rightApplicationMem
  have postCut : leftApplication.config.cut = rightApplication.config.cut := by
    apply cut_eq_of_completionOrder_eq
    simpa only [leftApplicationEq, rightApplicationEq, playerObserve] using
      congrArg PlayerObservation.completionOrder focalResult
  have preCut : left.native.application.config.cut = right.native.application.config.cut := by
    apply cut_eq_of_completionOrder_eq
    simpa only [playerObserve] using congrArg PlayerObservation.completionOrder replay.observation
  have accepted : leftApplication.accepted = rightApplication.accepted := by
    rw [leftTables.1, rightTables.1]
    exact congrArg PublicView.accepted replay.publicView
  have clock : leftApplication.clock = rightApplication.clock := by
    rw [leftFrame.1, rightFrame.1]
    exact congrArg PublicView.clock replay.publicView
  have preClock : left.native.application.clock = right.native.application.clock :=
    congrArg PublicView.clock replay.publicView
  have preActivated : left.native.application.activatedAt =
      right.native.application.activatedAt :=
    congrArg PublicView.activatedAt replay.publicView
  have activated : leftApplication.activatedAt = rightApplication.activatedAt := by
    rcases leftFrame.2 with ⟨leftConfig, leftActivated⟩ |
      ⟨leftReady, leftAction, leftStep, leftActivated⟩
    · rcases rightFrame.2 with ⟨rightConfig, rightActivated⟩ |
        ⟨rightReady, rightAction, rightStep, rightActivated⟩
      · rw [leftActivated, rightActivated]
        exact congrArg PublicView.activatedAt replay.publicView
      · exfalso
        have completed : event ∈ rightApplication.config.cut.completed := by
          rw [right.native.application.config.step_cut event rightReady rightAction
            rightApplication.config rightStep, EventOrder.Cut.mem_complete]
          exact Or.inl rfl
        rw [← postCut, leftConfig, preCut] at completed
        exact rightReady.1 completed
    · rcases rightFrame.2 with ⟨rightConfig, rightActivated⟩ |
        ⟨rightReady, rightAction, rightStep, rightActivated⟩
      · exfalso
        have completed : event ∈ leftApplication.config.cut.completed := by
          rw [left.native.application.config.step_cut event leftReady leftAction
            leftApplication.config leftStep, EventOrder.Cut.mem_complete]
          exact Or.inl rfl
        rw [postCut, rightConfig, ← preCut] at completed
        exact leftReady.1 completed
      · rw [leftActivated, rightActivated]
        unfold State.refreshActivated
        funext query
        rw [postCut, preClock, preActivated]
  have serviceGrant : leftApplication.serviceGrant = rightApplication.serviceGrant := by
    rw [environmentStep_serviceGrant runtime left.native.application leftApplication
        (.executeSample event) leftApplicationMem,
      environmentStep_serviceGrant runtime right.native.application rightApplication
        (.executeSample event) rightApplicationMem]
    exact congrArg PublicView.serviceGrant replay.publicView
  have publicResult : leftNext.native.application.publicView =
      rightNext.native.application.publicView := by
    rw [leftApplicationEq, rightApplicationEq]
    unfold State.publicView
    congr 1
    exact publicObserve_eq_of_playerObserve_eq focal leftApplication.config
      rightApplication.config (by simpa [leftApplicationEq, rightApplicationEq] using focalResult)
  exact replay.environmentExecuteSample runtime focal event leftSupported rightSupported
    publicResult focalResult

/-- Paired sample transitions append the same addressed event to chronological
completion order (or both stutter), independently of the sampled value. -/
theorem environmentExecuteSample_completionOrder
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (.executeSample event))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (.executeSample event))).support) :
    leftNext.native.application.config.history.map Completion.event =
      rightNext.native.application.config.history.map Completion.event := by
  have leftNative : leftNext.native ∈
      ((runtime.application.environmentPolicyStep left
        (.application (.executeSample event))).map
          MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨leftNext, leftSupported, rfl⟩
  have rightNative : rightNext.native ∈
      ((runtime.application.environmentPolicyStep right
        (.application (.executeSample event))).map
          MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨rightNext, rightSupported, rfl⟩
  rw [runtime.application.environmentStep_native] at leftNative rightNative
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.support_map, Set.mem_image] at leftNative rightNative
  obtain ⟨leftApplication, leftApplicationMem, leftStateEq⟩ := leftNative
  obtain ⟨rightApplication, rightApplicationMem, rightStateEq⟩ := rightNative
  change leftApplication ∈
    (environmentStep runtime left.native.application (.executeSample event)).support
    at leftApplicationMem
  change rightApplication ∈
    (environmentStep runtime right.native.application (.executeSample event)).support
    at rightApplicationMem
  have preOrder := congrArg PlayerObservation.completionOrder replay.observation
  simp only [playerObserve] at preOrder
  have readyEq : left.native.application.config.cut = right.native.application.config.cut := by
    exact cut_eq_of_completionOrder_eq _ _ preOrder
  by_cases leftReady : left.native.application.config.cut.Ready event
  · have rightReady : right.native.application.config.cut.Ready event := by
      rw [← readyEq]
      exact leftReady
    cases view : nodeView graph event with
    | bind | resolve =>
        have nonsample : ∀ payload law outputEq codeEq,
            nodeView graph event ≠ .sample payload law outputEq codeEq := by
          intro payload law outputEq codeEq opposite
          rw [view] at opposite
          contradiction
        rw [environmentStep_executeSample_of_nonsample runtime left.native.application event
            leftReady nonsample, FinDist.mem_support_pure] at leftApplicationMem
        rw [environmentStep_executeSample_of_nonsample runtime right.native.application event
            rightReady nonsample, FinDist.mem_support_pure] at rightApplicationMem
        subst leftApplication
        subst rightApplication
        rw [← leftStateEq, ← rightStateEq]
        exact preOrder
    | sample payload law outputEq codeEq =>
        rw [environmentStep_executeSample_eq runtime left.native.application event leftReady
          payload law outputEq codeEq view, FinDist.support_map] at leftApplicationMem
        rw [environmentStep_executeSample_eq runtime right.native.application event rightReady
          payload law outputEq codeEq view, FinDist.support_map] at rightApplicationMem
        obtain ⟨leftConfig, leftConfigMem, rfl⟩ := leftApplicationMem
        obtain ⟨rightConfig, rightConfigMem, rfl⟩ := rightApplicationMem
        rw [← leftStateEq, ← rightStateEq]
        rw [left.native.application.config.step_history event leftReady _ leftConfig
            leftConfigMem,
          right.native.application.config.step_history event rightReady _ rightConfig
            rightConfigMem]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [preOrder]
  · have rightReady : ¬right.native.application.config.cut.Ready event := by
      intro ready
      apply leftReady
      rw [readyEq]
      exact ready
    rw [environmentStep_executeSample_of_not_ready runtime left.native.application event
        leftReady, FinDist.mem_support_pure] at leftApplicationMem
    rw [environmentStep_executeSample_of_not_ready runtime right.native.application event
        rightReady, FinDist.mem_support_pure] at rightApplicationMem
    subst leftApplication
    subst rightApplication
    rw [← leftStateEq, ← rightStateEq]
    exact preOrder

end NativeReplay

namespace ServiceReplay

/-- At a common epoch boundary, a fixed pure public order policy selects the
same epoch plan and preserves synchronized replay. Terminal controls stutter. -/
theorem orderStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (response : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → ServiceOrder graph)
    (fixed : order = fun history view => FinDist.pure (response history view))
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (leftPlan : left.plan = [])
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = [] := replay.plan.symm.trans leftPlan
  cases leftEpochs : left.epochs with
  | zero =>
      have rightEpochs : right.epochs = 0 := by rw [← replay.epochs, leftEpochs]
      simp only [serviceControlStep, leftPlan, leftEpochs, FinDist.mem_support_pure]
        at leftSupported
      simp only [serviceControlStep, rightPlan, rightEpochs, FinDist.mem_support_pure]
        at rightSupported
      subst leftNext
      subst rightNext
      exact replay
  | succ epochs =>
      have rightEpochs : right.epochs = epochs + 1 := by rw [← replay.epochs, leftEpochs]
      simp only [serviceControlStep, leftPlan, leftEpochs, fixed, FinDist.support_map,
        Set.mem_image] at leftSupported
      simp only [serviceControlStep, rightPlan, rightEpochs, fixed, FinDist.support_map,
        Set.mem_image] at rightSupported
      obtain ⟨leftOrder, leftOrderMem, rfl⟩ := leftSupported
      obtain ⟨rightOrder, rightOrderMem, rfl⟩ := rightSupported
      rw [FinDist.mem_support_pure] at leftOrderMem rightOrderMem
      have inputEq := replay.environmentInput
      have orderEq : response left.execution.environmentHistory
            (MessageApplication.State.environmentView runtime.application
              left.execution.native) =
          response right.execution.environmentHistory
            (MessageApplication.State.environmentView runtime.application
              right.execution.native) :=
        congrArg (fun input => response input.1 input.2) inputEq
      subst leftOrder
      subst rightOrder
      rw [orderEq]
      exact ⟨rfl, rfl, replay.native⟩

/-- Executing the common focal-player head instruction under a fixed pure
response preserves the synchronized control replay. -/
theorem focalPlayerStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (response : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixed : players focal = fun history view => FinDist.pure (response history view))
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .player focal :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .player focal :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.purePlayer_afterInvoke runtime focal players
        (runtime.application.wireEnvironment wire) response fixed leftExecutionMem
          rightExecutionMem }

/-- Executing a common pure wire-policy head instruction preserves control
replay, including arbitrary public inclusion traffic. -/
theorem wireStep (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (ordered : graph.BarrierOrdered) (focal : Player)
    (prescribedOthers : ∀ who, who ≠ focal →
      ∃ policy : graph.BehavioralPolicy who,
        players who = runtime.compilePlayerPolicy who policy)
    (response : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → WireCommand Player)
    (fixed : wire = fun history view => FinDist.pure (response history view))
    {left right leftNext rightNext : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .wire :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .wire :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftExecutionMem rightExecutionMem
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftExecutionMem
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightExecutionMem
  let leftView := MessageApplication.State.environmentView runtime.application
    left.execution.native
  let rightView := MessageApplication.State.environmentView runtime.application
    right.execution.native
  change leftCommand ∈ (runtime.application.wireEnvironment wire
    left.execution.environmentHistory leftView).support at leftChosen
  change rightCommand ∈ (runtime.application.wireEnvironment wire
    right.execution.environmentHistory rightView).support at rightChosen
  have inputEq : (left.execution.environmentHistory, leftView) =
      (right.execution.environmentHistory, rightView) := replay.environmentInput
  let chosen := response left.execution.environmentHistory leftView
  have chosenEq : chosen = response right.execution.environmentHistory rightView :=
    congrArg (fun input => response input.1 input.2) inputEq
  have leftLaw : runtime.application.wireEnvironment wire
      left.execution.environmentHistory leftView =
      FinDist.pure (chosen.toEnvironmentCommand runtime.application) := by
    simp only [MessageApplication.wireEnvironment, fixed, FinDist.map_pure]
    rfl
  have rightLaw : runtime.application.wireEnvironment wire
      right.execution.environmentHistory rightView =
      FinDist.pure (chosen.toEnvironmentCommand runtime.application) := by
    simp only [MessageApplication.wireEnvironment, fixed, FinDist.map_pure]
    rw [chosenEq]
  rw [leftLaw, FinDist.mem_support_pure] at leftChosen
  rw [rightLaw, FinDist.mem_support_pure] at rightChosen
  subst leftCommand
  subst rightCommand
  have nativeReplay : NativeReplay runtime focal leftExecution rightExecution := by
    generalize chosenEqn : chosen = wireCommand at leftStep rightStep
    cases wireCommand with
    | wait =>
        simp only [WireCommand.toEnvironmentCommand] at leftStep rightStep
        exact replay.native.environmentWait runtime focal leftStep rightStep
    | deliver observer id =>
        simp only [WireCommand.toEnvironmentCommand] at leftStep rightStep
        exact replay.native.environmentDeliver runtime focal observer id leftStep rightStep
    | «include» id =>
        simp only [WireCommand.toEnvironmentCommand] at leftStep rightStep
        exact replay.native.environmentInclude_reachable runtime inputs roster reactionRounds
          players wire order ordered focal prescribedOthers leftReachable rightReachable id
          leftStep rightStep
  exact ⟨replay.epochs, rfl, nativeReplay⟩

/-- Executing a prescribed nonfocal-player head instruction preserves the
control replay. The only endpoint-sensitive input is equality of the two
stage-two resolution packets. -/
theorem prescribedPlayerStep (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal owner : Player) (different : owner ≠ focal)
    (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {left right leftNext rightNext : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .player owner :: rest)
    (event : graph.EventId)
    (grant : left.execution.native.application.serviceGrant = some event)
    (resolutionPayloadEq : ∀ (payload : L.Ty)
      (binding : FieldRef graph.layout (.binding owner payload))
      (checks : List (GuardCheck graph.layout payload))
      (outputEq : graph.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
        (graph.nodes event) = .resolve owner payload binding checks)
      (_viewNode : nodeView graph event =
        .resolve owner payload binding checks outputEq codeEq)
      (_actor : graph.actor? event = some owner)
      (_leftReady : left.execution.native.application.config.cut.Ready event)
      (_rightReady : right.execution.native.application.config.cut.Ready event)
      (leftAction rightAction : graph.Action event),
      left.execution.native.application.remembered event = some leftAction →
      right.execution.native.application.remembered event = some rightAction →
      runtime.resolutionPayload owner event payload binding checks outputEq leftAction
          (MessageApplication.State.observe runtime.application left.execution.native owner) =
        runtime.resolutionPayload owner event payload binding checks outputEq rightAction
          (MessageApplication.State.observe runtime.application right.execution.native owner))
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .player owner :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  have leftCoherent := leftReachable.policyCoherentAll runtime inputs roster reactionRounds
    players wire order owner policy prescribed
  have rightCoherent := rightReachable.policyCoherentAll runtime inputs roster reactionRounds
    players wire order owner policy prescribed
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.prescribedPlayer_afterInvoke runtime focal owner different policy
        players (runtime.application.wireEnvironment wire) leftCoherent rightCoherent event grant
        prescribed resolutionPayloadEq leftExecutionMem rightExecutionMem }

/-- A prescribed nonfocal player waits when no service event is granted. -/
theorem prescribedPlayerStep_noGrant (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal owner : Player) (different : owner ≠ focal)
    (policy : graph.BehavioralPolicy owner)
    (prescribed : players owner = runtime.compilePlayerPolicy owner policy)
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .player owner :: rest)
    (grant : left.execution.native.application.serviceGrant = none)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .player owner :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftExecutionMem rightExecutionMem
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftExecutionMem
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightExecutionMem
  have rightGrant : right.execution.native.application.serviceGrant = none := by
    have grantEq := congrArg PublicView.serviceGrant replay.native.publicView
    change left.execution.native.application.serviceGrant =
      right.execution.native.application.serviceGrant at grantEq
    exact grantEq.symm.trans grant
  have leftViewGrant : (MessageApplication.State.observe runtime.application
      left.execution.native owner).application.publicView.serviceGrant = none := grant
  have rightViewGrant : (MessageApplication.State.observe runtime.application
      right.execution.native owner).application.publicView.serviceGrant = none := rightGrant
  rw [prescribed] at leftChosen rightChosen
  unfold compilePlayerPolicy at leftChosen rightChosen
  rw [leftViewGrant, FinDist.mem_support_pure] at leftChosen
  rw [rightViewGrant, FinDist.mem_support_pure] at rightChosen
  subst leftCommand
  subst rightCommand
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.nonfocalPlayerStep runtime focal owner different
        (.wait : NativeReplay.PrescribedCommandPair runtime .wait .wait) leftStep rightStep }

/-- Executing the common grant head instruction preserves synchronized
control replay. -/
theorem grantStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .grant event :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .grant event :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.environmentGrant runtime focal event leftExecutionMem
        rightExecutionMem }

/-- Executing the common public clock head instruction preserves synchronized
control replay. -/
theorem tickStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .tick :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .tick :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.environmentAdvanceClock runtime focal leftExecutionMem
        rightExecutionMem }

/-- Executing the common chance head instruction preserves synchronized
control replay once endpoint reconstruction has identified its public and
focal-observation results. -/
theorem sampleStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .sample event :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support)
    (focalResult : graph.playerObserve focal
        leftNext.execution.native.application.config =
      graph.playerObserve focal rightNext.execution.native.application.config) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .sample event :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.environmentExecuteSample_of_observation runtime focal event
        leftExecutionMem rightExecutionMem focalResult }

/-- Equal normalized residual endpoints determine the focal observation after
a paired sample instruction, so the actual chance step preserves replay even
when the sampled hidden values differ. -/
theorem sampleStep_of_endpoint (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (sampled target : graph.EventId)
    {left right leftNext rightNext leftEnd rightEnd : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .sample sampled :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support)
    (leftTail : ServiceControlPath runtime roster reactionRounds players wire order
      leftNext leftEnd)
    (rightTail : ServiceControlPath runtime roster reactionRounds players wire order
      rightNext rightEnd)
    (endpoints : graph.normalizeObservation target focal
        (graph.playerObserve focal leftEnd.execution.native.application.config) =
      graph.normalizeObservation target focal
        (graph.playerObserve focal rightEnd.execution.native.application.config)) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .sample sampled :: rest := by
    rw [← replay.plan]
    exact leftPlan
  have leftMember := leftSupported
  have rightMember := rightSupported
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftMember
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightMember
  obtain ⟨leftExecution, leftExecutionMem, leftNextEq⟩ := leftMember
  obtain ⟨rightExecution, rightExecutionMem, rightNextEq⟩ := rightMember
  have orderEq : leftNext.execution.native.application.config.history.map Completion.event =
      rightNext.execution.native.application.config.history.map Completion.event := by
    rw [← leftNextEq, ← rightNextEq]
    exact replay.native.environmentExecuteSample_completionOrder runtime focal sampled
      leftExecutionMem rightExecutionMem
  have focalResult := leftTail.playerObserve_eq_of_endpoint runtime roster reactionRounds players
    wire order focal target rightTail orderEq endpoints
  exact replay.sampleStep runtime roster reactionRounds players wire order focal sampled rest
    leftPlan leftSupported rightSupported focalResult

/-- Executing the common expiry head instruction preserves synchronized
control replay once the protected/local endpoint argument identifies its
public and focal-observation results. -/
theorem expireStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .expire event :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .expire event :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  exact
    { epochs := replay.epochs
      plan := rfl
      native := replay.native.environmentExpire runtime focal event leftExecutionMem
        rightExecutionMem }

/-- The reserved inclusion instruction is fully replayable from the common
public pool. Foreign prescribed openings use reachable provenance and binding
invariants; other packet forms are locally observational. -/
theorem includeLatestStep (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (ordered : graph.BarrierOrdered) (focal owner : Player)
    (prescribedOthers : ∀ who, who ≠ focal →
      ∃ policy : graph.BehavioralPolicy who,
        players who = runtime.compilePlayerPolicy who policy)
    (event : graph.EventId)
    {left right leftNext rightNext : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : ServiceReplay runtime focal left right)
    (rest : List (ServiceInstruction graph))
    (leftPlan : left.plan = .includeLatest event owner :: rest)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support) :
    ServiceReplay runtime focal leftNext rightNext := by
  have rightPlan : right.plan = .includeLatest event owner :: rest := by
    rw [← replay.plan]
    exact leftPlan
  simp only [serviceControlStep, leftPlan, FinDist.support_map, Set.mem_image] at leftSupported
  simp only [serviceControlStep, rightPlan, FinDist.support_map, Set.mem_image] at rightSupported
  obtain ⟨leftExecution, leftExecutionMem, rfl⟩ := leftSupported
  obtain ⟨rightExecution, rightExecutionMem, rfl⟩ := rightSupported
  let leftView := MessageApplication.State.environmentView runtime.application
    left.execution.native
  let rightView := MessageApplication.State.environmentView runtime.application
    right.execution.native
  have viewEq : leftView = rightView := replay.native.environmentView
  change leftExecution ∈ (runtime.application.environmentPolicyStep left.execution
    (runtime.latestEventSubmissionCommand event owner leftView)).support at leftExecutionMem
  change rightExecution ∈ (runtime.application.environmentPolicyStep right.execution
    (runtime.latestEventSubmissionCommand event owner rightView)).support at rightExecutionMem
  cases selected : latestEventSubmission? leftView.pool event owner with
  | none =>
      have command : runtime.latestEventSubmissionCommand event owner leftView = .wait := by
        simp [latestEventSubmissionCommand, selected]
      have rightCommand : runtime.latestEventSubmissionCommand event owner rightView = .wait :=
        by rw [← viewEq, command]
      rw [command] at leftExecutionMem
      rw [rightCommand] at rightExecutionMem
      exact
        { epochs := replay.epochs
          plan := rfl
          native := replay.native.environmentWait runtime focal leftExecutionMem
            rightExecutionMem }
  | some message =>
      have command : runtime.latestEventSubmissionCommand event owner leftView =
          .include message.id := by simp [latestEventSubmissionCommand, selected]
      have rightCommand : runtime.latestEventSubmissionCommand event owner rightView =
          .include message.id := by rw [← viewEq, command]
      rw [command] at leftExecutionMem
      rw [rightCommand] at rightExecutionMem
      have specification := latestEventSubmission?_spec leftView.pool event owner message selected
      obtain ⟨pending, sender, address⟩ := specification
      have authorship := leftReachable.authorship runtime inputs roster reactionRounds players
        wire order
      have lookup : left.execution.native.pool.lookup message.id = some message :=
        MessageApplication.Authorship.lookup_eq_of_mem_pending runtime.application left.execution
          authorship message pending
      rcases message with ⟨⟨senderId, nonce⟩, payload⟩
      change senderId = owner at sender
      subst senderId
      cases payload with
      | commitment addressed candidate =>
          simp only [Payload.event?] at address
          have addressedEq := Option.some.inj address
          subst addressed
          exact
            { epochs := replay.epochs
              plan := rfl
              native := replay.native.environmentInclude_commitment runtime focal
                (owner, nonce) ⟨(owner, nonce), .commitment event candidate⟩ event candidate
                lookup rfl leftExecutionMem rightExecutionMem }
      | withhold addressed =>
          simp only [Payload.event?] at address
          have addressedEq := Option.some.inj address
          subst addressed
          exact
            { epochs := replay.epochs
              plan := rfl
              native := replay.native.environmentInclude_withhold runtime focal (owner, nonce)
                (owner, nonce) event lookup leftExecutionMem rightExecutionMem }
      | malformed raw => cases address
      | opening addressed candidate raw =>
          simp only [Payload.event?] at address
          have addressedEq := Option.some.inj address
          subst addressed
          by_cases same : owner = focal
          · subst owner
            have authored : ∀ query,
                left.execution.native.pool.lookup (focal, nonce) = some query →
                query.sender = focal := by
              intro query queryLookup
              rw [lookup] at queryLookup
              exact congrArg Message.sender (Option.some.inj queryLookup.symm)
            exact
              { epochs := replay.epochs
                plan := rfl
                native := replay.native.environmentInclude_focal runtime focal (focal, nonce)
                  authored leftExecutionMem rightExecutionMem }
          · obtain ⟨policy, prescribed⟩ := prescribedOthers owner same
            have leftOrigins := leftReachable.resolutionOrigins runtime inputs roster
              reactionRounds players wire order ordered owner policy prescribed
            have rightOrigins := rightReachable.resolutionOrigins runtime inputs roster
              reactionRounds players wire order ordered owner policy prescribed
            have leftBinding := leftReachable.bindingInvariant runtime inputs roster
              reactionRounds players wire order
            have rightBinding := rightReachable.bindingInvariant runtime inputs roster
              reactionRounds players wire order
            exact
              { epochs := replay.epochs
                plan := rfl
                native := replay.native.environmentInclude_prescribedOpening runtime focal owner
                  same (owner, nonce) nonce event candidate raw leftOrigins rightOrigins
                  leftBinding rightBinding lookup leftExecutionMem rightExecutionMem }

/-- One actual paired service-control transition. Endpoint-sensitive premises
identify the prescribed resolution packet and the public chance observation;
the other branches depend only on the current replay relation. -/
theorem pairedControlStep (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (ordered : graph.BarrierOrdered) (focal : Player)
    (focalResponse : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixedFocal : players focal = fun history view =>
      FinDist.pure (focalResponse history view))
    (wireResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → WireCommand Player)
    (fixedWire : wire = fun history view => FinDist.pure (wireResponse history view))
    (orderResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → ServiceOrder graph)
    (fixedOrder : order = fun history view => FinDist.pure (orderResponse history view))
    (prescribedOthers : ∀ who, who ≠ focal →
      ∃ policy : graph.BehavioralPolicy who,
        players who = runtime.compilePlayerPolicy who policy)
    {left right leftNext rightNext : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : ServiceReplay runtime focal left right)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support)
    (resolutionPayloadEq : ∀ (owner : Player) (_different : owner ≠ focal)
      (policy : graph.BehavioralPolicy owner)
      (_prescribed : players owner = runtime.compilePlayerPolicy owner policy)
      (rest : List (ServiceInstruction graph)) (event : graph.EventId),
      left.plan = .player owner :: rest →
      left.execution.native.application.serviceGrant = some event →
      ∀ (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
        (checks : List (GuardCheck graph.layout payload))
        (outputEq : graph.outputLayout event = .publication payload)
        (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
          (graph.nodes event) = .resolve owner payload binding checks)
        (_viewNode : nodeView graph event =
          .resolve owner payload binding checks outputEq codeEq)
        (_actor : graph.actor? event = some owner)
        (_leftReady : left.execution.native.application.config.cut.Ready event)
        (_rightReady : right.execution.native.application.config.cut.Ready event)
        (leftAction rightAction : graph.Action event),
        left.execution.native.application.remembered event = some leftAction →
        right.execution.native.application.remembered event = some rightAction →
        runtime.resolutionPayload owner event payload binding checks outputEq leftAction
            (MessageApplication.State.observe runtime.application left.execution.native owner) =
          runtime.resolutionPayload owner event payload binding checks outputEq rightAction
            (MessageApplication.State.observe runtime.application right.execution.native owner))
    (sampleResult : ∀ (event : graph.EventId) (rest : List (ServiceInstruction graph)),
      left.plan = .sample event :: rest →
      graph.playerObserve focal leftNext.execution.native.application.config =
        graph.playerObserve focal rightNext.execution.native.application.config) :
    ServiceReplay runtime focal leftNext rightNext := by
  cases leftPlanEq : left.plan with
  | nil =>
      exact replay.orderStep runtime roster reactionRounds players wire order focal orderResponse
        fixedOrder leftPlanEq leftSupported rightSupported
  | cons instruction rest =>
      cases instruction with
      | player who =>
          by_cases same : who = focal
          · subst who
            exact replay.focalPlayerStep runtime roster reactionRounds players wire order focal
              focalResponse fixedFocal rest leftPlanEq leftSupported rightSupported
          · obtain ⟨policy, prescribed⟩ := prescribedOthers who same
            cases grant : left.execution.native.application.serviceGrant with
            | none =>
                exact replay.prescribedPlayerStep_noGrant runtime roster reactionRounds players
                  wire order focal who same policy prescribed rest leftPlanEq grant leftSupported
                  rightSupported
            | some event =>
                exact replay.prescribedPlayerStep runtime inputs roster reactionRounds players
                  wire order focal who same policy prescribed leftReachable rightReachable rest
                  leftPlanEq event grant
                  (resolutionPayloadEq who same policy prescribed rest event leftPlanEq grant)
                  leftSupported rightSupported
      | wire =>
          exact replay.wireStep runtime inputs roster reactionRounds players wire order ordered
            focal prescribedOthers wireResponse fixedWire leftReachable rightReachable rest
            leftPlanEq leftSupported rightSupported
      | grant event =>
          exact replay.grantStep runtime roster reactionRounds players wire order focal event rest
            leftPlanEq leftSupported rightSupported
      | includeLatest event owner =>
          exact replay.includeLatestStep runtime inputs roster reactionRounds players wire order
            ordered focal owner prescribedOthers event leftReachable rightReachable rest
            leftPlanEq leftSupported rightSupported
      | sample event =>
          have focalResult := sampleResult event rest leftPlanEq
          exact replay.sampleStep runtime roster reactionRounds players wire order focal event rest
            leftPlanEq leftSupported rightSupported focalResult
      | tick =>
          exact replay.tickStep runtime roster reactionRounds players wire order focal rest
            leftPlanEq leftSupported rightSupported
      | expire event =>
          exact replay.expireStep runtime roster reactionRounds players wire order focal event rest
            leftPlanEq leftSupported rightSupported

/-- Endpoint-aware actual paired step. Equal normalized target observations
discharge chance coupling, while completed public resolution outputs discharge
prescribed stage-two packet equality. -/
theorem pairedControlStep_of_endpoint (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (focalResponse : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixedFocal : players focal = fun history view =>
      FinDist.pure (focalResponse history view))
    (wireResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → WireCommand Player)
    (fixedWire : wire = fun history view => FinDist.pure (wireResponse history view))
    (orderResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → ServiceOrder graph)
    (fixedOrder : order = fun history view => FinDist.pure (orderResponse history view))
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (target : graph.EventId) (targetActor : graph.actor? target = some focal)
    {left right leftNext rightNext leftEnd rightEnd : ServiceControl runtime}
    (leftReachable : ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      right)
    (replay : ServiceReplay runtime focal left right)
    (leftSupported : leftNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order left).support)
    (rightSupported : rightNext ∈
      (runtime.serviceControlStep roster reactionRounds players wire order right).support)
    (leftTail : ServiceControlPath runtime roster reactionRounds players wire order
      leftNext leftEnd)
    (rightTail : ServiceControlPath runtime roster reactionRounds players wire order
      rightNext rightEnd)
    (endpoints : graph.normalizeObservation target focal
        (graph.playerObserve focal leftEnd.execution.native.application.config) =
      graph.normalizeObservation target focal
        (graph.playerObserve focal rightEnd.execution.native.application.config))
    (leftEndReady : leftEnd.execution.native.application.config.cut.Ready target)
    (rightEndReady : rightEnd.execution.native.application.config.cut.Ready target) :
    ServiceReplay runtime focal leftNext rightNext := by
  have prescribedOthers : ∀ owner, owner ≠ focal →
      ∃ policy : graph.BehavioralPolicy owner,
        players owner = runtime.compilePlayerPolicy owner policy := by
    intro owner different
    exact ⟨profile owner, opponentCompiled owner different⟩
  apply replay.pairedControlStep runtime inputs roster reactionRounds players wire order ordered
    focal focalResponse fixedFocal wireResponse fixedWire orderResponse fixedOrder
    prescribedOthers leftReachable rightReachable leftSupported rightSupported
  · intro owner different policy prescribed rest event leftPlan grant payload binding checks
      outputEq codeEq viewNode actor leftReady rightReady leftAction rightAction leftCached
      rightCached
    have completedAtEnd
        (before next endpoint : ServiceControl runtime)
        (step : next ∈
          (runtime.serviceControlStep roster reactionRounds players wire order before).support)
        (tail : ServiceControlPath runtime roster reactionRounds players wire order next endpoint)
        (ready : before.execution.native.application.config.cut.Ready event)
        (endpointReady : endpoint.execution.native.application.config.cut.Ready target) :
        event ∈ endpoint.execution.native.application.config.cut.completed := by
      by_contra unfinished
      have fullPath : ServiceControlPath runtime roster reactionRounds players wire order before
          endpoint := .cons step tail
      have completedSubset := completed_subset_of_history_prefix
        before.execution.native.application.config endpoint.execution.native.application.config
        (fullPath.history_prefix runtime roster reactionRounds players wire order)
      have eventReady : endpoint.execution.native.application.config.cut.Ready event := by
        refine ⟨unfinished, ?_⟩
        intro predecessor dependency
        exact completedSubset (ready.2 dependency)
      have isPublic : (graph.outputLayout event).IsPublic := by
        rw [outputEq]
        trivial
      have sameEvent := ordered.ready_public_unique
        endpoint.execution.native.application.config.cut isPublic eventReady endpointReady
      subst event
      rw [targetActor] at actor
      exact different (Option.some.inj actor.symm)
    have leftCompleted := completedAtEnd left leftNext leftEnd leftSupported leftTail leftReady
      leftEndReady
    have rightCompleted := completedAtEnd right rightNext rightEnd rightSupported rightTail
      rightReady rightEndReady
    let leftPath := ServiceControlPath.cons leftSupported leftTail
    let rightPath := ServiceControlPath.cons rightSupported rightTail
    exact leftPath.prescribed_resolutionPayload_eq_of_endpoint
      runtime feasible ordered inputs profile roster reactionRounds players wire order focal owner
      different opponentCompiled left right leftEnd rightEnd leftReachable rightReachable replay
      rightPath target event payload binding checks outputEq codeEq viewNode leftReady rightReady
      actor leftAction rightAction leftCached rightCached leftCompleted rightCompleted endpoints
  · intro sampled rest leftPlan
    exact (replay.sampleStep_of_endpoint runtime roster reactionRounds players wire order focal
      sampled target rest leftPlan leftSupported rightSupported leftTail rightTail
      endpoints).native.observation

end ServiceReplay

/-- Once actual paired service steps preserve `ServiceReplay`, two reachable
completions at one normalized focal observation have the same effective
dependent action.  Different prefix lengths are impossible: lockstep replay
would complete the event on the longer path before its alleged ready state. -/
theorem reachedFocalAction_eq_of_pairedStep
    (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId)
    (prefixPaired : ∀
      {left right leftNext rightNext leftEnd rightEnd : ServiceControl runtime},
      ServiceReachable runtime inputs roster reactionRounds players wire order left →
      ServiceReachable runtime inputs roster reactionRounds players wire order right →
      ServiceReplay runtime focal left right →
      leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        left).support →
      rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        right).support →
      ServiceControlPath runtime roster reactionRounds players wire order leftNext leftEnd →
      ServiceControlPath runtime roster reactionRounds players wire order rightNext rightEnd →
      graph.normalizeObservation event focal
          (graph.playerObserve focal leftEnd.execution.native.application.config) =
        graph.normalizeObservation event focal
          (graph.playerObserve focal rightEnd.execution.native.application.config) →
      leftEnd.execution.native.application.config.cut.Ready event →
      rightEnd.execution.native.application.config.cut.Ready event →
      ServiceReplay runtime focal leftNext rightNext)
    (completionPaired : ∀ {left right leftNext rightNext : ServiceControl runtime},
      ServiceReachable runtime inputs roster reactionRounds players wire order left →
      ServiceReachable runtime inputs roster reactionRounds players wire order right →
      ServiceReplay runtime focal left right →
      leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        left).support →
      rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        right).support →
      ((∃ (ready : left.execution.native.application.config.cut.Ready event)
          (action : graph.Action event),
          leftNext.execution.native.application.config ∈
            (left.execution.native.application.config.step event ready action).support) ∨
        ∃ (ready : right.execution.native.application.config.cut.Ready event)
          (action : graph.Action event),
          rightNext.execution.native.application.config ∈
            (right.execution.native.application.config.step event ready action).support) →
      ServiceReplay runtime focal leftNext rightNext)
    (observation : graph.PlayerObservation focal)
    (leftAction rightAction : graph.Action event)
    (leftReached : ReachedFocalAction runtime inputs roster reactionRounds players wire order
      focal event observation leftAction)
    (rightReached : ReachedFocalAction runtime inputs roster reactionRounds players wire order
      focal event observation rightAction) :
    leftAction = rightAction := by
  rcases leftReached with
    ⟨leftBefore, leftAfter, leftReachable, leftTransition, leftActor, leftReady,
      leftCompletion, leftObserved⟩
  rcases rightReached with
    ⟨rightBefore, rightAfter, rightReachable, rightTransition, rightActor, rightReady,
      rightCompletion, rightObserved⟩
  obtain ⟨leftInput, leftInputMem, leftPath⟩ :=
    leftReachable.exists_initial_path runtime inputs roster reactionRounds players wire order
  obtain ⟨rightInput, rightInputMem, rightPath⟩ :=
    rightReachable.exists_initial_path runtime inputs roster reactionRounds players wire order
  have endpoints : graph.normalizeObservation event focal
        (graph.playerObserve focal leftBefore.execution.native.application.config) =
      graph.normalizeObservation event focal
        (graph.playerObserve focal rightBefore.execution.native.application.config) :=
    leftObserved.trans rightObserved.symm
  have initialNative := NativeReplay.initial_of_endpoint runtime roster reactionRounds players
    wire order focal event leftInput rightInput leftBefore rightBefore leftPath rightPath endpoints
  have initial : ServiceReplay runtime focal
      { epochs := runtime.serviceEpochs
        plan := []
        execution := MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial leftInput)) }
      { epochs := runtime.serviceEpochs
        plan := []
        execution := MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial rightInput)) } :=
    ⟨rfl, rfl, initialNative⟩
  have leftInitialReachable : ServiceReachable runtime inputs roster reactionRounds players wire
      order _ := .initial leftInput leftInputMem
  have rightInitialReachable : ServiceReachable runtime inputs roster reactionRounds players wire
      order _ := .initial rightInput rightInputMem
  have compared := leftPath.compareEndpointReachable runtime inputs roster reactionRounds players
    wire order focal
    (fun leftReach rightReach replay leftStep rightStep leftTail rightTail =>
      prefixPaired (leftEnd := leftBefore) (rightEnd := rightBefore) leftReach rightReach replay
        leftStep rightStep leftTail rightTail endpoints leftReady rightReady)
    leftInitialReachable rightInitialReachable initial rightPath
  cases compared with
  | same replay leftReach rightReach =>
      have afterReplay := completionPaired leftReach rightReach replay leftTransition
        rightTransition (Or.inl ⟨leftReady, leftAction, leftCompletion⟩)
      exact replay.native.completedFocalAction_eq runtime focal afterReplay.native event leftActor
        leftReady rightReady leftAction rightAction leftCompletion rightCompletion
  | leftShort rightAt rightNext replay leftReach rightReach rightStep rightTail =>
      have afterReplay := completionPaired leftReach rightReach replay leftTransition rightStep
        (Or.inl ⟨leftReady, leftAction, leftCompletion⟩)
      have cutEq : leftAfter.execution.native.application.config.cut =
          rightNext.execution.native.application.config.cut := by
        apply cut_eq_of_completionOrder_eq
        simpa only [playerObserve] using
          congrArg PlayerObservation.completionOrder
            afterReplay.native.observation
      have rightNextCompleted :
          event ∈ rightNext.execution.native.application.config.cut.completed := by
        rw [← cutEq, leftBefore.execution.native.application.config.step_cut event leftReady
          leftAction leftAfter.execution.native.application.config leftCompletion,
          EventOrder.Cut.mem_complete]
        exact Or.inl rfl
      have persists := completed_subset_of_history_prefix
        rightNext.execution.native.application.config
        rightBefore.execution.native.application.config
        (rightTail.history_prefix runtime roster reactionRounds players wire order)
        rightNextCompleted
      exact False.elim (rightReady.1 persists)
  | rightShort leftAt leftNext replay leftReach rightReach leftStep leftTail =>
      have afterReplay := completionPaired leftReach rightReach replay leftStep rightTransition
        (Or.inr ⟨rightReady, rightAction, rightCompletion⟩)
      have cutEq : leftNext.execution.native.application.config.cut =
          rightAfter.execution.native.application.config.cut := by
        apply cut_eq_of_completionOrder_eq
        simpa only [playerObserve] using
          congrArg PlayerObservation.completionOrder
            afterReplay.native.observation
      have leftNextCompleted :
          event ∈ leftNext.execution.native.application.config.cut.completed := by
        rw [cutEq, rightBefore.execution.native.application.config.step_cut event rightReady
          rightAction rightAfter.execution.native.application.config rightCompletion,
          EventOrder.Cut.mem_complete]
        exact Or.inl rfl
      have persists := completed_subset_of_history_prefix
        leftNext.execution.native.application.config
        leftBefore.execution.native.application.config
        (leftTail.history_prefix runtime roster reactionRounds players wire order)
        leftNextCompleted
      exact False.elim (leftReady.1 persists)

end Vegas.EventGraphRuntime
