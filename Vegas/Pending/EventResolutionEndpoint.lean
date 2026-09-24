/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventDeviationEnvironment
import Vegas.Pending.EventDeviationLaw
import Vegas.Pending.EventOpeningObservation
import Vegas.Pending.EventPrescribedReachability
import Vegas.Pending.EventReplayEnvironment
import Vegas.Pending.EventServiceReachability
import Vegas.Pending.EventStore
import Vegas.EventGraph.ResolutionProvenance

/-! # Endpoint determination of prescribed resolution actions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- If one environment policy command completes a ready prescribed resolution,
the effective graph action is its immutable cached action. -/
theorem environmentPolicyStep_prescribed_resolution_completion
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (focal owner : Player) (other : owner ≠ focal)
    (execution after : runtime.application.PolicyExecution)
    (assumptions : DeviationEnvironmentState runtime execution focal)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (cached : execution.native.application.remembered event = some action)
    (command : runtime.application.EnvironmentPolicyCommand)
    (supported : after ∈
      (runtime.application.environmentPolicyStep execution command).support)
    (completed : event ∈ after.native.application.config.cut.completed) :
    after.native.application.config ∈
      (execution.native.application.config.step event ready action).support := by
  have isPublic : (graph.outputLayout event).IsPublic := by
    rw [outputEq]
    trivial
  have nativeMem : after.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      have same := congrArg
        (fun state : runtime.application.State => state.application.config) nativeMem
      exact (ready.1 (same ▸ completed)).elim
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup] at nativeMem
          have same := congrArg
            (fun state : runtime.application.State => state.application.config) nativeMem
          exact (ready.1 (same ▸ completed)).elim
      | some message =>
          cases acceptedEq : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message lookup
                acceptedEq] at nativeMem
              have same := congrArg
                (fun state : runtime.application.State => state.application.config) nativeMem
              exact (ready.1 (same ▸ completed)).elim
          | some next =>
              rw [runtime.application.includePending_accept execution.native id message next
                lookup acceptedEq] at nativeMem
              have afterApplication : after.native.application = next := congrArg
                (fun state : runtime.application.State => state.application) nativeMem
              obtain ⟨actual, addressed, actualReady, actualAction, actualMember⟩ :=
                runtime.handle_config_mem_step execution.native.application next message acceptedEq
              have actualEq : actual = event :=
                ordered.ready_public_unique execution.native.application.config.cut isPublic ready
                  actualReady
              subst actual
              obtain ⟨authenticated, authenticatedAddress, authenticatedActor⟩ :=
                handle_event_actor runtime execution.native.application next message acceptedEq
              have authenticatedEq : authenticated = event := Option.some.inj
                (authenticatedAddress.symm.trans addressed)
              subst authenticated
              have sender : message.sender = owner := by
                rw [actor] at authenticatedActor
                exact Option.some.inj authenticatedActor.symm
              have timely := runtime.handle_withinDeadline execution.native.application next
                message event addressed acceptedEq
              obtain ⟨saved, savedCache, savedMember, _, _⟩ :=
                runtime.handle_prescribed_owner_cached_action execution owner assumptions.authorship
                  (assumptions.coherent owner other)
                  (assumptions.bindingCoherent owner other)
                  (assumptions.resources owner other)
                  (assumptions.bindingSubmissions owner other)
                  (assumptions.resolutionOrigins owner other) assumptions.bindingInvariant event
                  ready timely actor message (List.mem_of_find?_eq_some lookup) sender addressed
                  next acceptedEq
              have savedEq : saved = action := Option.some.inj (savedCache.symm.trans cached)
              subst saved
              rw [afterApplication]
              exact savedMember
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at nativeMem
      obtain ⟨next, nextMem, nativeEq⟩ := nativeMem
      have afterApplication : after.native.application = next := congrArg
        (fun state : runtime.application.State => state.application) nativeEq.symm
      change next ∈ (environmentStep runtime execution.native.application
        applicationCommand).support at nextMem
      cases applicationCommand with
      | grant query | advanceClock =>
          simp only [environmentStep, FinDist.mem_support_pure] at nextMem
          rw [afterApplication, nextMem] at completed
          exact (ready.1 completed).elim
      | executeSample query =>
          obtain ⟨_, stutter | stepped⟩ :=
            runtime.environmentStep_executeSample_config_activated
              execution.native.application next query nextMem
          · rw [afterApplication, stutter.1] at completed
            exact (ready.1 completed).elim
          · obtain ⟨queryReady, queryAction, queryStep, _⟩ := stepped
            have same : query = event := ordered.ready_public_unique
              execution.native.application.config.cut isPublic ready queryReady
            subst query
            rw [runtime.environmentStep_executeSample_of_nonsample
              execution.native.application event ready (by
                intro samplePayload law sampleOutput sampleCode sampleView
                rw [viewNode] at sampleView
                contradiction), FinDist.mem_support_pure] at nextMem
            rw [afterApplication, nextMem] at completed
            exact (ready.1 completed).elim
      | expire query =>
          obtain stutter | ⟨queryReady, queryAction, queryStep⟩ :=
            runtime.environmentStep_expire_config_eq_or_mem_step
              execution.native.application next query nextMem
          · rw [afterApplication, stutter] at completed
            exact (ready.1 completed).elim
          · have same : query = event := ordered.ready_public_unique
              execution.native.application.config.cut isPublic ready queryReady
            subst query
            rw [runtime.environmentStep_expire_eq_of_age execution.native.application event
              (feasible event) (assumptions.activationAge owner other event actor),
              FinDist.mem_support_pure] at nextMem
            rw [afterApplication, nextMem] at completed
            exact (ready.1 completed).elim

/-- Any actual control transition which first completes the ready prescribed
resolution executes its cached action. Order choices and player-only commands
cannot be that transition. -/
theorem serviceControlStep_prescribed_resolution_completion
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal owner : Player) (other : owner ≠ focal)
    (before after : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
    (assumptions : DeviationEnvironmentState runtime before.execution focal)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (ready : before.execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (cached : before.execution.native.application.remembered event = some action)
    (supported : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support)
    (completed : event ∈ after.execution.native.application.config.cut.completed) :
    after.execution.native.application.config ∈
      (before.execution.native.application.config.step event ready action).support := by
  rcases runtime.serviceControlStep_cases roster reactionRounds players wire order before after
      supported with terminal | selected | executed
  · obtain ⟨_, _, rfl⟩ := terminal
    exact (ready.1 completed).elim
  · obtain ⟨_, _, _, _, _, rfl⟩ := selected
    exact (ready.1 completed).elim
  · obtain ⟨instruction, rest, plan, _, _, step⟩ := executed
    cases instruction with
    | player who =>
        simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
          Set.mem_iUnion] at step
        obtain ⟨command, _, playerStep⟩ := step
        have nativeMem : after.execution.native ∈
            ((runtime.application.playerStep who before.execution command).map
              MessageInterface.PolicyExecution.native).support := by
          rw [FinDist.support_map]
          exact ⟨after.execution, playerStep, rfl⟩
        rw [runtime.application.playerStep_native] at nativeMem
        cases command with
        | privateCommand privateCommand =>
            simp only [MessageApplication.PlayerCommand.toAction,
              MessageApplication.step, FinDist.mem_support_pure] at nativeMem
            have application := congrArg
              (fun state : runtime.application.State => state.application) nativeMem
            have config : after.execution.native.application.config =
                before.execution.native.application.config := by
              rw [application]
              exact (privateStep_facts before.execution.native.application who privateCommand).1
            rw [config] at completed
            exact (ready.1 completed).elim
        | submit packet | replay id | wait =>
            simp only [MessageApplication.PlayerCommand.toAction,
              MessageApplication.step, FinDist.mem_support_pure] at nativeMem
            have config := congrArg
              (fun state : runtime.application.State => state.application.config) nativeMem
            rw [config] at completed
            exact (ready.1 completed).elim
    | wire =>
        simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
          Set.mem_iUnion] at step
        obtain ⟨command, _, environmentStep⟩ := step
        exact runtime.environmentPolicyStep_prescribed_resolution_completion feasible ordered
          focal owner other before.execution after.execution assumptions event payload binding
          checks outputEq codeEq viewNode ready actor action cached command environmentStep
          completed
    | grant query =>
        exact runtime.environmentPolicyStep_prescribed_resolution_completion feasible ordered
          focal owner other before.execution after.execution assumptions event payload binding
          checks outputEq codeEq viewNode ready actor action cached (.application (.grant query))
          step completed
    | includeLatest query who =>
        exact runtime.environmentPolicyStep_prescribed_resolution_completion feasible ordered
          focal owner other before.execution after.execution assumptions event payload binding
          checks outputEq codeEq viewNode ready actor action cached
          (runtime.latestEventSubmissionCommand query who
            (MessageApplication.State.environmentView runtime.application
              before.execution.native)) step completed
    | sample query =>
        exact runtime.environmentPolicyStep_prescribed_resolution_completion feasible ordered
          focal owner other before.execution after.execution assumptions event payload binding
          checks outputEq codeEq viewNode ready actor action cached
          (.application (.executeSample query)) step completed
    | tick =>
        exact runtime.environmentPolicyStep_prescribed_resolution_completion feasible ordered
          focal owner other before.execution after.execution assumptions event payload binding
          checks outputEq codeEq viewNode ready actor action cached (.application .advanceClock)
          step completed
    | expire query =>
        exact runtime.environmentPolicyStep_prescribed_resolution_completion feasible ordered
          focal owner other before.execution after.execution assumptions event payload binding
          checks outputEq codeEq viewNode ready actor action cached (.application (.expire query))
          step completed

/-- The deterministic resolution value visible at any later endpoint is
already determined at the ready prescribed resolution site.  The only timing
input is the pointwise one-block bound for prescribed opponents along this
actual path; all authentication, coherence, provenance, and store facts are
obtained from reachability. -/
theorem ServiceControlPath.prescribed_resolution_output
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal owner : Player) (other : owner ≠ focal)
    (opponentCompiled : ∀ prescribed, prescribed ≠ focal →
      players prescribed = runtime.compilePlayerPolicy prescribed (profile prescribed))
    (before endpoint : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
    (path : ServiceControlPath runtime roster reactionRounds players wire order before endpoint)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (ready : before.execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (cached : before.execution.native.application.remembered event = some action)
    (completed : event ∈ endpoint.execution.native.application.config.cut.completed) :
    EventCode.resolveOutput? binding checks
        (cast (congrArg EventField.Action outputEq) action)
        before.execution.native.application.config.store =
      cast (congrArg Option (congrArg EventField.Value outputEq))
        (endpoint.execution.native.application.config.outputs event) := by
  induction path with
  | nil => exact (ready.1 completed).elim
  | @cons before middle endpoint step tail ih =>
      have middleReachable :
          ServiceReachable runtime inputs roster reactionRounds players wire order middle :=
        .step reachable step
      by_cases middleCompleted :
          event ∈ middle.execution.native.application.config.cut.completed
      · have assumptions := ServiceReachable.deviationEnvironmentState runtime ordered inputs
          profile roster reactionRounds players wire order focal before reachable opponentCompiled
          (fun prescribed different =>
            ServiceReachable.ownerActivationAgeOne runtime inputs ordered feasible prescribed
              (profile prescribed) roster reactionRounds players
              (opponentCompiled prescribed different) wire order before reachable)
        have firstStep := runtime.serviceControlStep_prescribed_resolution_completion feasible
          ordered inputs roster reactionRounds players wire order focal owner other before middle
          reachable assumptions event payload binding checks outputEq codeEq viewNode ready actor
          action cached step middleCompleted
        have firstOutput := Config.resolution_step_output event owner payload binding checks
          outputEq
          codeEq before.execution.native.application.config
          middle.execution.native.application.config ready action firstStep
        have present :
            (middle.execution.native.application.config.outputs event).isSome = true := by
          rw [middle.execution.native.application.config.output_available]
          exact middleCompleted
        cases outputAtMiddle : middle.execution.native.application.config.outputs event with
        | none => simp [outputAtMiddle] at present
        | some value =>
            have endpointStored := tail.store_of_some runtime roster reactionRounds players wire
              order (.inr event) value (by simpa only [Config.store_output] using outputAtMiddle)
            have endpointOutput :
                endpoint.execution.native.application.config.outputs event = some value := by
              simpa only [Config.store_output] using endpointStored
            have outputsEqual :
                middle.execution.native.application.config.outputs event =
                  endpoint.execution.native.application.config.outputs event :=
              outputAtMiddle.trans endpointOutput.symm
            exact firstOutput.trans (congrArg
              (fun output => cast
                (congrArg Option (congrArg EventField.Value outputEq)) output)
              outputsEqual)
      · obtain ⟨actions, _, nativeStep⟩ := runtime.serviceControlStep_native_support
          roster reactionRounds players wire order before middle step
        have isPublic : (graph.outputLayout event).IsPublic := by
          rw [outputEq]
          trivial
        have frame := runtime.applicationRun_ready_public_frame ordered
          before.execution.native middle.execution.native event isPublic ready middleCompleted
          actions nativeStep
        have middleReady :
            middle.execution.native.application.config.cut.Ready event := by
          simpa only [frame.1] using ready
        have middleCached :
            middle.execution.native.application.remembered event = some action :=
          frame.2.2 action cached
        have tailResult := ih middleReachable middleReady middleCached completed
        simpa only [frame.1] using tailResult

/-- Two ready prescribed resolution sites emit the same packet when their
actual suffixes complete the event into endpoint observations with the same
public store.  The actions themselves need not be equal: a private withhold
and a guard-rejected disclosure are correctly identified by their common
effective result. -/
theorem ServiceControlPath.prescribed_resolutionPayload_eq_of_endpoint
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal owner : Player) (other : owner ≠ focal)
    (opponentCompiled : ∀ prescribed, prescribed ≠ focal →
      players prescribed = runtime.compilePlayerPolicy prescribed (profile prescribed))
    (left right leftEnd rightEnd : ServiceControl runtime)
    (leftReachable :
      ServiceReachable runtime inputs roster reactionRounds players wire order left)
    (rightReachable :
      ServiceReachable runtime inputs roster reactionRounds players wire order right)
    (replay : ServiceReplay runtime focal left right)
    (leftPath : ServiceControlPath runtime roster reactionRounds players wire order left leftEnd)
    (rightPath :
      ServiceControlPath runtime roster reactionRounds players wire order right rightEnd)
    (target event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (leftReady : left.execution.native.application.config.cut.Ready event)
    (rightReady : right.execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (leftAction rightAction : graph.Action event)
    (leftCached : left.execution.native.application.remembered event = some leftAction)
    (rightCached : right.execution.native.application.remembered event = some rightAction)
    (leftCompleted : event ∈ leftEnd.execution.native.application.config.cut.completed)
    (rightCompleted : event ∈ rightEnd.execution.native.application.config.cut.completed)
    (endpoints : graph.normalizeObservation target focal
        (graph.playerObserve focal leftEnd.execution.native.application.config) =
      graph.normalizeObservation target focal
        (graph.playerObserve focal rightEnd.execution.native.application.config)) :
    runtime.resolutionPayload owner event payload binding checks outputEq leftAction
        (MessageApplication.State.observe runtime.application left.execution.native owner) =
      runtime.resolutionPayload owner event payload binding checks outputEq rightAction
        (MessageApplication.State.observe runtime.application right.execution.native owner) := by
  have leftResult := leftPath.prescribed_resolution_output runtime feasible ordered inputs profile
    roster reactionRounds players wire order focal owner other opponentCompiled left
    leftEnd leftReachable event payload binding checks outputEq codeEq viewNode leftReady actor
    leftAction leftCached leftCompleted
  have rightResult := rightPath.prescribed_resolution_output runtime feasible ordered inputs profile
    roster reactionRounds players wire order focal owner other opponentCompiled right
    rightEnd rightReachable event payload binding checks outputEq codeEq viewNode rightReady actor
    rightAction rightCached rightCompleted
  have endpointStores :
      graph.playerStore focal leftEnd.execution.native.application.config.store =
        graph.playerStore focal rightEnd.execution.native.application.config.store := by
    simpa only [normalizeObservation_store, playerObserve] using
      congrArg PlayerObservation.store endpoints
  have visible : (graph.outputLayout event).VisibleTo focal := by
    rw [outputEq]
    trivial
  have endpointOutputs :
      leftEnd.execution.native.application.config.outputs event =
        rightEnd.execution.native.application.config.outputs event := by
    have atEvent := congrFun endpointStores (.inr event)
    have fieldVisible : graph.fieldVisibleTo focal (.inr event) := by
      change (graph.outputLayout event).VisibleTo focal
      exact visible
    rw [graph.playerStore_of_visible focal _ _ fieldVisible,
      graph.playerStore_of_visible focal _ _ fieldVisible] at atEvent
    simpa only [Config.store_output] using atEvent
  have effectiveFull :
      EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) leftAction)
          left.execution.native.application.config.store =
        EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) rightAction)
          right.execution.native.application.config.store := by
    exact leftResult.trans ((congrArg
      (fun output => cast (congrArg Option (congrArg EventField.Value outputEq)) output)
      endpointOutputs).trans rightResult.symm)
  let leftView := MessageApplication.State.observe runtime.application
    left.execution.native owner
  let rightView := MessageApplication.State.observe runtime.application
    right.execution.native owner
  have accepted : leftView.application.publicView.accepted binding.field =
      rightView.application.publicView.accepted binding.field := by
    change left.execution.native.application.accepted binding.field =
      right.execution.native.application.accepted binding.field
    exact congrFun (congrArg PublicView.accepted replay.native.publicView) binding.field
  have effective :
      EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) leftAction)
          leftView.application.observation.store =
        EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) rightAction)
          rightView.application.observation.store := by
    change EventCode.resolveOutput? binding checks
        (cast (congrArg EventField.Action outputEq) leftAction)
          (graph.playerStore owner left.execution.native.application.config.store) =
      EventCode.resolveOutput? binding checks
        (cast (congrArg EventField.Action outputEq) rightAction)
          (graph.playerStore owner right.execution.native.application.config.store)
    rw [EventCode.resolveOutput?_playerStore, EventCode.resolveOutput?_playerStore]
    exact effectiveFull
  exact runtime.resolutionPayload_eq_of_effectiveResult_eq owner event payload binding checks
    outputEq leftAction rightAction leftView rightView accepted effective

end Vegas.EventGraphRuntime
