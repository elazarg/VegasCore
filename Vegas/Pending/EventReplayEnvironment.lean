/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplay
import Vegas.Pending.EventHandleObservation
import Vegas.Pending.EventPrescribedReplay
import Vegas.Pending.EventServiceProtocol
import Vegas.Pending.EventDeviationAction
import Vegas.Pending.EventStore
import Interaction.MessageApplicationLaws

/-! # Environment transitions in native event replay -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace NativeReplay

private theorem afterEnvironmentStep
    (runtime : EventGraphRuntime graph) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (command : runtime.application.EnvironmentPolicyCommand)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right command).support)
    (applicationView : leftNext.native.application.playerView focal =
      rightNext.native.application.playerView focal)
    (pool : leftNext.native.pool = rightNext.native.pool)
    (receipts : leftNext.native.receipts = rightNext.native.receipts) :
    NativeReplay runtime focal leftNext rightNext := by
  have principalLeft := runtime.application.environmentStep_principalHistory left command
    leftNext leftSupported
  have principalRight := runtime.application.environmentStep_principalHistory right command
    rightNext rightSupported
  have focalHistory : leftNext.principalHistory focal = rightNext.principalHistory focal :=
    by rw [principalLeft, principalRight, replay.focalHistory]
  have oldEnvironment := replay.environmentView
  have environmentHistory : leftNext.environmentHistory = rightNext.environmentHistory := by
    have leftStep := leftSupported
    have rightStep := rightSupported
    simp only [MessageApplication.environmentPolicyStep, FinDist.support_bind,
      Set.mem_iUnion, FinDist.mem_support_pure] at leftStep rightStep
    obtain ⟨leftAdvanced, _, leftStep⟩ := leftStep
    obtain ⟨rightAdvanced, _, rightStep⟩ := rightStep
    subst leftNext
    subst rightNext
    simp only
    rw [replay.environmentHistory, oldEnvironment]
  have publicView := congrArg PlayerView.publicView applicationView
  have observation : graph.playerObserve focal leftNext.native.application.config =
      graph.playerObserve focal rightNext.native.application.config := by
    have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) applicationView
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed
  exact
    { publicView
      observation
      remembered := congrArg PlayerView.remembered applicationView
      candidates := congrArg PlayerView.candidates applicationView
      pool
      receipts
      focalHistory
      environmentHistory
      stagingCount_other := fun owner different event => by
        rw [principalLeft, principalRight]
        exact replay.stagingCount_other owner different event
      submittedAt_other := fun owner different event => by
        rw [principalLeft, principalRight]
        exact replay.submittedAt_other owner different event }

/-- Recording an environment wait preserves native replay. -/
theorem environmentWait
    (runtime : EventGraphRuntime graph) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left .wait).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right .wait).support) :
    NativeReplay runtime focal leftNext rightNext := by
  rw [runtime.application.environmentStep_wait, FinDist.mem_support_pure] at leftSupported
  rw [runtime.application.environmentStep_wait, FinDist.mem_support_pure] at rightSupported
  subst leftNext
  subst rightNext
  apply afterEnvironmentStep runtime focal replay .wait
  · simp [runtime.application.environmentStep_wait]
  · simp [runtime.application.environmentStep_wait]
  · exact replay.applicationPlayerView
  · exact replay.pool
  · exact replay.receipts

/-- Delivering the same published packet to the same observer preserves
native replay.  Delivery changes only the common transport pool. -/
theorem environmentDeliver
    (runtime : EventGraphRuntime graph) (focal observer : Player)
    (id : MessageId Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.deliver observer id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.deliver observer id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftMem := leftSupported
  have rightMem := rightSupported
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at leftMem rightMem
  subst leftNext
  subst rightNext
  apply afterEnvironmentStep runtime focal replay (.deliver observer id)
  · exact leftSupported
  · exact rightSupported
  · exact replay.applicationPlayerView
  · simp only
    rw [replay.pool]
  · exact replay.receipts

/-- Granting the same public service cursor preserves native replay. -/
theorem environmentGrant
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (.grant event))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (.grant event))).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftMem := leftSupported
  have rightMem := rightSupported
  simp only [application, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, environmentStep, FinDist.map_pure, FinDist.pure_bind,
    FinDist.mem_support_pure] at leftMem rightMem
  subst leftNext
  subst rightNext
  have applicationView :
      ({ left.native.application with serviceGrant := some event }).playerView focal =
        ({ right.native.application with serviceGrant := some event }).playerView focal := by
    unfold State.playerView
    congr 1
    · change { left.native.application.publicView with serviceGrant := some event } =
        { right.native.application.publicView with serviceGrant := some event }
      rw [replay.publicView]
    · exact replay.observation
    · exact replay.remembered
    · exact replay.candidates
  apply afterEnvironmentStep runtime focal replay (.application (.grant event))
  · exact leftSupported
  · exact rightSupported
  · exact applicationView
  · exact replay.pool
  · exact replay.receipts

/-- Advancing the common public clock preserves native replay. -/
theorem environmentAdvanceClock
    (runtime : EventGraphRuntime graph) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application .advanceClock)).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application .advanceClock)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftMem := leftSupported
  have rightMem := rightSupported
  simp only [application, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, environmentStep, FinDist.map_pure, FinDist.pure_bind,
    FinDist.mem_support_pure] at leftMem rightMem
  subst leftNext
  subst rightNext
  have applicationView :
      ({ left.native.application with clock := left.native.application.clock + 1 }).playerView
          focal =
        ({ right.native.application with clock := right.native.application.clock + 1 }).playerView
          focal := by
    have clockEq : left.native.application.clock = right.native.application.clock :=
      congrArg PublicView.clock replay.publicView
    unfold State.playerView
    congr 1
    · change { left.native.application.publicView with
          clock := left.native.application.clock + 1 } =
        { right.native.application.publicView with
          clock := right.native.application.clock + 1 }
      rw [replay.publicView, clockEq]
    · exact replay.observation
    · exact replay.remembered
    · exact replay.candidates
  apply afterEnvironmentStep runtime focal replay (.application .advanceClock)
  · exact leftSupported
  · exact rightSupported
  · exact applicationView
  · exact replay.pool
  · exact replay.receipts

/-- Paired execution of the same sample command preserves replay when the
coupled draws produce the same public result and focal graph observation.
Candidate tables and private caches are not assumptions: the actual supported
environment transitions preserve them. -/
theorem environmentExecuteSample
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (.executeSample event))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (.executeSample event))).support)
    (publicResult : leftNext.native.application.publicView =
      rightNext.native.application.publicView)
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
  have leftRemembered := environmentStep_remembered runtime left.native.application
    leftApplication (.executeSample event) leftApplicationMem
  have rightRemembered := environmentStep_remembered runtime right.native.application
    rightApplication (.executeSample event) rightApplicationMem
  have remembered : (fun query => if graph.actor? query = some focal then
      leftNext.native.application.remembered query else none) =
    fun query => if graph.actor? query = some focal then
      rightNext.native.application.remembered query else none := by
    rw [leftApplicationEq, rightApplicationEq, leftRemembered, rightRemembered]
    exact replay.remembered
  have candidates : (fun slot =>
      leftNext.native.application.candidates.lookup (focal, slot)) =
    fun slot => rightNext.native.application.candidates.lookup (focal, slot) := by
    rw [leftApplicationEq, rightApplicationEq, leftTables.2, rightTables.2]
    exact replay.candidates
  have applicationView : leftNext.native.application.playerView focal =
      rightNext.native.application.playerView focal := by
    unfold State.playerView
    congr 1
  have pool : leftNext.native.pool = rightNext.native.pool := by
    rw [← leftStateEq, ← rightStateEq]
    exact replay.pool
  have receipts : leftNext.native.receipts = rightNext.native.receipts := by
    rw [← leftStateEq, ← rightStateEq]
    exact replay.receipts
  exact afterEnvironmentStep runtime focal replay
    (.application (.executeSample event)) leftSupported rightSupported applicationView
    pool receipts

/-- Paired expiry preserves replay once its deterministic completion has the
same public result and focal graph observation.  This is the narrow interface
needed by endpoint reconstruction or a protected foreign-timeout proof; all
transport, tables, caches, receipts, and policy histories are derived here. -/
theorem environmentExpire_of_result
    (runtime : EventGraphRuntime graph) (focal : Player) (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (.expire event))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (.expire event))).support)
    (publicResult : leftNext.native.application.publicView =
      rightNext.native.application.publicView)
    (focalResult : graph.playerObserve focal leftNext.native.application.config =
      graph.playerObserve focal rightNext.native.application.config) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftNative : leftNext.native ∈
      ((runtime.application.environmentPolicyStep left
        (.application (.expire event))).map
          MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨leftNext, leftSupported, rfl⟩
  have rightNative : rightNext.native ∈
      ((runtime.application.environmentPolicyStep right
        (.application (.expire event))).map
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
    (.expire event) leftApplicationMem
  have rightTables := environmentStep_tables runtime right.native.application rightApplication
    (.expire event) rightApplicationMem
  have leftRemembered := environmentStep_remembered runtime left.native.application
    leftApplication (.expire event) leftApplicationMem
  have rightRemembered := environmentStep_remembered runtime right.native.application
    rightApplication (.expire event) rightApplicationMem
  have remembered : (fun query => if graph.actor? query = some focal then
      leftNext.native.application.remembered query else none) =
    fun query => if graph.actor? query = some focal then
      rightNext.native.application.remembered query else none := by
    rw [leftApplicationEq, rightApplicationEq, leftRemembered, rightRemembered]
    exact replay.remembered
  have candidates : (fun slot =>
      leftNext.native.application.candidates.lookup (focal, slot)) =
    fun slot => rightNext.native.application.candidates.lookup (focal, slot) := by
    rw [leftApplicationEq, rightApplicationEq, leftTables.2, rightTables.2]
    exact replay.candidates
  have applicationView : leftNext.native.application.playerView focal =
      rightNext.native.application.playerView focal := by
    unfold State.playerView
    congr 1
  have pool : leftNext.native.pool = rightNext.native.pool := by
    rw [← leftStateEq, ← rightStateEq]
    exact replay.pool
  have receipts : leftNext.native.receipts = rightNext.native.receipts := by
    rw [← leftStateEq, ← rightStateEq]
    exact replay.receipts
  exact afterEnvironmentStep runtime focal replay
    (.application (.expire event)) leftSupported rightSupported applicationView pool receipts

private theorem environmentInclude_of_present_handleView
    (runtime : EventGraphRuntime graph) (focal : Player) (id : MessageId Player)
    (message : Message Player (Payload graph))
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (lookup : left.native.pool.lookup id = some message)
    (handled : Option.map (fun state => state.playerView focal)
        (runtime.handle left.native.application message) =
      Option.map (fun state => state.playerView focal)
        (runtime.handle right.native.application message))
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftMem := leftSupported
  have rightMem := rightSupported
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at leftMem rightMem
  subst leftNext
  subst rightNext
  have rightLookup : right.native.pool.lookup id = some message := by
    rw [← replay.pool]
    exact lookup
  cases leftHandle : runtime.handle left.native.application message with
  | none =>
      have rightHandle : runtime.handle right.native.application message = none := by
        simpa [leftHandle] using handled
      rw [runtime.application.includePending_reject left.native id message lookup leftHandle,
        runtime.application.includePending_reject right.native id message rightLookup rightHandle]
      apply afterEnvironmentStep runtime focal replay (.include id)
      · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          runtime.application.includePending_reject left.native id message lookup leftHandle]
      · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          runtime.application.includePending_reject right.native id message rightLookup rightHandle]
      · exact replay.applicationPlayerView
      · simp only
        rw [replay.pool]
      · simp only
        rw [replay.receipts]
  | some leftApplication =>
      cases rightHandle : runtime.handle right.native.application message with
      | none => simp [leftHandle, rightHandle] at handled
      | some rightApplication =>
          have applicationView : leftApplication.playerView focal =
              rightApplication.playerView focal := by
            simpa [leftHandle, rightHandle] using handled
          rw [runtime.application.includePending_accept left.native id message
                leftApplication lookup leftHandle,
            runtime.application.includePending_accept right.native id message
                rightApplication rightLookup rightHandle]
          apply afterEnvironmentStep runtime focal replay (.include id)
          · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
              MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
              runtime.application.includePending_accept left.native id message
                leftApplication lookup leftHandle]
          · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
              MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
              runtime.application.includePending_accept right.native id message
                rightApplication rightLookup rightHandle]
          · exact applicationView
          · simp only
            rw [replay.pool]
          · simp only
            rw [replay.receipts]

/-- Including a focal-authored packet preserves native replay.  The theorem
covers missing packets and both handler rejection and acceptance; in the last
case the focal handler observation theorem supplies the resulting view. -/
theorem environmentInclude_focal
    (runtime : EventGraphRuntime graph) (focal : Player) (id : MessageId Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (authored : ∀ message, left.native.pool.lookup id = some message →
      message.sender = focal)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftMem := leftSupported
  have rightMem := rightSupported
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at leftMem rightMem
  subst leftNext
  subst rightNext
  have lookupEq : left.native.pool.lookup id = right.native.pool.lookup id := by
    rw [replay.pool]
  cases lookup : left.native.pool.lookup id with
  | none =>
      have rightLookup : right.native.pool.lookup id = none := lookupEq.symm.trans lookup
      rw [runtime.application.includePending_missing left.native id lookup,
        runtime.application.includePending_missing right.native id rightLookup]
      apply afterEnvironmentStep runtime focal replay (.include id)
      · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          runtime.application.includePending_missing left.native id lookup]
      · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          runtime.application.includePending_missing right.native id rightLookup]
      · exact replay.applicationPlayerView
      · exact replay.pool
      · exact replay.receipts
  | some message =>
      have rightLookup : right.native.pool.lookup id = some message := lookupEq.symm.trans lookup
      have sender := authored message lookup
      have handled := handle_playerView_congr_of_sender runtime
        left.native.application right.native.application focal message
        replay.applicationPlayerView sender
      cases leftHandle : runtime.handle left.native.application message with
      | none =>
          have rightHandle : runtime.handle right.native.application message = none := by
            simpa [leftHandle] using handled
          rw [runtime.application.includePending_reject left.native id message lookup leftHandle,
            runtime.application.includePending_reject right.native id message rightLookup
              rightHandle]
          apply afterEnvironmentStep runtime focal replay (.include id)
          · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
              MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
              runtime.application.includePending_reject left.native id message lookup leftHandle]
          · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
              MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
              runtime.application.includePending_reject right.native id message rightLookup
                rightHandle]
          · exact replay.applicationPlayerView
          · simp only
            rw [replay.pool]
          · simp only
            rw [replay.receipts]
      | some leftApplication =>
          cases rightHandle : runtime.handle right.native.application message with
          | none => simp [leftHandle, rightHandle] at handled
          | some rightApplication =>
              have applicationView : leftApplication.playerView focal =
                  rightApplication.playerView focal := by
                simpa [leftHandle, rightHandle] using handled
              rw [runtime.application.includePending_accept left.native id message
                  leftApplication lookup leftHandle,
                runtime.application.includePending_accept right.native id message
                  rightApplication rightLookup rightHandle]
              apply afterEnvironmentStep runtime focal replay (.include id)
              · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
                  MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
                  runtime.application.includePending_accept left.native id message
                    leftApplication lookup leftHandle]
              · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
                  MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
                  runtime.application.includePending_accept right.native id message
                    rightApplication rightLookup rightHandle]
              · exact applicationView
              · simp only
                rw [replay.pool]
              · simp only
                rw [replay.receipts]

/-- Including a present commitment packet preserves native replay for every
sender.  Foreign binding meanings may differ; commitment handling exposes
neither their values nor their actions to `focal`. -/
theorem environmentInclude_commitment
    (runtime : EventGraphRuntime graph) (focal : Player) (id : MessageId Player)
    (message : Message Player (Payload graph)) (event : graph.EventId)
    (candidate : Handle graph)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (lookup : left.native.pool.lookup id = some message)
    (packet : message.payload = .commitment event candidate)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have leftMem := leftSupported
  have rightMem := rightSupported
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at leftMem rightMem
  subst leftNext
  subst rightNext
  have rightLookup : right.native.pool.lookup id = some message := by
    rw [← replay.pool]
    exact lookup
  rcases message with ⟨messageId, payload⟩
  change payload = .commitment event candidate at packet
  subst payload
  have handled := handle_commitment_playerView_congr runtime
    left.native.application right.native.application focal messageId event candidate
    replay.applicationPlayerView
  cases leftHandle : runtime.handle left.native.application
      ⟨messageId, .commitment event candidate⟩ with
  | none =>
      have rightHandle : runtime.handle right.native.application
          ⟨messageId, .commitment event candidate⟩ = none := by
        simpa [leftHandle] using handled
      rw [runtime.application.includePending_reject left.native id
            ⟨messageId, .commitment event candidate⟩ lookup leftHandle,
        runtime.application.includePending_reject right.native id
            ⟨messageId, .commitment event candidate⟩ rightLookup rightHandle]
      apply afterEnvironmentStep runtime focal replay (.include id)
      · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          runtime.application.includePending_reject left.native id
            ⟨messageId, .commitment event candidate⟩ lookup leftHandle]
      · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
          MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
          runtime.application.includePending_reject right.native id
            ⟨messageId, .commitment event candidate⟩ rightLookup rightHandle]
      · exact replay.applicationPlayerView
      · simp only
        rw [replay.pool]
      · simp only
        rw [replay.receipts]
  | some leftApplication =>
      cases rightHandle : runtime.handle right.native.application
          ⟨messageId, .commitment event candidate⟩ with
      | none => simp [leftHandle, rightHandle] at handled
      | some rightApplication =>
          have applicationView : leftApplication.playerView focal =
              rightApplication.playerView focal := by
            simpa [leftHandle, rightHandle] using handled
          rw [runtime.application.includePending_accept left.native id
                ⟨messageId, .commitment event candidate⟩ leftApplication lookup leftHandle,
            runtime.application.includePending_accept right.native id
                ⟨messageId, .commitment event candidate⟩ rightApplication rightLookup
                  rightHandle]
          apply afterEnvironmentStep runtime focal replay (.include id)
          · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
              MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
              runtime.application.includePending_accept left.native id
                ⟨messageId, .commitment event candidate⟩ leftApplication lookup leftHandle]
          · simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
              MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
              runtime.application.includePending_accept right.native id
                ⟨messageId, .commitment event candidate⟩ rightApplication rightLookup
                  rightHandle]
          · exact applicationView
          · simp only
            rw [replay.pool]
          · simp only
            rw [replay.receipts]

/-- Including a present withholding packet preserves native replay for every
sender; foreign cached choices are intentionally unconstrained. -/
theorem environmentInclude_withhold
    (runtime : EventGraphRuntime graph) (focal : Player) (id messageId : MessageId Player)
    (event : graph.EventId)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (lookup : left.native.pool.lookup id = some ⟨messageId, .withhold event⟩)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  apply environmentInclude_of_present_handleView runtime focal id
    ⟨messageId, .withhold event⟩ replay lookup
  · by_cases sender : messageId.1 = focal
    · exact handle_playerView_congr_of_sender runtime left.native.application
        right.native.application focal ⟨messageId, .withhold event⟩
        replay.applicationPlayerView sender
    · exact handle_withhold_playerView_congr_of_sender_ne runtime left.native.application
        right.native.application focal messageId event replay.applicationPlayerView sender
  · exact leftSupported
  · exact rightSupported

/-- Including a present malformed packet records the same rejection receipt
and otherwise preserves replay. -/
theorem environmentInclude_malformed
    (runtime : EventGraphRuntime graph) (focal : Player) (id messageId : MessageId Player)
    (raw : Raw L)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (lookup : left.native.pool.lookup id = some ⟨messageId, .malformed raw⟩)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  apply environmentInclude_of_present_handleView runtime focal id
    ⟨messageId, .malformed raw⟩ replay lookup
  · exact handle_malformed_playerView_congr runtime left.native.application
      right.native.application focal messageId raw
  · exact leftSupported
  · exact rightSupported

/-- Including a present prescribed foreign opening preserves replay. Packet
origin and binding invariants replace any equality assumption on the owner's
private candidate catalogue or binding store. -/
theorem environmentInclude_prescribedOpening
    (runtime : EventGraphRuntime graph) (focal owner : Player)
    (different : owner ≠ focal) (id : MessageId Player) (nonce : Nat)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftOrigins : ResolutionOrigins runtime left owner)
    (rightOrigins : ResolutionOrigins runtime right owner)
    (leftBinding : left.native.application.BindingInvariant)
    (rightBinding : right.native.application.BindingInvariant)
    (lookup : left.native.pool.lookup id =
      some ⟨(owner, nonce), .opening event candidate raw⟩)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    NativeReplay runtime focal leftNext rightNext := by
  have pending : (⟨(owner, nonce), .opening event candidate raw⟩ :
      Message Player (Payload graph)) ∈ left.native.pool.pending := by
    change left.native.pool.pending.find? (fun message => message.id = id) =
      some ⟨(owner, nonce), .opening event candidate raw⟩ at lookup
    exact List.mem_of_find?_eq_some lookup
  apply environmentInclude_of_present_handleView runtime focal id
    ⟨(owner, nonce), .opening event candidate raw⟩ replay lookup
  · exact replay.handle_prescribed_opening runtime focal owner different leftOrigins rightOrigins
      leftBinding rightBinding event nonce candidate raw pending
  · exact leftSupported
  · exact rightSupported

/-- If paired replay is retained across two transitions that complete the
same focal-owned event, the effective dependent actions are equal. -/
theorem completedFocalAction_eq
    (runtime : EventGraphRuntime graph) (focal : Player)
    {leftBefore rightBefore leftAfter rightAfter : runtime.application.PolicyExecution}
    (beforeReplay : NativeReplay runtime focal leftBefore rightBefore)
    (afterReplay : NativeReplay runtime focal leftAfter rightAfter)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (leftReady : leftBefore.native.application.config.cut.Ready event)
    (rightReady : rightBefore.native.application.config.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftCompletion : leftAfter.native.application.config ∈
      (leftBefore.native.application.config.step event leftReady leftAction).support)
    (rightCompletion : rightAfter.native.application.config ∈
      (rightBefore.native.application.config.step event rightReady rightAction).support) :
    leftAction = rightAction := by
  have beforeOwn := congrArg PlayerObservation.ownActions beforeReplay.observation
  have afterOwn := congrArg PlayerObservation.ownActions afterReplay.observation
  have leftHistory := leftBefore.native.application.config.step_history event leftReady
    leftAction leftAfter.native.application.config leftCompletion
  have rightHistory := rightBefore.native.application.config.step_history event rightReady
    rightAction rightAfter.native.application.config rightCompletion
  simp only [playerObserve] at beforeOwn afterOwn
  rw [leftHistory, rightHistory] at afterOwn
  simp only [ownCompletions] at beforeOwn
  simp only [ownCompletions, List.filter_append, List.filter_cons, actor, decide_true,
    ↓reduceIte, List.filter_nil] at afterOwn
  rw [beforeOwn] at afterOwn
  have completionEq : (⟨event, leftAction⟩ : graph.Completion) = ⟨event, rightAction⟩ :=
    (List.cons.inj (List.append_cancel_left afterOwn)).1
  cases completionEq
  rfl

end NativeReplay

/-- Synchronized service cursors together with their native focal replay
state.  Order selection and instruction consumption are compared only while
these public control fields agree. -/
structure ServiceReplay (runtime : EventGraphRuntime graph) (focal : Player)
    (left right : ServiceControl runtime) : Prop where
  epochs : left.epochs = right.epochs
  plan : left.plan = right.plan
  native : NativeReplay runtime focal left.execution right.execution

namespace ServiceReplay

theorem environmentInput
    {runtime : EventGraphRuntime graph} {focal : Player}
    {left right : ServiceControl runtime}
    (replay : ServiceReplay runtime focal left right) :
    (left.execution.environmentHistory,
        MessageApplication.State.environmentView runtime.application
          left.execution.native) =
      (right.execution.environmentHistory,
        MessageApplication.State.environmentView runtime.application
          right.execution.native) := by
  exact Prod.ext replay.native.environmentHistory replay.native.environmentView

end ServiceReplay

/-- Controls reachable through the actual adaptive service small-step
semantics, starting from an input in the supplied initialization law. -/
inductive ServiceReachable (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ServiceControl runtime → Prop
  | initial (input : graph.Inputs) (member : input ∈ inputs.support) :
      ServiceReachable runtime inputs roster reactionRounds players wire order
        { epochs := runtime.serviceEpochs
          plan := []
          execution := MessageApplication.PolicyExecution.initial runtime.application
            (MessageApplication.State.initial runtime.application (State.initial input)) }
  | step {before after : ServiceControl runtime}
      (prior : ServiceReachable runtime inputs roster reactionRounds players wire order before)
      (supported : after ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        before).support) :
      ServiceReachable runtime inputs roster reactionRounds players wire order after

/-- A finite actual small-step suffix between two service controls. -/
inductive ServiceControlPath (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ServiceControl runtime → ServiceControl runtime → Prop
  | nil (control : ServiceControl runtime) :
      ServiceControlPath runtime roster reactionRounds players wire order control control
  | cons {before middle after : ServiceControl runtime}
      (step : middle ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        before).support)
      (tail : ServiceControlPath runtime roster reactionRounds players wire order middle after) :
      ServiceControlPath runtime roster reactionRounds players wire order before after

namespace ServiceControlPath

theorem trans (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {first middle last : ServiceControl runtime}
    (left : ServiceControlPath runtime roster reactionRounds players wire order first middle)
    (right : ServiceControlPath runtime roster reactionRounds players wire order middle last) :
    ServiceControlPath runtime roster reactionRounds players wire order first last := by
  induction left with
  | nil => exact right
  | cons step tail ih => exact .cons step (ih right)

theorem history_prefix (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {before after : ServiceControl runtime}
    (path : ServiceControlPath runtime roster reactionRounds players wire order before after) :
    before.execution.native.application.config.history.IsPrefix
      after.execution.native.application.config.history := by
  induction path with
  | nil => exact ⟨[], by simp⟩
  | cons step tail ih =>
      exact (runtime.serviceControlStep_history_prefix roster reactionRounds players wire order
        _ _ step).trans ih

theorem store_of_some (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {before after : ServiceControl runtime}
    (path : ServiceControlPath runtime roster reactionRounds players wire order before after)
    (field : graph.Field) (value : (graph.layout field).Value)
    (stored : before.execution.native.application.config.store field = some value) :
    after.execution.native.application.config.store field = some value := by
  induction path with
  | nil => exact stored
  | cons step tail ih =>
      apply ih
      exact runtime.serviceControlStep_store_of_some roster reactionRounds players wire order
        _ _ step field value stored

/-- Equal normalized endpoint observations reconstruct the complete focal
observation at two earlier service positions once their chronological event
orders agree.  Endpoint data is used only through immutable suffixes. -/
theorem playerObserve_eq_of_endpoint (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (orderPolicy : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId)
    {left right leftEnd rightEnd : ServiceControl runtime}
    (leftPath : ServiceControlPath runtime roster reactionRounds players wire orderPolicy
      left leftEnd)
    (rightPath : ServiceControlPath runtime roster reactionRounds players wire orderPolicy
      right rightEnd)
    (orderEq : left.execution.native.application.config.history.map Completion.event =
      right.execution.native.application.config.history.map Completion.event)
    (endpoints : graph.normalizeObservation event focal
        (graph.playerObserve focal leftEnd.execution.native.application.config) =
      graph.normalizeObservation event focal
        (graph.playerObserve focal rightEnd.execution.native.application.config)) :
    graph.playerObserve focal left.execution.native.application.config =
      graph.playerObserve focal right.execution.native.application.config := by
  let leftConfig := left.execution.native.application.config
  let rightConfig := right.execution.native.application.config
  let leftEndConfig := leftEnd.execution.native.application.config
  let rightEndConfig := rightEnd.execution.native.application.config
  have cuts : leftConfig.cut = rightConfig.cut :=
    cut_eq_of_completionOrder_eq leftConfig rightConfig orderEq
  have endpointStores : graph.playerStore focal leftEndConfig.store =
      graph.playerStore focal rightEndConfig.store := by
    simpa only [normalizeObservation_store, playerObserve] using
      congrArg PlayerObservation.store endpoints
  have endpointActions : graph.ownCompletions focal leftEndConfig.history =
      graph.ownCompletions focal rightEndConfig.history := by
    simpa only [normalizeObservation_ownActions, playerObserve] using
      congrArg PlayerObservation.ownActions endpoints
  have stores : graph.playerStore focal leftConfig.store =
      graph.playerStore focal rightConfig.store := by
    apply playerStore_eq_of_extensions focal leftConfig rightConfig leftEndConfig rightEndConfig
      cuts endpointStores
    · intro field value stored
      exact leftPath.store_of_some runtime roster reactionRounds players wire orderPolicy
        field value stored
    · intro field value stored
      exact rightPath.store_of_some runtime roster reactionRounds players wire orderPolicy
        field value stored
  have actions : graph.ownCompletions focal leftConfig.history =
      graph.ownCompletions focal rightConfig.history := by
    apply ownCompletions_eq_of_extensions focal leftConfig rightConfig leftEndConfig
      rightEndConfig orderEq endpointActions
    · exact leftPath.history_prefix runtime roster reactionRounds players wire orderPolicy
    · exact rightPath.history_prefix runtime roster reactionRounds players wire orderPolicy
  apply PlayerObservation.ext graph
  · exact orderEq
  · exact stores
  · exact actions

end ServiceControlPath

/-- The result of synchronizing two finite service paths until one or both
paths end. -/
inductive ServicePathComparison (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (leftEnd rightEnd : ServiceControl runtime) : Prop
  | same (replay : ServiceReplay runtime focal leftEnd rightEnd)
  | leftShort (rightAt rightNext : ServiceControl runtime)
      (replay : ServiceReplay runtime focal leftEnd rightAt)
      (step : rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        rightAt).support)
      (suffix : ServiceControlPath runtime roster reactionRounds players wire order
        rightNext rightEnd)
  | rightShort (leftAt leftNext : ServiceControl runtime)
      (replay : ServiceReplay runtime focal leftAt rightEnd)
      (step : leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        leftAt).support)
      (suffix : ServiceControlPath runtime roster reactionRounds players wire order
        leftNext leftEnd)

/-- Lockstep comparison is purely structural once the semantic one-step replay
law has been supplied. -/
theorem ServiceControlPath.compare (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (paired : ∀ {left right leftNext rightNext : ServiceControl runtime},
      ServiceReplay runtime focal left right →
      leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        left).support →
      rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        right).support →
      ServiceReplay runtime focal leftNext rightNext)
    {left right leftEnd rightEnd : ServiceControl runtime}
    (initial : ServiceReplay runtime focal left right)
    (leftPath : ServiceControlPath runtime roster reactionRounds players wire order
      left leftEnd)
    (rightPath : ServiceControlPath runtime roster reactionRounds players wire order
      right rightEnd) :
    ServicePathComparison runtime roster reactionRounds players wire order focal
      leftEnd rightEnd := by
  induction leftPath generalizing right with
  | nil =>
      cases rightPath with
      | nil => exact .same initial
      | cons rightStep rightTail => exact .leftShort _ _ initial rightStep rightTail
  | cons leftStep leftTail ih =>
      cases rightPath with
      | nil => exact .rightShort _ _ initial leftStep leftTail
      | cons rightStep rightTail =>
          exact ih (paired initial leftStep rightStep) rightTail

/-- Endpoint-aware lockstep comparison.  The paired-step proof receives the
remaining actual suffixes, which is essential for coupling public chance
results from equal normalized endpoints. -/
theorem ServiceControlPath.compareEndpoint (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (paired : ∀ {left right leftNext rightNext leftEnd rightEnd : ServiceControl runtime},
      ServiceReplay runtime focal left right →
      leftNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        left).support →
      rightNext ∈ (runtime.serviceControlStep roster reactionRounds players wire order
        right).support →
      ServiceControlPath runtime roster reactionRounds players wire order leftNext leftEnd →
      ServiceControlPath runtime roster reactionRounds players wire order rightNext rightEnd →
      ServiceReplay runtime focal leftNext rightNext)
    {left right leftEnd rightEnd : ServiceControl runtime}
    (initial : ServiceReplay runtime focal left right)
    (leftPath : ServiceControlPath runtime roster reactionRounds players wire order
      left leftEnd)
    (rightPath : ServiceControlPath runtime roster reactionRounds players wire order
      right rightEnd) :
    ServicePathComparison runtime roster reactionRounds players wire order focal
      leftEnd rightEnd := by
  induction leftPath generalizing right with
  | nil =>
      cases rightPath with
      | nil => exact .same initial
      | cons rightStep rightTail => exact .leftShort _ _ initial rightStep rightTail
  | cons leftStep leftTail ih =>
      cases rightPath with
      | nil => exact .rightShort _ _ initial leftStep leftTail
      | cons rightStep rightTail =>
          exact ih (paired initial leftStep rightStep leftTail rightTail) rightTail

namespace ServiceReachable

/-- Every reachable control retains a concrete supported path from one
supported initialized input. -/
theorem exists_initial_path (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    {control : ServiceControl runtime}
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      control) :
    ∃ input, input ∈ inputs.support ∧
      ServiceControlPath runtime roster reactionRounds players wire order
        { epochs := runtime.serviceEpochs
          plan := []
          execution := MessageApplication.PolicyExecution.initial runtime.application
            (MessageApplication.State.initial runtime.application (State.initial input)) }
        control := by
  induction reachable with
  | initial input member => exact ⟨input, member, .nil _⟩
  | step prior supported ih =>
      obtain ⟨input, member, path⟩ := ih
      exact ⟨input, member, path.trans runtime roster reactionRounds players wire order
        (.cons supported (.nil _))⟩

end ServiceReachable

/-- One focal-owned semantic action realized by an actual reachable service
control transition.  The observed key is source-rank normalized, while the
effective action is the dependent action retained by the graph completion. -/
inductive ReachedFocalAction (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId)
    (observation : graph.PlayerObservation focal) (action : graph.Action event) : Prop where
  | realized (before after : ServiceControl runtime)
      (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
      (transition : after ∈
        (runtime.serviceControlStep roster reactionRounds players wire order before).support)
      (actor : graph.actor? event = some focal)
      (ready : before.execution.native.application.config.cut.Ready event)
      (completion : after.execution.native.application.config ∈
        (before.execution.native.application.config.step event ready action).support)
      (observed : graph.normalizeObservation event focal
        (graph.playerObserve focal before.execution.native.application.config) = observation) :
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
        observation action

/-- Canonical fallback used only at normalized observations that no native
execution reaches. -/
def defaultEventAction (event : graph.EventId) : graph.Action event := by
  classical
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      exact cast (congrArg EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))
  | resolve owner payload binding checks outputEq codeEq =>
      exact cast (congrArg EventField.Action outputEq.symm) false
  | sample payload law outputEq codeEq =>
      exact cast (congrArg EventField.Action outputEq.symm) PUnit.unit

/-- Total graph policy extracted from the partial relation of actions reached
by one fixed native response triple. -/
def reachedFocalPolicy (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) : graph.BehavioralPolicy focal := by
  classical
  intro event actor observation
  let relation := fun action : graph.Action event =>
    ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
      (graph.normalizeObservation event focal observation) action
  exact FinDist.pure (if existsAction : ∃ action, relation action then
    Classical.choose existsAction else defaultEventAction event)

/-- The extracted policy selects every reached effective action once the
two-run locality relation is functional. -/
theorem reachedFocalPolicy_eq_of_functional
    (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (observation : graph.PlayerObservation focal) (action : graph.Action event)
    (reached : ReachedFocalAction runtime inputs roster reactionRounds players wire order focal
      event (graph.normalizeObservation event focal observation) action) :
    reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
      event actor observation = FinDist.pure action := by
  unfold reachedFocalPolicy
  dsimp only
  rw [dite_eq_left ⟨action, reached⟩]
  exact congrArg FinDist.pure
    (functional event _ (Classical.choose _) action (Classical.choose_spec _) reached)

end Vegas.EventGraphRuntime
