/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageReplayApplication
import Vegas.Graph.MessageReplayTick

/-! # Environment-step replay bookkeeping -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Paired supported executions of one environment command retain every input
used by the focal and service responses. The chance tick is supplied by the
caller's coupled public draw; all deterministic message commands are handled
by the application replay law. -/
theorem FocalReplayCheckpoint.environmentPolicyStep_focalReplay_congr
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    {suffix : Graph Player L Γ Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (command : runtime.application.EnvironmentPolicyCommand)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right command).support)
    (foreignOpening : ∀ id message site handle raw,
      command = .include id →
      left.native.pool.lookup id = some message →
      message.payload = .opening site handle raw → message.sender ≠ focal →
      checkpoint.leftCandidates.verify handle raw =
        checkpoint.rightCandidates.verify handle raw)
    (tickKey : ∀ environmentCommand, command = .application environmentCommand →
      State.focalReplayKey focal leftNext.native.application =
        State.focalReplayKey focal rightNext.native.application)
    (tickEnvironment : ∀ environmentCommand, command = .application environmentCommand →
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      State.focalReplayKey focal leftNext.native.application =
        State.focalReplayKey focal rightNext.native.application ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native := by
  have principalLeft := runtime.application.environmentStep_principalHistory
    left command leftNext leftSupported
  have principalRight := runtime.application.environmentStep_principalHistory
    right command rightNext rightSupported
  have principal : leftNext.principalHistory focal = rightNext.principalHistory focal := by
    rw [congrFun principalLeft focal, congrFun principalRight focal]
    exact checkpoint.focalHistory
  have oldEnvironment :
      MessageApplication.State.environmentView runtime.application left.native =
        MessageApplication.State.environmentView runtime.application right.native :=
    by
      simp only [MessageApplication.State.environmentView]
      congr 1
      · exact checkpoint.pool
      · rw [checkpoint.leftState, checkpoint.rightState]
        rfl
      · exact checkpoint.receipts
  have oldApplicationEnvironment := congrArg
    MessageInterface.EnvironmentObservation.application oldEnvironment
  have oldKey : State.focalReplayKey focal left.native.application =
      State.focalReplayKey focal right.native.application := by
    rw [checkpoint.leftState, checkpoint.rightState]
    apply Prod.ext
    · change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
      congr 1
      · exact checkpoint.focalObservation
      · funext serial
        exact checkpoint.focalCandidates (.prepared serial)
    · funext slot
      exact checkpoint.focalCandidates slot
  refine ⟨principal, ?_⟩
  cases command with
  | application environmentCommand =>
      refine ⟨?_, tickKey environmentCommand rfl,
        tickEnvironment environmentCommand rfl⟩
      simp only [MessageApplication.environmentPolicyStep, FinDist.support_bind,
        Set.mem_iUnion, FinDist.mem_support_pure] at leftSupported rightSupported
      obtain ⟨leftAdvanced, _, rfl⟩ := leftSupported
      obtain ⟨rightAdvanced, _, rfl⟩ := rightSupported
      simp [checkpoint.environmentHistory, oldEnvironment]
  | wait =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, FinDist.pure_bind,
        FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftNext
      subst rightNext
      refine ⟨by simp [checkpoint.environmentHistory, oldEnvironment], ?_, oldEnvironment⟩
      · exact oldKey
  | deliver observer id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.mem_support_pure] at leftSupported rightSupported
      subst leftNext
      subst rightNext
      refine ⟨by simp [checkpoint.environmentHistory, oldEnvironment], ?_, ?_⟩
      · exact oldKey
      · simp only [MessageApplication.State.environmentView]
        rw [checkpoint.pool, checkpoint.receipts, checkpoint.leftState,
          checkpoint.rightState]
        rfl
  | «include» id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.mem_support_pure] at leftSupported rightSupported
      subst leftNext
      subst rightNext
      have lookupEq : left.native.pool.lookup id = right.native.pool.lookup id := by
        rw [checkpoint.pool]
      cases lookup : left.native.pool.lookup id with
      | none =>
          have rightLookup : right.native.pool.lookup id = none := lookupEq.symm.trans lookup
          rw [runtime.application.includePending_missing left.native id lookup,
            runtime.application.includePending_missing right.native id rightLookup]
          refine ⟨by simp [checkpoint.environmentHistory, oldEnvironment], ?_, ?_⟩
          · exact oldKey
          · exact oldEnvironment
      | some message =>
          have rightLookup : right.native.pool.lookup id = some message :=
            lookupEq.symm.trans lookup
          have handled := checkpoint.handle_focalReplayKey_congr runtime focal message
            (fun site handle raw payload foreign =>
              foreignOpening id message site handle raw rfl lookup payload foreign)
          cases leftHandle : runtime.handle left.native.application message with
          | none =>
              have rightHandle : runtime.handle right.native.application message = none := by
                simpa [leftHandle] using handled
              rw [runtime.application.includePending_reject left.native id message lookup
                    leftHandle,
                runtime.application.includePending_reject right.native id message rightLookup
                  rightHandle]
              refine ⟨by simp [checkpoint.environmentHistory, oldEnvironment], ?_, ?_⟩
              · exact oldKey
              · simp only [MessageApplication.State.environmentView]
                congr 1
                · rw [checkpoint.pool]
                · rw [checkpoint.receipts]
          | some leftApplication =>
              cases rightHandle : runtime.handle right.native.application message with
              | none => simp [leftHandle, rightHandle] at handled
              | some rightApplication =>
                  have keys : leftApplication.focalReplayKey focal =
                      rightApplication.focalReplayKey focal := by
                    simpa [leftHandle, rightHandle] using handled
                  rw [runtime.application.includePending_accept left.native id message
                    leftApplication lookup leftHandle,
                    runtime.application.includePending_accept right.native id message
                      rightApplication rightLookup rightHandle]
                  refine ⟨by simp [checkpoint.environmentHistory, oldEnvironment], keys, ?_⟩
                  simp only [MessageApplication.State.environmentView]
                  congr 1
                  · rw [checkpoint.pool]
                  · have playerKeys := congrArg Prod.fst keys
                    exact congrArg PlayerView.publicState playerKeys
                  · rw [checkpoint.receipts]

/-- At a public sample cursor, equality of the two successor focal graph
observations forces the supported public draws to coincide. Consequently the
generic environment replay theorem needs no residual tick premise. -/
theorem FocalReplayCheckpoint.sampleTick_focalReplay_congr
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    {name : VarId} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {law : PublicDist (L := L) Γ payload}
    {next : Graph Player L ((name, .pub payload) :: Γ) Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal
      (.sample name fresh law next) left right)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (EnvironmentCommand.tick : runtime.application.EnvironmentCommand))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (EnvironmentCommand.tick : runtime.application.EnvironmentCommand))).support)
    (successorVisible : ∀ leftValue rightValue,
      leftNext.native.application = .running next
        (VEnv.cons (x := name) (τ := .pub payload) leftValue checkpoint.leftIdeal)
        (PublicValues.consPublic leftValue checkpoint.publicValues)
        checkpoint.bindings checkpoint.leftCandidates (checkpoint.pc + 1)
        (checkpoint.clock + 1) (checkpoint.clock + 1) →
      rightNext.native.application = .running next
        (VEnv.cons (x := name) (τ := .pub payload) rightValue checkpoint.rightIdeal)
        (PublicValues.consPublic rightValue checkpoint.publicValues)
        checkpoint.bindings checkpoint.rightCandidates (checkpoint.pc + 1)
        (checkpoint.clock + 1) (checkpoint.clock + 1) →
      observe focal (VEnv.cons (x := name) (τ := .pub payload)
        leftValue checkpoint.leftIdeal) =
        observe focal (VEnv.cons (x := name) (τ := .pub payload)
          rightValue checkpoint.rightIdeal)) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      State.focalReplayKey focal leftNext.native.application =
        State.focalReplayKey focal rightNext.native.application ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native := by
  have leftStep := leftSupported
  have rightStep := rightSupported
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure]
    at leftSupported rightSupported
  obtain ⟨leftAdvanced, leftAdvancedMem, rfl⟩ := leftSupported
  obtain ⟨rightAdvanced, rightAdvancedMem, rfl⟩ := rightSupported
  rw [checkpoint.leftState] at leftAdvancedMem
  rw [checkpoint.rightState] at rightAdvancedMem
  simp only [FinDist.support_map, Set.mem_image]
    at leftAdvancedMem rightAdvancedMem
  obtain ⟨leftNative, ⟨leftApplication, leftApplicationMem, leftNativeState⟩,
    leftState⟩ := leftAdvancedMem
  obtain ⟨rightNative, ⟨rightApplication, rightApplicationMem, rightNativeState⟩,
    rightState⟩ :=
    rightAdvancedMem
  change leftApplication ∈
    (runtime.tick (.running (.sample name fresh law next) checkpoint.leftIdeal
      checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates checkpoint.pc
      checkpoint.clock checkpoint.enteredAt)).support at leftApplicationMem
  change rightApplication ∈
    (runtime.tick (.running (.sample name fresh law next) checkpoint.rightIdeal
      checkpoint.publicValues checkpoint.bindings checkpoint.rightCandidates checkpoint.pc
      checkpoint.clock checkpoint.enteredAt)).support at rightApplicationMem
  simp only [GraphRuntime.tick, FinDist.support_map, Set.mem_image]
    at leftApplicationMem rightApplicationMem
  obtain ⟨leftValue, _, leftApplicationState⟩ := leftApplicationMem
  obtain ⟨rightValue, _, rightApplicationState⟩ := rightApplicationMem
  subst leftAdvanced
  subst rightAdvanced
  subst leftNative
  subst rightNative
  subst leftApplication
  subst rightApplication
  have visible := successorVisible leftValue rightValue rfl rfl
  have valueEq : leftValue = rightValue := by
    have cell := congrArg (fun observation => observation.cells.get
      (.here : HasVar ((name, .pub payload) :: Γ) name (.pub payload))) visible
    change leftValue = rightValue at cell
    exact cell
  subst rightValue
  apply checkpoint.environmentPolicyStep_focalReplay_congr runtime focal
    (.application (EnvironmentCommand.tick : runtime.application.EnvironmentCommand))
    leftStep rightStep
  · intro id message site handle raw command
    cases command
  · intro environmentCommand command
    cases command
    apply Prod.ext
    · change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
      congr 1
      funext serial
      exact checkpoint.focalCandidates (.prepared serial)
    · funext slot
      exact checkpoint.focalCandidates slot
  · intro environmentCommand command
    cases command
    simp only [MessageApplication.State.environmentView]
    congr 1
    · exact checkpoint.pool
    · exact checkpoint.receipts

/-- Policy-step lift of `tick_application_congr`: away from chance nodes a
supported environment tick preserves every replay input, including histories
recorded by the message-policy wrapper. -/
theorem FocalReplayCheckpoint.nonsampleTick_focalReplay_congr
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    {suffix : Graph Player L Γ Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (notSample : ¬ ∃ (name : VarId) (payload : L.Ty)
        (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
        (tail : Graph Player L ((name, .pub payload) :: Γ) Δ),
      suffix = .sample name fresh law tail)
    (leftSupported : leftNext ∈ (runtime.application.environmentPolicyStep left
      (.application (EnvironmentCommand.tick : runtime.application.EnvironmentCommand))).support)
    (rightSupported : rightNext ∈ (runtime.application.environmentPolicyStep right
      (.application (EnvironmentCommand.tick : runtime.application.EnvironmentCommand))).support) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      State.focalReplayKey focal leftNext.native.application =
        State.focalReplayKey focal rightNext.native.application ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native := by
  have leftStep := leftSupported
  have rightStep := rightSupported
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure]
    at leftSupported rightSupported
  obtain ⟨leftAdvanced, leftAdvancedMem, rfl⟩ := leftSupported
  obtain ⟨rightAdvanced, rightAdvancedMem, rfl⟩ := rightSupported
  rw [checkpoint.leftState] at leftAdvancedMem
  rw [checkpoint.rightState] at rightAdvancedMem
  simp only [FinDist.support_map, Set.mem_image] at leftAdvancedMem rightAdvancedMem
  obtain ⟨leftNative, ⟨leftApplication, leftApplicationMem, leftNativeState⟩,
    leftState⟩ := leftAdvancedMem
  obtain ⟨rightNative, ⟨rightApplication, rightApplicationMem, rightNativeState⟩,
    rightState⟩ := rightAdvancedMem
  change leftApplication ∈ (runtime.tick (.running suffix checkpoint.leftIdeal
    checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates checkpoint.pc
    checkpoint.clock checkpoint.enteredAt)).support at leftApplicationMem
  change rightApplication ∈ (runtime.tick (.running suffix checkpoint.rightIdeal
    checkpoint.publicValues checkpoint.bindings checkpoint.rightCandidates checkpoint.pc
    checkpoint.clock checkpoint.enteredAt)).support at rightApplicationMem
  have native := checkpoint.tick_application_congr runtime focal notSample
    leftApplicationMem rightApplicationMem
  subst leftAdvanced
  subst rightAdvanced
  subst leftNative
  subst rightNative
  apply checkpoint.environmentPolicyStep_focalReplay_congr runtime focal
    (.application (EnvironmentCommand.tick : runtime.application.EnvironmentCommand))
    leftStep rightStep
  · intro id message site handle raw command
    cases command
  · intro environmentCommand command
    cases command
    exact Prod.ext native.1 native.2.1
  · intro environmentCommand command
    cases command
    simp only [MessageApplication.State.environmentView]
    congr 1
    · exact checkpoint.pool
    · exact native.2.2
    · exact checkpoint.receipts

/-- info: 'Vegas.GraphRuntime.FocalReplayCheckpoint.environmentPolicyStep_focalReplay_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.FocalReplayCheckpoint.environmentPolicyStep_focalReplay_congr

/-- info: 'Vegas.GraphRuntime.FocalReplayCheckpoint.sampleTick_focalReplay_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.FocalReplayCheckpoint.sampleTick_focalReplay_congr

/-- info: 'Vegas.GraphRuntime.FocalReplayCheckpoint.nonsampleTick_focalReplay_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.FocalReplayCheckpoint.nonsampleTick_focalReplay_congr

end Vegas.GraphRuntime
