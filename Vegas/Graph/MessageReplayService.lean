/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationPrefixLocality
import Vegas.Graph.MessageReplayEnvironment
import Vegas.Graph.MessageOpeningSoundness

/-! # Actual service-environment replay -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- The environment replay law with its two semantic side conditions derived
from actual initialized reaches and actual residual endpoints. -/
theorem FocalReplayCheckpoint.environmentStep_initialized_replay
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    {suffix : Graph Player L Γ Δ}
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (environment : runtime.application.EnvironmentPolicy)
    (leftInput rightInput : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (leftPrefix rightPrefix : List (@MessageApplication.Invocation Player))
    (leftReached : left ∈ (runtime.application.runPolicies players environment leftPrefix
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))).support)
    (rightReached : right ∈ (runtime.application.runPolicies players environment rightPrefix
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput)))).support)
    (command : runtime.application.EnvironmentPolicyCommand)
    (leftSupported : leftNext ∈
      (runtime.application.environmentPolicyStep left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.environmentPolicyStep right command).support)
    (leftRest rightRest : List (@MessageApplication.Invocation Player))
    (leftEnd rightEnd : runtime.application.PolicyExecution)
    {target : VCtx Player L} (endSuffix : Graph Player L target Δ)
    (leftEndIdeal rightEndIdeal : VEnv L target)
    (leftEndValues rightEndValues : PublicValues target)
    (leftEndBindings rightEndBindings : Bindings Player)
    (leftEndCandidates rightEndCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftEndPc leftEndClock leftEndEntered rightEndPc rightEndClock rightEndEntered : Nat)
    (leftResidual : leftEnd ∈
      (runtime.application.runPolicies players environment leftRest leftNext).support)
    (rightResidual : rightEnd ∈
      (runtime.application.runPolicies players environment rightRest rightNext).support)
    (leftEndState : leftEnd.native.application = .running endSuffix leftEndIdeal
      leftEndValues leftEndBindings leftEndCandidates leftEndPc leftEndClock leftEndEntered)
    (rightEndState : rightEnd.native.application = .running endSuffix rightEndIdeal
      rightEndValues rightEndBindings rightEndCandidates rightEndPc rightEndClock rightEndEntered)
    (endVisible : observe focal leftEndIdeal = observe focal rightEndIdeal) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      State.focalReplayKey focal leftNext.native.application =
        State.focalReplayKey focal rightNext.native.application ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native := by
  apply checkpoint.environmentPolicyStep_focalReplay_congr runtime focal command
    leftSupported rightSupported
  · intro id message site handle raw commandEq lookup payload foreign
    have rightLookup : right.native.pool.lookup id = some message := by
      rw [← checkpoint.pool]
      exact lookup
    have leftPending : message ∈ left.native.pool.pending := List.mem_of_find?_eq_some lookup
    have rightPending : message ∈ right.native.pool.pending :=
      List.mem_of_find?_eq_some rightLookup
    rcases message with ⟨⟨sender, serial⟩, messagePayload⟩
    change sender ≠ focal at foreign
    change messagePayload = .opening site handle raw at payload
    subst messagePayload
    have leftVerified := runtime.pending_opening_verified whole leftInput unique discipline
      sender (profile sender) players (compiled sender foreign) environment leftPrefix left
      site serial handle raw leftReached leftPending
    have rightVerified := runtime.pending_opening_verified whole rightInput unique discipline
      sender (profile sender) players (compiled sender foreign) environment rightPrefix right
      site serial handle raw rightReached rightPending
    have leftVerified' : checkpoint.leftCandidates.verify handle raw = true := by
      rw [checkpoint.leftState] at leftVerified
      exact leftVerified
    have rightVerified' : checkpoint.rightCandidates.verify handle raw = true := by
      rw [checkpoint.rightState] at rightVerified
      exact rightVerified
    exact leftVerified'.trans rightVerified'.symm
  · intro environmentCommand commandEq
    subst command
    cases environmentCommand
    by_cases sample : ∃ (name : VarId) (payload : L.Ty)
        (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
        (tail : Graph Player L ((name, .pub payload) :: Γ) Δ),
      suffix = .sample name fresh law tail
    · obtain ⟨name, payload, fresh, law, sampleTail, rfl⟩ := sample
      exact (checkpoint.sampleTick_focalReplay_congr runtime focal leftSupported rightSupported
        (by
        intro leftValue rightValue leftState rightState
        have leftExtends := runtime.runPolicies_extends sampleTail
          (VEnv.cons leftValue checkpoint.leftIdeal) players environment leftRest leftNext leftEnd
          (by
            rw [leftState]
            exact State.running_extends _ _ _ _ _ _ _ _)
          leftResidual
        have rightExtends := runtime.runPolicies_extends sampleTail
          (VEnv.cons rightValue checkpoint.rightIdeal) players environment rightRest rightNext
          rightEnd
          (by
            rw [rightState]
            exact State.running_extends _ _ _ _ _ _ _ _)
          rightResidual
        rw [leftEndState] at leftExtends
        rw [rightEndState] at rightExtends
        exact endpointObservation_restricts_to_cursor focal sampleTail
          (VEnv.cons leftValue checkpoint.leftIdeal)
          (VEnv.cons rightValue checkpoint.rightIdeal) endSuffix leftEndIdeal rightEndIdeal
          leftEndValues rightEndValues leftEndBindings rightEndBindings leftEndCandidates
          rightEndCandidates leftEndPc leftEndClock leftEndEntered rightEndPc rightEndClock
          rightEndEntered leftExtends rightExtends endVisible)).2.2.1
    · exact (checkpoint.nonsampleTick_focalReplay_congr runtime focal sample
        leftSupported rightSupported).2.2.1
  · intro environmentCommand commandEq
    subst command
    cases environmentCommand
    by_cases sample : ∃ (name : VarId) (payload : L.Ty)
        (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
        (tail : Graph Player L ((name, .pub payload) :: Γ) Δ),
      suffix = .sample name fresh law tail
    · obtain ⟨name, payload, fresh, law, sampleTail, rfl⟩ := sample
      exact (checkpoint.sampleTick_focalReplay_congr runtime focal leftSupported rightSupported
        (by
        intro leftValue rightValue leftState rightState
        have leftExtends := runtime.runPolicies_extends sampleTail
          (VEnv.cons leftValue checkpoint.leftIdeal) players environment leftRest leftNext leftEnd
          (by rw [leftState]; exact State.running_extends _ _ _ _ _ _ _ _)
          leftResidual
        have rightExtends := runtime.runPolicies_extends sampleTail
          (VEnv.cons rightValue checkpoint.rightIdeal) players environment rightRest rightNext
          rightEnd (by rw [rightState]; exact State.running_extends _ _ _ _ _ _ _ _)
          rightResidual
        rw [leftEndState] at leftExtends
        rw [rightEndState] at rightExtends
        exact endpointObservation_restricts_to_cursor focal sampleTail
          (VEnv.cons leftValue checkpoint.leftIdeal)
          (VEnv.cons rightValue checkpoint.rightIdeal) endSuffix leftEndIdeal rightEndIdeal
          leftEndValues rightEndValues leftEndBindings rightEndBindings leftEndCandidates
          rightEndCandidates leftEndPc leftEndClock leftEndEntered rightEndPc rightEndClock
          rightEndEntered leftExtends rightExtends endVisible)).2.2.2
    · exact (checkpoint.nonsampleTick_focalReplay_congr runtime focal sample
        leftSupported rightSupported).2.2.2

/-- One actual invocation of the pure service environment preserves the native
replay invariant at every nonsample cursor.  The common command is derived
from the equal service inputs, not supplied by the caller. -/
theorem NativeReplayInvariant.pureServiceEnvironment_nonsample_afterInvoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right)
    {suffix : Graph Player L Γ Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (notSample : ¬ ∃ (name : VarId) (payload : L.Ty)
      (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
      (tail : Graph Player L ((name, .pub payload) :: Γ) Δ),
      suffix = .sample name fresh law tail)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (plan : List (ServiceInstruction Player))
    (wireResponse : (List runtime.application.EnvironmentEntry ×
      runtime.application.EnvironmentObservation) → WireCommand Player)
    (leftInput rightInput : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (leftPrefix rightPrefix : List (@MessageApplication.Invocation Player))
    (leftReached : left ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) leftPrefix
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))).support)
    (rightReached : right ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) rightPrefix
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput)))).support)
    (leftSupported : leftNext ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) left .environment).support)
    (rightSupported : rightNext ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) right .environment).support) :
    NativeReplayInvariant runtime whole focal leftNext rightNext := by
  let service := runtime.serviceEnvironment plan (fun history view =>
    FinDist.pure (wireResponse (history, view)))
  have leftInvoke := leftSupported
  have rightInvoke := rightSupported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftSupported rightSupported
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftSupported
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightSupported
  have serviceInput : (left.environmentHistory,
      MessageApplication.State.environmentView runtime.application left.native) =
      (right.environmentHistory,
        MessageApplication.State.environmentView runtime.application right.native) :=
    Prod.ext invariant.environmentHistory invariant.environmentView
  have lawEq : service left.environmentHistory
      (MessageApplication.State.environmentView runtime.application left.native) =
      service right.environmentHistory
        (MessageApplication.State.environmentView runtime.application right.native) := by
    exact congrArg (fun input => service input.1 input.2) serviceInput
  have deterministic : ∃ command, service left.environmentHistory
      (MessageApplication.State.environmentView runtime.application left.native) =
        FinDist.pure command := by
    unfold service GraphRuntime.serviceEnvironment
    generalize
      (plan.filterMap ServiceInstruction.environmentSlot)[left.environmentHistory.length]? = slot
    cases slot with
    | none => exact ⟨.wait, rfl⟩
    | some instruction =>
        cases instruction with
        | player owner => exact ⟨.wait, rfl⟩
        | wire =>
            let response := wireResponse (left.environmentHistory,
              MessageApplication.State.environmentView runtime.application left.native)
            refine ⟨response.toEnvironmentCommand runtime.application, ?_⟩
            simp only [MessageApplication.wireEnvironment, FinDist.map_pure]
            rfl
        | includeLatest owner => exact ⟨_, rfl⟩
        | expire phase => exact ⟨_, rfl⟩
  obtain ⟨chosen, chosenLaw⟩ := deterministic
  change leftCommand ∈ (service left.environmentHistory
    (MessageApplication.State.environmentView runtime.application left.native)).support
    at leftChosen
  change rightCommand ∈ (service right.environmentHistory
    (MessageApplication.State.environmentView runtime.application right.native)).support
    at rightChosen
  rw [chosenLaw, FinDist.mem_support_pure] at leftChosen
  rw [← lawEq, chosenLaw, FinDist.mem_support_pure] at rightChosen
  subst leftCommand
  subst rightCommand
  have replay := checkpoint.environmentPolicyStep_focalReplay_congr runtime focal chosen
    leftStep rightStep
    (by
      intro id message site handle raw commandEq lookup payload foreign
      have rightLookup : right.native.pool.lookup id = some message := by
        rw [← checkpoint.pool]
        exact lookup
      have leftPending := List.mem_of_find?_eq_some lookup
      have rightPending := List.mem_of_find?_eq_some rightLookup
      rcases message with ⟨⟨sender, serial⟩, messagePayload⟩
      change sender ≠ focal at foreign
      change messagePayload = .opening site handle raw at payload
      subst messagePayload
      have lv := runtime.pending_opening_verified whole leftInput unique discipline sender
        (profile sender) players (compiled sender foreign) service leftPrefix left site serial
        handle raw leftReached leftPending
      have rv := runtime.pending_opening_verified whole rightInput unique discipline sender
        (profile sender) players (compiled sender foreign) service rightPrefix right site serial
        handle raw rightReached rightPending
      rw [checkpoint.leftState] at lv
      rw [checkpoint.rightState] at rv
      exact lv.trans rv.symm)
    (by
      intro environmentCommand commandEq
      subst chosen
      cases environmentCommand
      exact (checkpoint.nonsampleTick_focalReplay_congr runtime focal notSample
        leftStep rightStep).2.2.1)
    (by
      intro environmentCommand commandEq
      subst chosen
      cases environmentCommand
      exact (checkpoint.nonsampleTick_focalReplay_congr runtime focal notSample
        leftStep rightStep).2.2.2)
  have phase := congrArg (fun view => view.application.pc) replay.2.2.2
  exact invariant.afterInvoke players service .environment leftInvoke rightInvoke phase
    replay.2.2.1 replay.2.2.2 replay.1 replay.2.1 (by
      intro owner different
      rw [runtime.application.environmentStep_principalHistory left chosen leftNext leftStep,
        runtime.application.environmentStep_principalHistory right chosen rightNext rightStep]
      exact invariant.cacheShape owner different)

/-- The endpoint-general pure service invocation replay law.  Unlike the
nonsample specialization, this version also couples public sample draws by
pulling the common endpoint observation back through the two residual runs. -/
theorem NativeReplayInvariant.pureServiceEnvironment_afterInvoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right)
    {suffix : Graph Player L Γ Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (plan : List (ServiceInstruction Player))
    (wireResponse : (List runtime.application.EnvironmentEntry ×
      runtime.application.EnvironmentObservation) → WireCommand Player)
    (leftInput rightInput : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (leftPrefix rightPrefix : List (@MessageApplication.Invocation Player))
    (leftReached : left ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) leftPrefix
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))).support)
    (rightReached : right ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) rightPrefix
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput)))).support)
    (leftSupported : leftNext ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) left .environment).support)
    (rightSupported : rightNext ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) right .environment).support)
    (leftRest rightRest : List (@MessageApplication.Invocation Player))
    (leftEnd rightEnd : runtime.application.PolicyExecution)
    {target : VCtx Player L} (endSuffix : Graph Player L target Δ)
    (leftEndIdeal rightEndIdeal : VEnv L target)
    (leftEndValues rightEndValues : PublicValues target)
    (leftEndBindings rightEndBindings : Bindings Player)
    (leftEndCandidates rightEndCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftEndPc leftEndClock leftEndEntered rightEndPc rightEndClock rightEndEntered : Nat)
    (leftResidual : leftEnd ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) leftRest leftNext).support)
    (rightResidual : rightEnd ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) rightRest rightNext).support)
    (leftEndState : leftEnd.native.application = .running endSuffix leftEndIdeal
      leftEndValues leftEndBindings leftEndCandidates leftEndPc leftEndClock leftEndEntered)
    (rightEndState : rightEnd.native.application = .running endSuffix rightEndIdeal
      rightEndValues rightEndBindings rightEndCandidates rightEndPc rightEndClock rightEndEntered)
    (endVisible : observe focal leftEndIdeal = observe focal rightEndIdeal) :
    NativeReplayInvariant runtime whole focal leftNext rightNext := by
  let service := runtime.serviceEnvironment plan (fun history view =>
    FinDist.pure (wireResponse (history, view)))
  have leftInvoke := leftSupported
  have rightInvoke := rightSupported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftSupported rightSupported
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftSupported
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightSupported
  have serviceInput : (left.environmentHistory,
      MessageApplication.State.environmentView runtime.application left.native) =
      (right.environmentHistory,
        MessageApplication.State.environmentView runtime.application right.native) :=
    Prod.ext invariant.environmentHistory invariant.environmentView
  have lawEq : service left.environmentHistory
      (MessageApplication.State.environmentView runtime.application left.native) =
      service right.environmentHistory
        (MessageApplication.State.environmentView runtime.application right.native) := by
    exact congrArg (fun input => service input.1 input.2) serviceInput
  have deterministic : ∃ command, service left.environmentHistory
      (MessageApplication.State.environmentView runtime.application left.native) =
        FinDist.pure command := by
    unfold service GraphRuntime.serviceEnvironment
    generalize
      (plan.filterMap ServiceInstruction.environmentSlot)[left.environmentHistory.length]? = slot
    cases slot with
    | none => exact ⟨.wait, rfl⟩
    | some instruction =>
        cases instruction with
        | player owner => exact ⟨.wait, rfl⟩
        | wire =>
            let response := wireResponse (left.environmentHistory,
              MessageApplication.State.environmentView runtime.application left.native)
            refine ⟨response.toEnvironmentCommand runtime.application, ?_⟩
            simp only [MessageApplication.wireEnvironment, FinDist.map_pure]
            rfl
        | includeLatest owner => exact ⟨_, rfl⟩
        | expire phase => exact ⟨_, rfl⟩
  obtain ⟨chosen, chosenLaw⟩ := deterministic
  change leftCommand ∈ (service left.environmentHistory
    (MessageApplication.State.environmentView runtime.application left.native)).support
    at leftChosen
  change rightCommand ∈ (service right.environmentHistory
    (MessageApplication.State.environmentView runtime.application right.native)).support
    at rightChosen
  rw [chosenLaw, FinDist.mem_support_pure] at leftChosen
  rw [← lawEq, chosenLaw, FinDist.mem_support_pure] at rightChosen
  subst leftCommand
  subst rightCommand
  have replay := checkpoint.environmentStep_initialized_replay runtime whole profile focal
    players compiled service leftInput rightInput unique discipline leftPrefix rightPrefix
    leftReached rightReached chosen leftStep rightStep leftRest rightRest leftEnd rightEnd
    endSuffix leftEndIdeal rightEndIdeal leftEndValues rightEndValues leftEndBindings
    rightEndBindings leftEndCandidates rightEndCandidates leftEndPc leftEndClock
    leftEndEntered rightEndPc rightEndClock rightEndEntered leftResidual rightResidual
    leftEndState rightEndState endVisible
  have phase := congrArg (fun view => view.application.pc) replay.2.2.2
  exact invariant.afterInvoke players service .environment leftInvoke rightInvoke phase
    replay.2.2.1 replay.2.2.2 replay.1 replay.2.1 (by
      intro owner different
      rw [runtime.application.environmentStep_principalHistory left chosen leftNext leftStep,
        runtime.application.environmentStep_principalHistory right chosen rightNext rightStep]
      exact invariant.cacheShape owner different)

end Vegas.GraphRuntime

/-- info: 'Vegas.GraphRuntime.NativeReplayInvariant.pureServiceEnvironment_nonsample_afterInvoke' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.NativeReplayInvariant.pureServiceEnvironment_nonsample_afterInvoke

/-- info: 'Vegas.GraphRuntime.NativeReplayInvariant.pureServiceEnvironment_afterInvoke' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.NativeReplayInvariant.pureServiceEnvironment_afterInvoke
