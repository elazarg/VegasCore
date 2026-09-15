/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageReplayInvocation
import Vegas.Graph.MessageEndpointOwnership

/-! # Cached disclosure results forced by reached focal endpoints -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- The cached-result premise of compiled-player replay follows from actual
service safety and equal observations at the reached focal decision. -/
theorem FocalReplayCheckpoint.cachedResultsAgree_of_endpoints
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (leftInput rightInput : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal owner : Player) (different : owner ≠ focal)
    (policy : BehavioralPolicy owner whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (wire : runtime.application.WirePolicy)
    (plan before leftSegment rightSegment leftRest rightRest : List (ServiceInstruction Player))
    (leftSplit : plan = before ++ leftSegment ++ leftRest)
    (rightSplit : plan = before ++ rightSegment ++ rightRest)
    (leftSafe : DeviationExpirySafe runtime players (runtime.serviceEnvironment plan wire)
      (some focal) plan (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole leftInput))))
    (rightSafe : DeviationExpirySafe runtime players (runtime.serviceEnvironment plan wire)
      (some focal) plan (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole rightInput))))
    (left right leftEnd rightEnd : runtime.application.PolicyExecution)
    (suffix : Graph Player L Γ Δ)
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (leftReached : left ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))).support)
    (rightReached : right ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput)))).support)
    (leftResidual : leftEnd ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan wire) (leftSegment.map ServiceInstruction.invocation)
      left).support)
    (rightResidual : rightEnd ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan wire) (rightSegment.map ServiceInstruction.invocation)
      right).support)
    (leftOwned : leftEnd.native.application.IsOwnedBy (some focal))
    (rightOwned : rightEnd.native.application.IsOwnedBy (some focal))
    {target : VCtx Player L} (endSuffix : Graph Player L target Δ)
    (leftEndIdeal rightEndIdeal : VEnv L target)
    (leftEndValues rightEndValues : PublicValues target)
    (leftEndBindings rightEndBindings : Bindings Player)
    (leftEndCandidates rightEndCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftEndPc leftEndClock leftEndEntered rightEndPc rightEndClock rightEndEntered : Nat)
    (leftEndState : leftEnd.native.application = .running endSuffix leftEndIdeal
      leftEndValues leftEndBindings leftEndCandidates leftEndPc leftEndClock leftEndEntered)
    (rightEndState : rightEnd.native.application = .running endSuffix rightEndIdeal
      rightEndValues rightEndBindings rightEndCandidates rightEndPc rightEndClock rightEndEntered)
    (endVisible : observe focal leftEndIdeal = observe focal rightEndIdeal) :
    CachedResultsAgree runtime owner (left.principalHistory owner) (right.principalHistory owner)
      checkpoint.pc suffix checkpoint.leftIdeal checkpoint.rightIdeal := by
  cases suffix with
  | ret | sample | bind => trivial
  | resolve outputName nodeOwner bindingName fresh source checks tail =>
      intro owned leftDisclose rightDisclose leftRemembered rightRemembered
      subst nodeOwner
      have leftNotOwned : ¬ left.native.application.IsOwnedBy (some focal) := by
        simpa only [checkpoint.leftState, State.IsOwnedBy, Option.some.injEq] using
          Ne.symm different
      have rightNotOwned : ¬ right.native.application.IsOwnedBy (some focal) := by
        simpa only [checkpoint.rightState, State.IsOwnedBy, Option.some.injEq] using
          Ne.symm different
      have leftAdvanced : checkpoint.pc < leftEnd.native.application.phase := by
        have advanced := runtime.runPolicies_phase_lt_of_owned_endpoint players
          (runtime.serviceEnvironment plan wire) (leftSegment.map ServiceInstruction.invocation)
          focal left leftEnd checkpoint.leftState leftNotOwned leftOwned leftResidual
        simpa only [checkpoint.leftState, State.phase] using advanced
      have rightAdvanced : checkpoint.pc < rightEnd.native.application.phase := by
        have advanced := runtime.runPolicies_phase_lt_of_owned_endpoint players
          (runtime.serviceEnvironment plan wire) (rightSegment.map ServiceInstruction.invocation)
          focal right rightEnd checkpoint.rightState rightNotOwned rightOwned rightResidual
        simpa only [checkpoint.rightState, State.phase] using advanced
      have leftPublic := runtime.runPolicies_preserves_publicAgreement players
        (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
        _ left (State.initial_publicAgreement whole leftInput) leftReached
      have rightPublic := runtime.runPolicies_preserves_publicAgreement players
        (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
        _ right (State.initial_publicAgreement whole rightInput) rightReached
      rw [checkpoint.leftState] at leftPublic
      rw [checkpoint.rightState] at rightPublic
      change (checkpoint.publicValues : PublicValues Γ) =
        (PublicValues.ofVEnv checkpoint.leftIdeal : PublicValues Γ) at leftPublic
      change (checkpoint.publicValues : PublicValues Γ) =
        (PublicValues.ofVEnv checkpoint.rightIdeal : PublicValues Γ) at rightPublic
      have leftExtends := runtime.compiled_resolve_endpoint_extends whole leftInput unique
        discipline focal owner different policy players compiled wire plan before leftSegment
        leftRest leftSplit leftSafe left leftEnd leftReached leftResidual outputName bindingName
        fresh source checks tail checkpoint.leftIdeal checkpoint.bindings checkpoint.leftCandidates
        checkpoint.pc checkpoint.clock checkpoint.enteredAt
        (checkpoint.leftState.trans (by rw [leftPublic])) leftDisclose leftRemembered leftAdvanced
      have rightExtends := runtime.compiled_resolve_endpoint_extends whole rightInput unique
        discipline focal owner different policy players compiled wire plan before rightSegment
        rightRest rightSplit rightSafe right rightEnd rightReached rightResidual outputName
        bindingName fresh source checks tail checkpoint.rightIdeal checkpoint.bindings
        checkpoint.rightCandidates checkpoint.pc checkpoint.clock checkpoint.enteredAt
        (checkpoint.rightState.trans (by rw [rightPublic])) rightDisclose rightRemembered
        rightAdvanced
      rw [leftEndState] at leftExtends
      rw [rightEndState] at rightExtends
      exact resolveResult_eq_of_endpoint_extends focal outputName tail
        checkpoint.leftIdeal checkpoint.rightIdeal _ _ endSuffix leftEndIdeal rightEndIdeal
        leftEndValues rightEndValues leftEndBindings rightEndBindings leftEndCandidates
        rightEndCandidates leftEndPc leftEndClock leftEndEntered rightEndPc rightEndClock
        rightEndEntered leftExtends rightExtends endVisible

/-- info: 'Vegas.GraphRuntime.FocalReplayCheckpoint.cachedResultsAgree_of_endpoints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.FocalReplayCheckpoint.cachedResultsAgree_of_endpoints

end Vegas.GraphRuntime
