/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReplayService
import Vegas.Pending.ReplayDisclosure
import Vegas.Pending.DeviationReachedLocality

/-! # Concrete endpoint-conditioned replay of service prefixes -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Δ : VCtx Player L}

theorem NativeReplayInvariant.replayPureServicePrefixAgainstExtension
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    (response : List (Entry runtime) → runtime.application.View → Command runtime)
    (players : Player → runtime.application.PlayerPolicy)
    (pureFocal : players focal = fun history view => FinDist.pure (response history view))
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (plan common extra leftTail rightTail : List (ServiceInstruction Player))
    (leftPlan : plan = common ++ leftTail)
    (rightPlan : plan = common ++ extra ++ rightTail)
    (wireResponse : (List runtime.application.EnvironmentEntry ×
      runtime.application.EnvironmentObservation) → WireCommand Player)
    (leftInput rightInput : VEnv L Γ₀) (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (leftSafe : DeviationExpirySafe runtime players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) (some focal) plan
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole leftInput))))
    (rightSafe : DeviationExpirySafe runtime players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) (some focal) plan
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole rightInput))))
    {leftInitial rightInitial leftBoundary rightFinal : runtime.application.PolicyExecution}
    (initial : NativeReplayInvariant runtime whole focal leftInitial rightInitial)
    (leftSupported : leftBoundary ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view))))
      (common.map ServiceInstruction.invocation) leftInitial).support)
    (rightSupported : rightFinal ∈ (runtime.application.runPolicies players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view))))
      ((common ++ extra).map ServiceInstruction.invocation) rightInitial).support)
    (leftInitialEq : leftInitial = MessageApplication.PolicyExecution.initial
      runtime.application (MessageApplication.State.initial runtime.application
        (State.initial whole leftInput)))
    (rightInitialEq : rightInitial = MessageApplication.PolicyExecution.initial
      runtime.application (MessageApplication.State.initial runtime.application
        (State.initial whole rightInput)))
    (leftOwned : leftBoundary.native.application.IsOwnedBy (some focal))
    (rightOwned : rightFinal.native.application.IsOwnedBy (some focal))
    {target : VCtx Player L} (endSuffix : Graph Player L target Δ)
    (leftIdeal rightIdeal : VEnv L target)
    (leftValues rightValues : PublicValues target)
    (leftBindings rightBindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftPc leftClock leftEntered rightPc rightClock rightEntered : Nat)
    (leftState : leftBoundary.native.application = .running endSuffix leftIdeal leftValues
      leftBindings leftCandidates leftPc leftClock leftEntered)
    (rightState : rightFinal.native.application = .running endSuffix rightIdeal rightValues
      rightBindings rightCandidates rightPc rightClock rightEntered)
    (visible : observe focal leftIdeal = observe focal rightIdeal) :
    ∃ rightBoundary,
      rightBoundary ∈ (runtime.application.runPolicies players
        (runtime.serviceEnvironment plan (fun history view =>
          FinDist.pure (wireResponse (history, view))))
        (common.map ServiceInstruction.invocation) rightInitial).support ∧
      rightFinal ∈ (runtime.application.runPolicies players
        (runtime.serviceEnvironment plan (fun history view =>
          FinDist.pure (wireResponse (history, view))))
        (extra.map ServiceInstruction.invocation) rightBoundary).support ∧
      NativeReplayInvariant runtime whole focal leftBoundary rightBoundary := by
  let environment := runtime.serviceEnvironment plan (fun history view =>
    FinDist.pure (wireResponse (history, view)))
  apply initial.runServicePlan_prefix_against_extension players environment common extra
    leftSupported rightSupported
  intro processed instruction rest leftCurrent rightCurrent leftNext rightNext split invariant
    leftReached rightReached leftInvoke rightInvoke leftResidual rightResidual
  obtain ⟨cursor, suffix, ⟨checkpoint⟩⟩ := invariant.exists_focalReplayCheckpoint
  have leftReachedInitial : leftCurrent ∈ (runtime.application.runPolicies players environment
      (processed.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))).support := by
    simpa only [leftInitialEq] using leftReached
  have rightReachedInitial : rightCurrent ∈ (runtime.application.runPolicies players environment
      (processed.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput)))).support := by
    simpa only [rightInitialEq] using rightReached
  cases instruction with
  | player actor =>
      have leftAgreement := runtime.runPolicies_preserves_publicAgreement players environment
        (processed.map ServiceInstruction.invocation) _ leftCurrent
        (State.initial_publicAgreement whole leftInput) leftReachedInitial
      have rightAgreement := runtime.runPolicies_preserves_publicAgreement players environment
        (processed.map ServiceInstruction.invocation) _ rightCurrent
        (State.initial_publicAgreement whole rightInput) rightReachedInitial
      apply invariant.player_invoke suffix checkpoint profile players compiled response pureFocal
        environment actor leftAgreement rightAgreement
      · intro different
        have leftSegmentRun : leftBoundary ∈ (runtime.application.runPolicies players environment
            ((ServiceInstruction.player actor :: rest).map ServiceInstruction.invocation)
            leftCurrent).support := by
          simp only [List.map_cons, MessageApplication.runPolicies, FinDist.support_bind,
            Set.mem_iUnion]
          exact ⟨leftNext, leftInvoke, leftResidual⟩
        have rightSegmentRun : rightFinal ∈ (runtime.application.runPolicies players environment
            ((ServiceInstruction.player actor :: (rest ++ extra)).map
              ServiceInstruction.invocation) rightCurrent).support := by
          simp only [List.map_cons, MessageApplication.runPolicies, FinDist.support_bind,
            Set.mem_iUnion]
          exact ⟨rightNext, rightInvoke, rightResidual⟩
        apply checkpoint.cachedResultsAgree_of_endpoints runtime whole leftInput rightInput unique
          discipline focal actor different (profile actor) players (compiled actor different)
          (fun history view => FinDist.pure (wireResponse (history, view))) plan processed
          (ServiceInstruction.player actor :: rest)
          (ServiceInstruction.player actor :: (rest ++ extra)) leftTail rightTail
        · simpa [split, List.append_assoc] using leftPlan
        · simpa [split, List.append_assoc] using rightPlan
        · exact leftSafe
        · exact rightSafe
        · exact leftReachedInitial
        · exact rightReachedInitial
        · exact leftSegmentRun
        · exact rightSegmentRun
        · exact leftOwned
        · exact rightOwned
        · exact leftState
        · exact rightState
        · exact visible
      · exact leftInvoke
      · exact rightInvoke
  | wire | includeLatest _ | expire _ =>
      apply invariant.pureServiceEnvironment_afterInvoke runtime whole profile focal checkpoint
        players compiled plan wireResponse leftInput rightInput unique discipline
        (processed.map ServiceInstruction.invocation)
        (processed.map ServiceInstruction.invocation)
        leftReachedInitial rightReachedInitial leftInvoke rightInvoke
        (rest.map ServiceInstruction.invocation)
        ((rest ++ extra).map ServiceInstruction.invocation) leftBoundary rightFinal endSuffix
        leftIdeal rightIdeal leftValues rightValues leftBindings rightBindings leftCandidates
        rightCandidates leftPc leftClock leftEntered rightPc rightClock rightEntered leftResidual
        rightResidual leftState rightState visible

end Vegas.GraphRuntime
