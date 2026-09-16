/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReplayPrefix
import Vegas.Pending.ActionReadout

/-! # Observation locality of reached native deviations -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Δ : VCtx Player L}

private def effectiveOwner : OwnAction Player L → Player
  | .bind owner _ _ _ => owner
  | .resolve owner _ _ => owner

/-- Ordered-prefix form of reached-action locality. -/
theorem reachedOwnActionAtPrefix_eq_of_length_le_pure
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (inputs : FinDist (VEnv L Γ₀))
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player)
    (response : List (Entry runtime) → runtime.application.View → Command runtime)
    (roster : List Player) (rounds : Nat)
    (wireResponse : (List runtime.application.EnvironmentEntry ×
      runtime.application.EnvironmentObservation) → WireCommand Player) :
    let plan := runtime.servicePlan roster rounds whole 0
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile whole profile) focal
      (fun history view => FinDist.pure (response history view))
    let environment := runtime.serviceEnvironment plan
      (fun history view => FinDist.pure (wireResponse (history, view)))
    ∀ {target : VCtx Player L} (suffix : Graph Player L target Δ) (site : Nat)
      (observation : Observation L focal target) (leftAction rightAction : OwnAction Player L)
      (leftBefore rightBefore : List (@MessageApplication.Invocation Player)),
      leftBefore.length ≤ rightBefore.length →
      ReachedOwnActionAtPrefix runtime whole inputs players environment
        (plan.map ServiceInstruction.invocation) leftBefore focal suffix site observation
        leftAction →
      ReachedOwnActionAtPrefix runtime whole inputs players environment
        (plan.map ServiceInstruction.invocation) rightBefore focal suffix site observation
        rightAction →
      leftAction = rightAction := by
  dsimp only
  intro target suffix site observation leftAction rightAction leftBefore rightBefore lengthLe
    leftReached rightReached
  rcases leftReached with
    ⟨leftOwnedAction, leftInput, leftInputMem, leftInstruction, leftRest, leftSplit,
      leftExecution, leftNext, leftExecutionMem, leftNextMem, leftIdeal, leftValues,
      leftBindings, leftCandidates, leftClock, leftEntered, leftState, leftVisible,
      leftRealizes⟩
  rcases rightReached with
    ⟨rightOwnedAction, rightInput, rightInputMem, rightInstruction, rightRest, rightSplit,
      rightExecution, rightNext, rightExecutionMem, rightNextMem, rightIdeal, rightValues,
      rightBindings, rightCandidates, rightClock, rightEntered, rightState, rightVisible,
      rightRealizes⟩
  let plan := runtime.servicePlan roster rounds whole 0
  let players := Profile.update
    (sig := MessageApplication.policySignature Player runtime.application)
    (runtime.compileProfile whole profile) focal
    (fun history view => FinDist.pure (response history view))
  let environment := runtime.serviceEnvironment plan
    (fun history view => FinDist.pure (wireResponse (history, view)))
  obtain ⟨leftServiceBefore, leftServiceInstruction, leftServiceRest, leftPlan,
      leftBeforeEq, leftInstructionEq, leftRestEq⟩ :=
    servicePlan_split_of_mapped_split plan leftBefore leftInstruction leftRest
      (by simpa only [plan] using leftSplit)
  obtain ⟨rightServiceBefore, rightServiceInstruction, rightServiceRest, rightPlan,
      rightBeforeEq, rightInstructionEq, rightRestEq⟩ :=
    servicePlan_split_of_mapped_split plan rightBefore rightInstruction rightRest
      (by simpa only [plan] using rightSplit)
  have serviceLengthLe : leftServiceBefore.length ≤ rightServiceBefore.length := by
    have leftLength := congrArg List.length leftBeforeEq
    have rightLength := congrArg List.length rightBeforeEq
    simp only [List.length_map] at leftLength rightLength
    omega
  obtain ⟨extra, rightBeforeExtension⟩ := schedule_prefix_extension_of_length_le plan
    leftServiceBefore rightServiceBefore leftServiceInstruction rightServiceInstruction
    leftServiceRest rightServiceRest leftPlan rightPlan serviceLengthLe
  have endpointVisible : observe focal leftIdeal = observe focal rightIdeal :=
    leftVisible.trans rightVisible.symm
  have initialVisible : observe focal leftInput = observe focal rightInput := by
    apply runPolicies_endpointObservation_initial_eq runtime focal whole leftInput rightInput
      players players environment environment leftBefore rightBefore leftExecution rightExecution
      suffix leftIdeal rightIdeal leftValues rightValues leftBindings rightBindings leftCandidates
      rightCandidates site leftClock leftEntered site rightClock rightEntered
      leftExecutionMem rightExecutionMem leftState rightState endpointVisible
  let leftInitial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial whole leftInput))
  let rightInitial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial whole rightInput))
  have initialInvariant : NativeReplayInvariant runtime whole focal leftInitial rightInitial :=
    initialNativeReplayInvariant runtime whole focal leftInput rightInput unique discipline
      initialVisible
  have compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor) := by
    intro actor different
    rw [show players actor = runtime.compileProfile whole profile actor by
      simp [players, Profile.update_of_ne _ _ different]]
    rfl
  have pureFocal : players focal =
      fun history view => FinDist.pure (response history view) := by
    simp [players]
  have leftSafe := runtime.servicePlan_unilateralDeviation_expirySafe whole profile leftInput
    unique discipline focal (fun history view => FinDist.pure (response history view)) roster
    rounds (fun history view => FinDist.pure (wireResponse (history, view)))
  have rightSafe := runtime.servicePlan_unilateralDeviation_expirySafe whole profile rightInput
    unique discipline focal (fun history view => FinDist.pure (response history view)) roster
    rounds (fun history view => FinDist.pure (wireResponse (history, view)))
  have leftPrefixSupport : leftExecution ∈
      (runtime.application.runPolicies players environment
        (leftServiceBefore.map ServiceInstruction.invocation) leftInitial).support := by
    simpa only [leftInitial, environment, players, leftBeforeEq] using leftExecutionMem
  have rightPrefixSupport : rightExecution ∈
      (runtime.application.runPolicies players environment
        ((leftServiceBefore ++ extra).map ServiceInstruction.invocation)
        rightInitial).support := by
    have rightMap : (leftServiceBefore ++ extra).map ServiceInstruction.invocation =
        rightBefore := by
      rw [← rightBeforeExtension]
      exact rightBeforeEq
    rw [rightMap]
    simpa only [rightInitial, environment, players] using rightExecutionMem
  have leftOwned := leftRealizes.before_isOwnedBy focal (by
    cases leftAction <;> exact leftOwnedAction)
  have rightOwned := rightRealizes.before_isOwnedBy focal (by
    cases rightAction <;> exact rightOwnedAction)
  obtain ⟨rightBoundary, rightBoundaryMem, rightExtraMem, boundaryInvariant⟩ :=
    initialInvariant.replayPureServicePrefixAgainstExtension runtime whole profile focal response
      players pureFocal compiled plan leftServiceBefore extra
      (leftServiceInstruction :: leftServiceRest)
      (rightServiceInstruction :: rightServiceRest) leftPlan
      (by simpa [rightBeforeExtension, List.append_assoc] using rightPlan)
      wireResponse leftInput rightInput unique discipline
      (by simpa only [plan, players, environment] using leftSafe)
      (by simpa only [plan, players, environment] using rightSafe)
      leftPrefixSupport rightPrefixSupport rfl rfl leftOwned rightOwned suffix leftIdeal
      rightIdeal leftValues rightValues leftBindings rightBindings leftCandidates rightCandidates
      site leftClock leftEntered site rightClock rightEntered leftState rightState endpointVisible
  obtain sameIndex | laterIndex := schedule_prefix_extension_head plan leftServiceBefore
    rightServiceBefore extra leftServiceInstruction rightServiceInstruction leftServiceRest
    rightServiceRest leftPlan rightPlan rightBeforeExtension
  · rcases sameIndex with ⟨rfl, instructionEq⟩
    simp only [List.map_nil, MessageApplication.runPolicies,
      FinDist.mem_support_pure] at rightExtraMem
    subst rightBoundary
    subst rightServiceInstruction
    obtain ⟨cursor, currentSuffix, ⟨checkpoint⟩⟩ :=
      boundaryInvariant.exists_focalReplayCheckpoint
    have leftInvoke : leftNext ∈
        (runtime.application.invoke players environment leftExecution
          leftServiceInstruction.invocation).support := by
      simpa only [environment, players, leftInstructionEq] using leftNextMem
    have rightInvoke : rightNext ∈
        (runtime.application.invoke players environment rightExecution
          leftServiceInstruction.invocation).support := by
      simpa only [environment, players, rightInstructionEq] using rightNextMem
    have nextInvariant := boundaryInvariant.focalOwned_invoke runtime whole profile focal
      checkpoint players compiled response pureFocal plan wireResponse leftInput rightInput unique
      discipline (leftServiceBefore.map ServiceInstruction.invocation)
      (leftServiceBefore.map ServiceInstruction.invocation) leftPrefixSupport
      (by simpa only [rightInitial, environment, players] using rightBoundaryMem) leftOwned
      leftServiceInstruction.invocation leftInvoke rightInvoke
    have nextView := congrArg Prod.fst nextInvariant.focalKey
    have leftRealizes' : State.RealizesOwnAction
        (.running suffix leftIdeal leftValues leftBindings leftCandidates site leftClock
          leftEntered) leftAction leftNext.native.application := by
      rw [← leftState]
      exact leftRealizes
    have rightRealizes' : State.RealizesOwnAction
        (.running suffix rightIdeal rightValues rightBindings rightCandidates site rightClock
          rightEntered) rightAction rightNext.native.application := by
      rw [← rightState]
      exact rightRealizes
    exact State.RealizesOwnAction.eq_of_playerView_eq focal suffix leftIdeal rightIdeal leftValues
      rightValues leftBindings rightBindings leftCandidates rightCandidates site leftClock
      leftEntered site rightClock rightEntered leftNext.native.application
      rightNext.native.application leftAction rightAction leftRealizes' rightRealizes'
      (by cases leftAction <;> exact leftOwnedAction)
      (by cases rightAction <;> exact rightOwnedAction) nextView
  · obtain ⟨extraTail, rfl⟩ := laterIndex
    simp only [List.map_cons, MessageApplication.runPolicies, FinDist.support_bind,
      Set.mem_iUnion] at rightExtraMem
    obtain ⟨rightMiddle, rightMiddleInvoke, rightMiddleResidual⟩ := rightExtraMem
    obtain ⟨cursor, currentSuffix, ⟨checkpoint⟩⟩ :=
      boundaryInvariant.exists_focalReplayCheckpoint
    have leftInvoke : leftNext ∈
        (runtime.application.invoke players environment leftExecution
          leftServiceInstruction.invocation).support := by
      simpa only [environment, players, leftInstructionEq] using leftNextMem
    have nextInvariant := boundaryInvariant.focalOwned_invoke runtime whole profile focal
      checkpoint players compiled response pureFocal plan wireResponse leftInput rightInput unique
      discipline (leftServiceBefore.map ServiceInstruction.invocation)
      (leftServiceBefore.map ServiceInstruction.invocation) leftPrefixSupport rightBoundaryMem
      leftOwned leftServiceInstruction.invocation leftInvoke rightMiddleInvoke
    exact (phase_change_forbids_same_phase_residual runtime players environment
      (extraTail.map ServiceInstruction.invocation) site leftNext rightMiddle rightExecution
      (by simpa only [leftState, State.phase] using leftRealizes.phase_lt)
      nextInvariant.phase rightMiddleResidual (by simp only [rightState, State.phase])).elim

/-- In initialized executions with deterministic focal and service responses,
the normalized focal action reached at a graph observation is unique. -/
theorem servicePlan_reachedOwnAction_locality_pure
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (inputs : FinDist (VEnv L Γ₀))
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (focal : Player)
    (response : List (Entry runtime) → runtime.application.View → Command runtime)
    (roster : List Player) (rounds : Nat)
    (wireResponse : (List runtime.application.EnvironmentEntry ×
      runtime.application.EnvironmentObservation) → WireCommand Player) :
    let plan := runtime.servicePlan roster rounds whole 0
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile whole profile) focal
      (fun history view => FinDist.pure (response history view))
    let environment := runtime.serviceEnvironment plan
      (fun history view => FinDist.pure (wireResponse (history, view)))
    ∀ {target : VCtx Player L} (suffix : Graph Player L target Δ) (site : Nat)
      (observation : Observation L focal target) (leftAction rightAction : OwnAction Player L),
      ReachedOwnAction runtime whole inputs players environment
        (plan.map ServiceInstruction.invocation) focal suffix site observation leftAction →
      ReachedOwnAction runtime whole inputs players environment
        (plan.map ServiceInstruction.invocation) focal suffix site observation rightAction →
      leftAction = rightAction := by
  dsimp only
  intro target suffix site observation leftAction rightAction leftReached rightReached
  rw [reachedOwnAction_iff_exists_atPrefix] at leftReached rightReached
  obtain ⟨leftBefore, leftReached⟩ := leftReached
  obtain ⟨rightBefore, rightReached⟩ := rightReached
  rcases Nat.le_total leftBefore.length rightBefore.length with ordered | ordered
  · exact runtime.reachedOwnActionAtPrefix_eq_of_length_le_pure whole profile inputs unique
      discipline focal response roster rounds wireResponse suffix site observation leftAction
      rightAction leftBefore rightBefore ordered leftReached rightReached
  · exact (runtime.reachedOwnActionAtPrefix_eq_of_length_le_pure whole profile inputs unique
      discipline focal response roster rounds wireResponse suffix site observation rightAction
      leftAction rightBefore leftBefore ordered rightReached leftReached).symm

end Vegas.GraphRuntime
