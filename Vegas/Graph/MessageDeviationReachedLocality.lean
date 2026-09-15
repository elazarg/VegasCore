/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationPrefixLocality
import Vegas.Graph.MessageReplayInvocation
import Vegas.Graph.MessageReplayService

/-! # Reached-action locality for the concrete service plan -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Δ : VCtx Player L}

/-- A reached effective action with its concrete schedule prefix exposed. -/
def ReachedOwnActionAtPrefix (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule before : List (@MessageApplication.Invocation Player)) (focal : Player)
    {Γ : VCtx Player L} (suffix : Graph Player L Γ Δ) (site : Nat)
    (observation : Observation L focal Γ) (action : OwnAction Player L) : Prop :=
  (match action with
    | .bind owner _ _ _ => owner = focal
    | .resolve owner _ _ => owner = focal) ∧
  ∃ input ∈ inputs.support, ∃ instruction rest,
    schedule = before ++ instruction :: rest ∧
    ∃ execution next : runtime.application.PolicyExecution,
      execution ∈ (runtime.application.runPolicies players environment before
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole input)))).support ∧
      next ∈ (runtime.application.invoke players environment execution instruction).support ∧
      ∃ ideal values bindings candidates clock enteredAt,
        execution.native.application =
          .running suffix ideal values bindings candidates site clock enteredAt ∧
        observe focal ideal = observation ∧
        State.RealizesOwnAction execution.native.application action next.native.application

/-- Exposing the invocation prefix loses no information from `ReachedOwnAction`. -/
theorem reachedOwnAction_iff_exists_atPrefix
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    {Γ : VCtx Player L} (suffix : Graph Player L Γ Δ) (site : Nat)
    (observation : Observation L focal Γ) (action : OwnAction Player L) :
    ReachedOwnAction runtime whole inputs players environment schedule focal suffix site
        observation action ↔
      ∃ before, ReachedOwnActionAtPrefix runtime whole inputs players environment schedule before
        focal suffix site observation action := by
  unfold ReachedOwnAction ReachedOwnActionAtPrefix
  constructor
  · rintro ⟨owned, input, inputMem, before, instruction, rest, split, execution, next,
      reached, invoked, ideal, values, bindings, candidates, clock, enteredAt, state,
      visible, realizes⟩
    exact ⟨before, owned, input, inputMem, instruction, rest, split, execution, next,
      reached, invoked, ideal, values, bindings, candidates, clock, enteredAt, state,
      visible, realizes⟩
  · rintro ⟨before, owned, input, inputMem, instruction, rest, split, execution, next,
      reached, invoked, ideal, values, bindings, candidates, clock, enteredAt, state,
      visible, realizes⟩
    exact ⟨owned, input, inputMem, before, instruction, rest, split, execution, next,
      reached, invoked, ideal, values, bindings, candidates, clock, enteredAt, state,
      visible, realizes⟩

omit [DecidableEq Player] in
/-- Lift a split of the mapped invocation schedule back to the concrete
service instruction at that position.  No injectivity of `invocation` is
needed. -/
theorem servicePlan_split_of_mapped_split
    (plan : List (ServiceInstruction Player))
    (before : List (@MessageApplication.Invocation Player))
    (instruction : @MessageApplication.Invocation Player)
    (rest : List (@MessageApplication.Invocation Player))
    (split : plan.map ServiceInstruction.invocation = before ++ instruction :: rest) :
    ∃ serviceBefore serviceInstruction serviceRest,
      plan = serviceBefore ++ serviceInstruction :: serviceRest ∧
      serviceBefore.map ServiceInstruction.invocation = before ∧
      serviceInstruction.invocation = instruction ∧
      serviceRest.map ServiceInstruction.invocation = rest := by
  rw [List.map_eq_append_iff] at split
  obtain ⟨serviceBefore, tail, planEq, beforeEq, tailEq⟩ := split
  rw [List.map_eq_cons_iff] at tailEq
  obtain ⟨serviceInstruction, serviceRest, tailSplit, instructionEq, restEq⟩ := tailEq
  subst tail
  exact ⟨serviceBefore, serviceInstruction, serviceRest, planEq, beforeEq,
    instructionEq, restEq⟩

namespace NativeReplayInvariant

/-- Replay a shorter service-instruction prefix against the corresponding
prefix of a longer run.  The induction retains the un-erased service
instruction split required by expiry safety and compiled-packet provenance;
the runner itself receives the mapped invocation schedule. -/
theorem runServicePlan_prefix_against_extension
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (common extra : List (ServiceInstruction Player))
    {leftInitial rightInitial leftBoundary rightFinal :
      runtime.application.PolicyExecution}
    (initial : NativeReplayInvariant runtime whole focal leftInitial rightInitial)
    (leftSupported : leftBoundary ∈
      (runtime.application.runPolicies players environment
        (common.map ServiceInstruction.invocation) leftInitial).support)
    (rightSupported : rightFinal ∈
      (runtime.application.runPolicies players environment
        ((common ++ extra).map ServiceInstruction.invocation) rightInitial).support)
    (step : ∀ (processed : List (ServiceInstruction Player)) instruction rest
      (leftCurrent rightCurrent leftNext rightNext : runtime.application.PolicyExecution),
      common = processed ++ instruction :: rest →
      NativeReplayInvariant runtime whole focal leftCurrent rightCurrent →
      leftCurrent ∈
        (runtime.application.runPolicies players environment
          (processed.map ServiceInstruction.invocation) leftInitial).support →
      rightCurrent ∈
        (runtime.application.runPolicies players environment
          (processed.map ServiceInstruction.invocation) rightInitial).support →
      leftNext ∈ (runtime.application.invoke players environment leftCurrent
        instruction.invocation).support →
      rightNext ∈ (runtime.application.invoke players environment rightCurrent
        instruction.invocation).support →
      leftBoundary ∈
        (runtime.application.runPolicies players environment
          (rest.map ServiceInstruction.invocation) leftNext).support →
      rightFinal ∈
        (runtime.application.runPolicies players environment
          ((rest ++ extra).map ServiceInstruction.invocation) rightNext).support →
      NativeReplayInvariant runtime whole focal leftNext rightNext) :
    ∃ rightBoundary,
      rightBoundary ∈
        (runtime.application.runPolicies players environment
          (common.map ServiceInstruction.invocation) rightInitial).support ∧
      rightFinal ∈
        (runtime.application.runPolicies players environment
          (extra.map ServiceInstruction.invocation) rightBoundary).support ∧
      NativeReplayInvariant runtime whole focal leftBoundary rightBoundary := by
  rw [List.map_append, runtime.application.runPolicies_append] at rightSupported
  simp only [FinDist.support_bind, Set.mem_iUnion] at rightSupported
  obtain ⟨rightBoundary, rightPrefix, rightExtra⟩ := rightSupported
  refine ⟨rightBoundary, rightPrefix, rightExtra, ?_⟩
  have replay : ∀ (processed remaining : List (ServiceInstruction Player))
      (leftCurrent rightCurrent : runtime.application.PolicyExecution),
      common = processed ++ remaining →
      NativeReplayInvariant runtime whole focal leftCurrent rightCurrent →
      leftCurrent ∈
        (runtime.application.runPolicies players environment
          (processed.map ServiceInstruction.invocation) leftInitial).support →
      rightCurrent ∈
        (runtime.application.runPolicies players environment
          (processed.map ServiceInstruction.invocation) rightInitial).support →
      leftBoundary ∈
        (runtime.application.runPolicies players environment
          (remaining.map ServiceInstruction.invocation) leftCurrent).support →
      rightBoundary ∈
        (runtime.application.runPolicies players environment
          (remaining.map ServiceInstruction.invocation) rightCurrent).support →
      NativeReplayInvariant runtime whole focal leftBoundary rightBoundary := by
    intro processed remaining
    induction remaining generalizing processed with
    | nil =>
        intro leftCurrent rightCurrent _ invariant _ _ leftTail rightTail
        simp only [List.map_nil, MessageApplication.runPolicies,
          FinDist.mem_support_pure] at leftTail rightTail
        subst leftBoundary
        subst rightBoundary
        exact invariant
    | cons instruction rest ih =>
        intro leftCurrent rightCurrent split invariant leftReached rightReached
          leftTail rightTail
        simp only [List.map_cons, MessageApplication.runPolicies, FinDist.support_bind,
          Set.mem_iUnion] at leftTail rightTail
        obtain ⟨leftNext, leftInvoke, leftResidual⟩ := leftTail
        obtain ⟨rightNext, rightInvoke, rightResidual⟩ := rightTail
        have rightUltimate : rightFinal ∈
            (runtime.application.runPolicies players environment
              ((rest ++ extra).map ServiceInstruction.invocation) rightNext).support := by
          rw [List.map_append, runtime.application.runPolicies_append]
          simp only [FinDist.support_bind, Set.mem_iUnion]
          exact ⟨rightBoundary, rightResidual, rightExtra⟩
        have nextInvariant := step processed instruction rest leftCurrent rightCurrent
          leftNext rightNext split invariant leftReached rightReached leftInvoke rightInvoke
            leftResidual rightUltimate
        have leftNextReached : leftNext ∈
            (runtime.application.runPolicies players environment
              ((processed ++ [instruction]).map ServiceInstruction.invocation)
              leftInitial).support := by
          rw [List.map_append, runtime.application.runPolicies_append]
          simp only [List.map_cons, List.map_nil, FinDist.support_bind, Set.mem_iUnion,
            MessageApplication.runPolicies]
          exact ⟨leftCurrent, leftReached, leftNext, leftInvoke, by simp⟩
        have rightNextReached : rightNext ∈
            (runtime.application.runPolicies players environment
              ((processed ++ [instruction]).map ServiceInstruction.invocation)
              rightInitial).support := by
          rw [List.map_append, runtime.application.runPolicies_append]
          simp only [List.map_cons, List.map_nil, FinDist.support_bind, Set.mem_iUnion,
            MessageApplication.runPolicies]
          exact ⟨rightCurrent, rightReached, rightNext, rightInvoke, by simp⟩
        apply ih (processed ++ [instruction]) leftNext rightNext
          (by simpa [List.append_assoc] using split) nextInvariant
          leftNextReached rightNextReached leftResidual rightResidual
  apply replay [] common leftInitial rightInitial
  · simp
  · exact initial
  · simp [MessageApplication.runPolicies]
  · simp [MessageApplication.runPolicies]
  · exact leftSupported
  · exact rightPrefix

end NativeReplayInvariant

/-- Once the paired invocation on the shorter run advances, phase monotonicity
prevents the longer run from consuming any nonempty residual and returning to
the same pre-action phase. -/
theorem phase_change_forbids_same_phase_residual
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (rest : List (@MessageApplication.Invocation Player))
    (site : Nat)
    (leftNext rightNext rightEnd : runtime.application.PolicyExecution)
    (leftAdvanced : site < leftNext.native.application.phase)
    (pairedPhase : leftNext.native.application.phase = rightNext.native.application.phase)
    (rightResidual : rightEnd ∈
      (runtime.application.runPolicies players environment rest rightNext).support)
    (rightEndPhase : rightEnd.native.application.phase = site) : False := by
  have monotone := runtime.runPolicies_phase_mono players environment rest rightNext rightEnd
    rightResidual
  omega

/-- Every realized source action is an actual one-phase graph advance. -/
theorem State.RealizesOwnAction.phase_lt
    {before after : State Player L Δ} {action : OwnAction Player L}
    (realizes : State.RealizesOwnAction before action after) :
    before.phase < after.phase := by
  cases realizes <;> simp only [State.phase] <;> omega

/-- At a focal-owned decision cursor, one paired actual invocation replays
without any future endpoint premise.  A nonfocal compiled player cannot be the
node owner there, and an environment tick is necessarily non-sample. -/
theorem NativeReplayInvariant.focalOwned_invoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    {Γ : VCtx Player L} {suffix : Graph Player L Γ Δ}
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right)
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (response : List (Entry runtime) → runtime.application.View → Command runtime)
    (pureFocal : players focal = fun history view => FinDist.pure (response history view))
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
    (leftOwned : left.native.application.IsOwnedBy (some focal))
    (invocation : @MessageApplication.Invocation Player)
    (leftSupported : leftNext ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) left invocation).support)
    (rightSupported : rightNext ∈ (runtime.application.invoke players
      (runtime.serviceEnvironment plan (fun history view =>
        FinDist.pure (wireResponse (history, view)))) right invocation).support) :
    NativeReplayInvariant runtime whole focal leftNext rightNext := by
  let service := runtime.serviceEnvironment plan (fun history view =>
    FinDist.pure (wireResponse (history, view)))
  have leftAgreement := runtime.runPolicies_preserves_publicAgreement players service leftPrefix
    _ left (State.initial_publicAgreement whole leftInput) leftReached
  have rightAgreement := runtime.runPolicies_preserves_publicAgreement players service rightPrefix
    _ right (State.initial_publicAgreement whole rightInput) rightReached
  cases invocation with
  | player actor =>
      refine invariant.player_invoke suffix checkpoint profile players compiled response pureFocal
        service actor leftAgreement rightAgreement ?_ leftSupported rightSupported
      intro different
      cases suffix with
      | ret | sample | bind => trivial
      | resolve outputName owner bindingName fresh source checks tail =>
          intro ownerEq
          subst owner
          have ownedFocal : actor = focal := by
            have same : focal = actor := by
              simpa only [checkpoint.leftState, State.IsOwnedBy,
                Option.some.injEq] using leftOwned
            exact same.symm
          exact (different ownedFocal).elim
  | environment =>
      have notSample : ¬ ∃ (name : VarId) (payload : L.Ty)
          (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
          (tail : Graph Player L ((name, .pub payload) :: Γ) Δ),
          suffix = .sample name fresh law tail := by
        rintro ⟨name, payload, fresh, law, tail, rfl⟩
        simp only [checkpoint.leftState, State.IsOwnedBy] at leftOwned
      exact invariant.pureServiceEnvironment_nonsample_afterInvoke runtime whole profile focal
        checkpoint notSample players compiled plan wireResponse leftInput rightInput unique
        discipline leftPrefix rightPrefix leftReached rightReached leftSupported rightSupported

end Vegas.GraphRuntime
