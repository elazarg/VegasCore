/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReplayApplication
import Vegas.Pending.ReplayHistory
import Vegas.Pending.ReplayPlayer
import Vegas.Pending.ReachedActions
import Vegas.Pending.ResolveEndpoint

/-! # Endpoint-conditioned replay of a native deviation

This module couples two actual initialized prefixes of the fixed service
schedule.  Foreign source draws remain independent; only cache shape and the
traffic exposed to the focal player and service are synchronized.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

namespace Prefix

/-- A graph has only one typed cursor at a fixed constructor depth.  The
dependent pair formulation is what lets raw service replay recover one common
suffix from two independent `Follows` witnesses. -/
theorem cursor_eq_of_same_length
    {whole : Graph Player L Γ₀ Δ} {leftTarget rightTarget : VCtx Player L}
    {leftSuffix : Graph Player L leftTarget Δ}
    {rightSuffix : Graph Player L rightTarget Δ} {length : Nat}
    (left : Prefix Δ whole leftSuffix length)
    (right : Prefix Δ whole rightSuffix length) :
    (⟨leftTarget, leftSuffix⟩ : Sigma fun target => Graph Player L target Δ) =
      ⟨rightTarget, rightSuffix⟩ := by
  induction left generalizing rightTarget rightSuffix with
  | refl => cases right; rfl
  | sample left ih =>
      cases right with
      | sample right => exact ih right
  | bind left ih =>
      cases right with
      | bind right => exact ih right
  | resolve left ih =>
      cases right with
      | resolve right => exact ih right

end Prefix

/-- Two strict prefixes of one finite invocation schedule are comparable by
length.  This turns the two existential `ReachedOwnAction` splits into the
common-prefix/extension shape used by replay. -/
theorem schedule_prefix_extension_of_length_le
    {α : Type} (schedule left right : List α) (leftHead rightHead : α)
    (leftRest rightRest : List α)
    (leftSplit : schedule = left ++ leftHead :: leftRest)
    (rightSplit : schedule = right ++ rightHead :: rightRest)
    (lengthLe : left.length ≤ right.length) :
    ∃ extra, right = left ++ extra := by
  have leftTake : schedule.take left.length = left := by
    rw [leftSplit]
    simp
  have rightTake : schedule.take left.length = right.take left.length := by
    rw [rightSplit]
    simp [lengthLe]
  have prefixEq : right.take left.length = left := rightTake.symm.trans leftTake
  refine ⟨right.drop left.length, ?_⟩
  calc
    right = right.take left.length ++ right.drop left.length :=
      (List.take_append_drop left.length right).symm
    _ = left ++ right.drop left.length := by rw [prefixEq]

/-- If the longer action prefix genuinely extends the shorter one, its first
extra invocation is exactly the shorter witness's advancing invocation. -/
theorem schedule_prefix_extension_head
    {α : Type} (schedule left right extra : List α) (leftHead rightHead : α)
    (leftRest rightRest : List α)
    (leftSplit : schedule = left ++ leftHead :: leftRest)
    (rightSplit : schedule = right ++ rightHead :: rightRest)
    (extensionEq : right = left ++ extra) :
    (extra = [] ∧ leftHead = rightHead) ∨
      ∃ tail, extra = leftHead :: tail := by
  have sameTail : leftHead :: leftRest = extra ++ rightHead :: rightRest := by
    apply List.append_right_injective left
    change left ++ leftHead :: leftRest = left ++ (extra ++ rightHead :: rightRest)
    calc
      left ++ leftHead :: leftRest = schedule := leftSplit.symm
      _ = right ++ rightHead :: rightRest := rightSplit
      _ = left ++ (extra ++ rightHead :: rightRest) := by
        rw [extensionEq, List.append_assoc]
  cases extra with
  | nil =>
      left
      simp only [List.nil_append] at sameTail
      exact ⟨rfl, List.cons.inj sameTail |>.1⟩
  | cons head tail =>
      right
      simp only [List.cons_append, List.cons.injEq] at sameTail
      exact ⟨tail, congrArg (fun value => value :: tail) sameTail.1.symm⟩

/-- Two cached resolve results retained by later endpoints are equal whenever
those endpoints have the same focal observation. -/
theorem resolveResult_eq_of_endpoint_extends
    (focal : Player)
    (outputName : VarId) {payload : L.Ty}
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (leftIdeal rightIdeal : VEnv L Γ)
    (leftResult rightResult : PublicationResult (L.Val payload))
    {target : VCtx Player L} (suffix : Graph Player L target Δ)
    (leftEnd rightEnd : VEnv L target)
    (leftValues rightValues : PublicValues target)
    (leftBindings rightBindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftPc leftClock leftEntered rightPc rightClock rightEntered : Nat)
    (leftExtends :
      (State.running suffix leftEnd leftValues leftBindings leftCandidates
        leftPc leftClock leftEntered).Extends tail
        (VEnv.cons ((R.valueEquiv payload).symm leftResult) leftIdeal))
    (rightExtends :
      (State.running suffix rightEnd rightValues rightBindings rightCandidates
        rightPc rightClock rightEntered).Extends tail
        (VEnv.cons ((R.valueEquiv payload).symm rightResult) rightIdeal))
    (visible : observe focal leftEnd = observe focal rightEnd) :
    leftResult = rightResult := by
  have earlier := endpointObservation_restricts_to_cursor focal tail
    (VEnv.cons ((R.valueEquiv payload).symm leftResult) leftIdeal)
    (VEnv.cons ((R.valueEquiv payload).symm rightResult) rightIdeal)
    suffix leftEnd rightEnd leftValues rightValues leftBindings rightBindings
    leftCandidates rightCandidates leftPc leftClock leftEntered rightPc rightClock
    rightEntered leftExtends rightExtends visible
  have publicEq := Graph.publicValues_eq_of_observe_eq focal _ _ earlier
  have encodedEq := congrArg
    (fun values : PublicValues ((outputName, .pub (R.result payload)) :: Γ) =>
      values (.here : HasVar ((outputName, .pub (R.result payload)) :: Γ)
        outputName (.pub (R.result payload)))) publicEq
  exact (R.valueEquiv payload).symm.injective encodedEq

/-- The proof state retained by the whole-prefix replay induction. -/
structure PrefixReplayInvariant (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (focal : Player)
    {Γ : VCtx Player L} (suffix : Graph Player L Γ Δ)
    (left right : runtime.application.PolicyExecution) : Type where
  checkpoint : FocalReplayCheckpoint runtime focal suffix left right
  cacheShape : ∀ owner, owner ≠ focal →
    CacheShape (left.principalHistory owner) (right.principalHistory owner)
  leftFollows : left.native.application.Follows whole 0
  rightFollows : right.native.application.Follows whole 0
  leftSound : left.native.application.BindingSoundness
  rightSound : right.native.application.BindingSoundness
  leftProvenance : left.native.application.DisciplinedBindingProvenance
  rightProvenance : right.native.application.DisciplinedBindingProvenance

/-- Cursor-independent form used while replaying the raw service schedule.
The common typed suffix is reconstructed only at graph checkpoints. -/
structure NativeReplayInvariant (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (focal : Player)
    (left right : runtime.application.PolicyExecution) : Prop where
  phase : left.native.application.phase = right.native.application.phase
  focalKey : left.native.application.focalReplayKey focal =
    right.native.application.focalReplayKey focal
  environmentView :
    MessageApplication.State.environmentView runtime.application left.native =
      MessageApplication.State.environmentView runtime.application right.native
  focalHistory : left.principalHistory focal = right.principalHistory focal
  environmentHistory : left.environmentHistory = right.environmentHistory
  cacheShape : ∀ owner, owner ≠ focal →
    CacheShape (left.principalHistory owner) (right.principalHistory owner)
  leftFollows : left.native.application.Follows whole 0
  rightFollows : right.native.application.Follows whole 0
  leftSound : left.native.application.BindingSoundness
  rightSound : right.native.application.BindingSoundness
  leftProvenance : left.native.application.DisciplinedBindingProvenance
  rightProvenance : right.native.application.DisciplinedBindingProvenance

/-- A fixed pure focal response selects the same concrete command at a
synchronized checkpoint.  The resulting invocation preserves every
observable replay field and every foreign cache shape. -/
theorem FocalReplayCheckpoint.focal_pure_invoke_replay
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {suffix : Graph Player L Γ Δ}
    (response : List (Entry runtime) → MessageApplication.View runtime.application →
      Command runtime)
    (players : Player → runtime.application.PlayerPolicy)
    (pureFocal : players focal = fun history view => FinDist.pure (response history view))
    (environment : runtime.application.EnvironmentPolicy)
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (shapes : ∀ owner, owner ≠ focal →
      CacheShape (left.principalHistory owner) (right.principalHistory owner))
    (leftSupported : leftNext ∈
      (runtime.application.invoke players environment left (.player focal)).support)
    (rightSupported : rightNext ∈
      (runtime.application.invoke players environment right (.player focal)).support) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      leftNext.native.application.focalReplayKey focal =
        rightNext.native.application.focalReplayKey focal ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native ∧
      ∀ owner, owner ≠ focal →
        CacheShape (leftNext.principalHistory owner) (rightNext.principalHistory owner) := by
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftSupported rightSupported
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftSupported
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightSupported
  rw [pureFocal, FinDist.mem_support_pure] at leftChosen rightChosen
  have inputEq := checkpoint.focalServiceInput_eq
  have responseEq : response (left.principalHistory focal)
      (MessageApplication.State.observe runtime.application left.native focal) =
    response (right.principalHistory focal)
      (MessageApplication.State.observe runtime.application right.native focal) := by
    exact congrArg (fun input => response input.1.1 input.1.2) inputEq
  subst leftCommand
  rw [responseEq] at leftStep
  subst rightCommand
  obtain ⟨focalHistory, environmentHistory, focalKey, environmentView⟩ :=
    checkpoint.focal_playerStep_replay runtime focal _ leftStep rightStep
  refine ⟨focalHistory, environmentHistory, focalKey, environmentView, ?_⟩
  intro owner different
  rw [runtime.application.playerStep_other_history focal owner different left _ leftNext
      leftStep,
    runtime.application.playerStep_other_history focal owner different right _ rightNext
      rightStep]
  exact shapes owner different

/-- Equal focal initial observations seed every component of prefix replay.
The two foreign private initial environments remain unrelated. -/
def initialPrefixReplayInvariant
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (focal : Player) (leftInput rightInput : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (visible : observe focal leftInput = observe focal rightInput) :
    PrefixReplayInvariant runtime whole focal whole
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput))) :=
  { checkpoint := initialFocalReplayCheckpoint runtime whole focal leftInput rightInput visible
    cacheShape := fun _ _ => CacheShape.refl []
    leftFollows := State.initial_follows whole leftInput
    rightFollows := State.initial_follows whole rightInput
    leftSound := State.initial_bindingSoundness whole leftInput unique
    rightSound := State.initial_bindingSoundness whole rightInput unique
    leftProvenance := State.initial_disciplinedBindingProvenance whole leftInput unique discipline
    rightProvenance :=
      State.initial_disciplinedBindingProvenance whole rightInput unique discipline }

namespace PrefixReplayInvariant

/-- Forget the dependent graph cursor while retaining every input and
certificate required by schedule replay. -/
theorem toNative
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} {suffix : Graph Player L Γ Δ}
    {left right : runtime.application.PolicyExecution}
    (invariant : PrefixReplayInvariant runtime whole focal suffix left right) :
    NativeReplayInvariant runtime whole focal left right := by
  have inputEq := invariant.checkpoint.focalServiceInput_eq
  have environmentView := congrArg Prod.snd (congrArg Prod.snd inputEq)
  change MessageApplication.State.environmentView runtime.application left.native =
    MessageApplication.State.environmentView runtime.application right.native
    at environmentView
  have focalView := congrArg Prod.snd (congrArg Prod.fst inputEq)
  change MessageApplication.State.observe runtime.application left.native focal =
    MessageApplication.State.observe runtime.application right.native focal at focalView
  have playerView := congrArg MessageInterface.View.application focalView
  have candidateKey :
      (fun slot => left.native.application.candidates.lookup (focal, slot)) =
        fun slot => right.native.application.candidates.lookup (focal, slot) := by
    rw [invariant.checkpoint.leftState, invariant.checkpoint.rightState]
    funext slot
    exact invariant.checkpoint.focalCandidates slot
  refine
    { phase := ?_
      focalKey := Prod.ext playerView candidateKey
      environmentView := environmentView
      focalHistory := invariant.checkpoint.focalHistory
      environmentHistory := invariant.checkpoint.environmentHistory
      cacheShape := invariant.cacheShape
      leftFollows := invariant.leftFollows
      rightFollows := invariant.rightFollows
      leftSound := invariant.leftSound
      rightSound := invariant.rightSound
      leftProvenance := invariant.leftProvenance
      rightProvenance := invariant.rightProvenance }
  rw [invariant.checkpoint.leftState, invariant.checkpoint.rightState]
  rfl

/-- Once one paired invocation has supplied the next concrete checkpoint and
cache shapes, the general graph invariants transport automatically. -/
def afterInvoke
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} {suffix : Graph Player L Γ Δ}
    {left right : runtime.application.PolicyExecution}
    (invariant : PrefixReplayInvariant runtime whole focal suffix left right)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (invocation : @MessageApplication.Invocation Player)
    {target : VCtx Player L} {nextSuffix : Graph Player L target Δ}
    {leftNext rightNext : runtime.application.PolicyExecution}
    (leftSupported : leftNext ∈
      (runtime.application.invoke players environment left invocation).support)
    (rightSupported : rightNext ∈
      (runtime.application.invoke players environment right invocation).support)
    (checkpoint : FocalReplayCheckpoint runtime focal nextSuffix leftNext rightNext)
    (shapes : ∀ owner, owner ≠ focal →
      CacheShape (leftNext.principalHistory owner) (rightNext.principalHistory owner)) :
    PrefixReplayInvariant runtime whole focal nextSuffix leftNext rightNext := by
  have leftRun : leftNext ∈
      (runtime.application.runPolicies players environment [invocation] left).support := by
    simpa [MessageApplication.runPolicies] using leftSupported
  have rightRun : rightNext ∈
      (runtime.application.runPolicies players environment [invocation] right).support := by
    simpa [MessageApplication.runPolicies] using rightSupported
  exact
    { checkpoint := checkpoint
      cacheShape := shapes
      leftFollows := runtime.runPolicies_follows whole 0 players environment [invocation]
        left leftNext invariant.leftFollows leftRun
      rightFollows := runtime.runPolicies_follows whole 0 players environment [invocation]
        right rightNext invariant.rightFollows rightRun
      leftSound := runtime.runPolicies_bindingSoundness players environment [invocation]
        left leftNext invariant.leftSound leftRun
      rightSound := runtime.runPolicies_bindingSoundness players environment [invocation]
        right rightNext invariant.rightSound rightRun
      leftProvenance := runtime.runPolicies_disciplinedBindingProvenance players environment
        [invocation] left leftNext invariant.leftProvenance leftRun
      rightProvenance := runtime.runPolicies_disciplinedBindingProvenance players environment
        [invocation] right rightNext invariant.rightProvenance rightRun }

end PrefixReplayInvariant

/-- Cursor-independent initialized seed used by the instruction induction. -/
theorem initialNativeReplayInvariant
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (focal : Player) (leftInput rightInput : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline Graph.BindingOrigins.none)
    (visible : observe focal leftInput = observe focal rightInput) :
    NativeReplayInvariant runtime whole focal
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole leftInput)))
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole rightInput))) :=
  (initialPrefixReplayInvariant runtime whole focal leftInput rightInput unique discipline
    visible).toNative

namespace NativeReplayInvariant

/-- The cursor-independent invariant determines one common typed running
checkpoint.  This is the dependent bridge used at every service invocation;
it is derived from the two actual `Follows` certificates and the observable
replay key, rather than postulated by the induction. -/
theorem exists_focalReplayCheckpoint
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} {left right : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right) :
    ∃ (target : VCtx Player L) (suffix : Graph Player L target Δ),
      Nonempty (FocalReplayCheckpoint runtime focal suffix left right) := by
  rcases invariant.leftFollows with
    ⟨leftTarget, leftSuffix, leftLength, leftIdeal, leftValues, leftBindings,
      leftCandidates, leftClock, leftEntered, leftWalk, leftState⟩
  rcases invariant.rightFollows with
    ⟨rightTarget, rightSuffix, rightLength, rightIdeal, rightValues, rightBindings,
      rightCandidates, rightClock, rightEntered, rightWalk, rightState⟩
  have lengthEq : leftLength = rightLength := by
    have phaseEq := invariant.phase
    rw [leftState, rightState] at phaseEq
    simpa using phaseEq
  subst rightLength
  have cursorEq := Prefix.cursor_eq_of_same_length leftWalk rightWalk
  cases cursorEq
  have environmentEq := invariant.environmentView
  simp only [MessageApplication.State.environmentView] at environmentEq
  rw [leftState, rightState] at environmentEq
  have publicEq := congrArg MessageInterface.EnvironmentObservation.application environmentEq
  simp only [observeEnvironment_eq, State.publicView, Nat.zero_add] at publicEq
  change PublicView.mk leftTarget leftValues leftLength leftClock leftEntered leftBindings =
    PublicView.mk leftTarget rightValues leftLength rightClock rightEntered rightBindings
    at publicEq
  injection publicEq with _ valuesEq _ clockEq enteredEq bindingsEq
  have valuesEq' : (leftValues : PublicValues leftTarget) =
      (rightValues : PublicValues leftTarget) := by
    funext field ty
    exact congrFun (congrFun valuesEq field) ty
  rw [valuesEq', clockEq, enteredEq, bindingsEq] at leftState
  have poolEq := congrArg MessageInterface.EnvironmentObservation.pool environmentEq
  have receiptsEq := congrArg MessageInterface.EnvironmentObservation.receipts environmentEq
  have playerEq := congrArg Prod.fst invariant.focalKey
  rw [leftState, rightState] at playerEq
  simp only [State.focalReplayKey, State.playerView, Nat.zero_add] at playerEq
  change PlayerView.mk focal
      ⟨leftTarget, rightValues, 0 + leftLength, rightClock, rightEntered, rightBindings⟩
      (observe focal leftIdeal) _ =
    PlayerView.mk focal
      ⟨leftTarget, rightValues, 0 + leftLength, rightClock, rightEntered, rightBindings⟩
      (observe focal rightIdeal) _ at playerEq
  injection playerEq with _ _ observationEq _
  have candidateEq := congrArg Prod.snd invariant.focalKey
  rw [leftState, rightState] at candidateEq
  refine ⟨leftTarget, leftSuffix, ⟨?_⟩⟩
  refine
    { leftIdeal := leftIdeal
      rightIdeal := rightIdeal
      publicValues := rightValues
      bindings := rightBindings
      leftCandidates := leftCandidates
      rightCandidates := rightCandidates
      pc := 0 + leftLength
      clock := rightClock
      enteredAt := rightEntered
      leftState := leftState
      rightState := rightState
      focalObservation := observationEq
      focalCandidates := ?_
      pool := poolEq
      receipts := receiptsEq
      focalHistory := invariant.focalHistory
      environmentHistory := invariant.environmentHistory }
  intro slot
  exact congrFun candidateEq slot

/-- The cursor-independent invariant still equates both pure response inputs. -/
theorem focalServiceInput_eq
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} {left right : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right) :
    focalServiceInput runtime focal left = focalServiceInput runtime focal right := by
  have playerView := congrArg Prod.fst invariant.focalKey
  have pool := congrArg MessageInterface.EnvironmentObservation.pool invariant.environmentView
  have receipts :=
    congrArg MessageInterface.EnvironmentObservation.receipts invariant.environmentView
  have focalView : MessageApplication.State.observe runtime.application left.native focal =
      MessageApplication.State.observe runtime.application right.native focal := by
    simp only [MessageApplication.State.observe]
    congr 1
    exact congrArg (fun current => current.observe focal) pool
  unfold focalServiceInput
  exact Prod.ext (Prod.ext invariant.focalHistory focalView)
    (Prod.ext invariant.environmentHistory invariant.environmentView)

/-- General invariant transport once a paired invocation has established its
observable replay fields. -/
theorem afterInvoke
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} {left right : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (invocation : @MessageApplication.Invocation Player)
    {leftNext rightNext : runtime.application.PolicyExecution}
    (leftSupported : leftNext ∈
      (runtime.application.invoke players environment left invocation).support)
    (rightSupported : rightNext ∈
      (runtime.application.invoke players environment right invocation).support)
    (phase : leftNext.native.application.phase = rightNext.native.application.phase)
    (focalKey : leftNext.native.application.focalReplayKey focal =
      rightNext.native.application.focalReplayKey focal)
    (environmentView :
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native)
    (focalHistory : leftNext.principalHistory focal = rightNext.principalHistory focal)
    (environmentHistory : leftNext.environmentHistory = rightNext.environmentHistory)
    (shapes : ∀ owner, owner ≠ focal →
      CacheShape (leftNext.principalHistory owner) (rightNext.principalHistory owner)) :
    NativeReplayInvariant runtime whole focal leftNext rightNext := by
  have leftRun : leftNext ∈
      (runtime.application.runPolicies players environment [invocation] left).support := by
    simpa [MessageApplication.runPolicies] using leftSupported
  have rightRun : rightNext ∈
      (runtime.application.runPolicies players environment [invocation] right).support := by
    simpa [MessageApplication.runPolicies] using rightSupported
  exact
    { phase := phase
      focalKey := focalKey
      environmentView := environmentView
      focalHistory := focalHistory
      environmentHistory := environmentHistory
      cacheShape := shapes
      leftFollows := runtime.runPolicies_follows whole 0 players environment [invocation]
        left leftNext invariant.leftFollows leftRun
      rightFollows := runtime.runPolicies_follows whole 0 players environment [invocation]
        right rightNext invariant.rightFollows rightRun
      leftSound := runtime.runPolicies_bindingSoundness players environment [invocation]
        left leftNext invariant.leftSound leftRun
      rightSound := runtime.runPolicies_bindingSoundness players environment [invocation]
        right rightNext invariant.rightSound rightRun
      leftProvenance := runtime.runPolicies_disciplinedBindingProvenance players environment
        [invocation] left leftNext invariant.leftProvenance leftRun
      rightProvenance := runtime.runPolicies_disciplinedBindingProvenance players environment
        [invocation] right rightNext invariant.rightProvenance rightRun }

end NativeReplayInvariant

end Vegas.GraphRuntime
