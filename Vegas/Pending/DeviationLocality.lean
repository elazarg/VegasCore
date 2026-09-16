/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationExtraction
import Vegas.Pending.ImmutablePrefix
import Vegas.Pending.Observation
import Vegas.Pending.ResolutionLaw

/-! # Cross-run locality for one native deviator

The focal native policy and service response may be fixed pure functions while
the compiled nonfocal policies and graph chance kernels remain live.  Their
private draws need not agree.  This file develops the endpoint-conditioned
cross-run facts needed to show that those differing private draws cannot change
the focal policy input before a common observed graph cursor.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

namespace Prefix

/-- The complete service block for a player-controlled graph head. -/
def playerPhaseBlock (runtime : GraphRuntime Player L Δ) (roster : List Player)
    (reactionRounds phase : Nat) (owner : Player) : List (ServiceInstruction Player) :=
  [.player owner, .player owner] ++
    (List.replicate reactionRounds (reactionRound roster)).flatten ++
    [.includeLatest owner] ++
    List.replicate (max 1 (runtime.deadline phase)) (.expire phase)

/-- The unique service-plan prefix corresponding to a typed graph prefix. -/
def servicePrefix (runtime : GraphRuntime Player L Δ) (roster : List Player)
    (reactionRounds base : Nat) : {start : VCtx Player L} →
    {whole : Graph Player L start Δ} → {target : VCtx Player L} →
    {suffix : Graph Player L target Δ} → {length : Nat} →
    Prefix Δ whole suffix length → List (ServiceInstruction Player)
  | _, _, _, _, _, .refl _ => []
  | _, _, _, _, _, .sample walk =>
      .expire base :: servicePrefix runtime roster reactionRounds (base + 1) walk
  | _, _, _, _, _, .bind (owner := owner) walk =>
      playerPhaseBlock runtime roster reactionRounds base owner ++
        servicePrefix runtime roster reactionRounds (base + 1) walk
  | _, _, _, _, _, .resolve (owner := owner) walk =>
      playerPhaseBlock runtime roster reactionRounds base owner ++
        servicePrefix runtime roster reactionRounds (base + 1) walk

/-- Splitting the service plan at a typed graph cursor produces exactly its
canonical prefix and the residual plan at the advanced ordinal. -/
theorem servicePlan_eq_servicePrefix_append
    (runtime : GraphRuntime Player L Δ) (roster : List Player)
    (reactionRounds base : Nat) {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) :
    runtime.servicePlan roster reactionRounds whole base =
      walk.servicePrefix runtime roster reactionRounds base ++
        runtime.servicePlan roster reactionRounds suffix (base + length) := by
  induction walk generalizing base with
  | refl => simp [servicePrefix]
  | sample walk ih =>
      simp [servicePlan, servicePrefix, ih, Nat.add_assoc]
      congr 1
      omega
  | bind walk ih =>
      simp [servicePlan, servicePrefix, playerPhaseBlock, ih,
        List.append_assoc, Nat.add_assoc]
      congr 1
      omega
  | resolve walk ih =>
      simp [servicePlan, servicePrefix, playerPhaseBlock, ih,
        List.append_assoc, Nat.add_assoc]
      congr 1
      omega

end Prefix

/-- If two continuations from the same typed cursor reach the same later graph
cursor with the same focal observation, then their earlier focal observations
were already equal.  The continuation traffic and all foreign secrets may
differ. -/
theorem endpointObservation_restricts_to_cursor
    (focal : Player) (cursor : Graph Player L Γ₀ Δ)
    (leftIdeal rightIdeal : VEnv L Γ₀)
    {target : VCtx Player L} (suffix : Graph Player L target Δ)
    (leftEnd rightEnd : VEnv L target)
    (leftValues rightValues : PublicValues target)
    (leftBindings rightBindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftPc leftClock leftEntered rightPc rightClock rightEntered : Nat)
    (leftExtends : (State.running suffix leftEnd leftValues leftBindings leftCandidates
      leftPc leftClock leftEntered).Extends cursor leftIdeal)
    (rightExtends : (State.running suffix rightEnd rightValues rightBindings rightCandidates
      rightPc rightClock rightEntered).Extends cursor rightIdeal)
    (visible : observe focal leftEnd = observe focal rightEnd) :
    observe focal leftIdeal = observe focal rightIdeal := by
  obtain ⟨leftLength, leftWalk, leftRetained⟩ := leftExtends
  obtain ⟨rightLength, rightWalk, rightRetained⟩ := rightExtends
  have lengthEq : leftLength = rightLength := by
    have leftContext := leftWalk.context_length
    have rightContext := rightWalk.context_length
    omega
  subst rightLength
  have walkEq : rightWalk = leftWalk := Subsingleton.elim _ _
  subst rightWalk
  calc
    observe focal leftIdeal = observe focal (leftWalk.restrictEnv leftEnd) :=
      congrArg (observe focal) leftRetained.symm
    _ = observe focal (leftWalk.restrictEnv rightEnd) :=
      leftWalk.observe_restrictEnv_eq focal leftEnd rightEnd visible
    _ = observe focal rightIdeal := congrArg (observe focal) rightRetained

/-- Endpoint equality pulls all the way back to initialized inputs through
arbitrary supported policy traffic.  This is the backward half of the
endpoint-conditioned replay argument: it does not require equal policies,
commands, schedules, or hidden foreign values. -/
theorem runPolicies_endpointObservation_initial_eq
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    (whole : Graph Player L Γ₀ Δ) (leftInput rightInput : VEnv L Γ₀)
    (leftPlayers rightPlayers : Player → runtime.application.PlayerPolicy)
    (leftEnvironment rightEnvironment : runtime.application.EnvironmentPolicy)
    (leftSchedule rightSchedule : List (@MessageApplication.Invocation Player))
    (leftEnd rightEnd : runtime.application.PolicyExecution)
    {target : VCtx Player L} (suffix : Graph Player L target Δ)
    (leftIdeal rightIdeal : VEnv L target)
    (leftValues rightValues : PublicValues target)
    (leftBindings rightBindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftPc leftClock leftEntered rightPc rightClock rightEntered : Nat)
    (leftSupported : leftEnd ∈
      (runtime.application.runPolicies leftPlayers leftEnvironment leftSchedule
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole leftInput)))).support)
    (rightSupported : rightEnd ∈
      (runtime.application.runPolicies rightPlayers rightEnvironment rightSchedule
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole rightInput)))).support)
    (leftState : leftEnd.native.application =
      .running suffix leftIdeal leftValues leftBindings leftCandidates
        leftPc leftClock leftEntered)
    (rightState : rightEnd.native.application =
      .running suffix rightIdeal rightValues rightBindings rightCandidates
        rightPc rightClock rightEntered)
    (visible : observe focal leftIdeal = observe focal rightIdeal) :
    observe focal leftInput = observe focal rightInput := by
  have leftExtends := runtime.runPolicies_extends whole leftInput leftPlayers leftEnvironment
    leftSchedule _ leftEnd (State.initial_extends whole leftInput) leftSupported
  have rightExtends := runtime.runPolicies_extends whole rightInput rightPlayers rightEnvironment
    rightSchedule _ rightEnd (State.initial_extends whole rightInput) rightSupported
  rw [leftState] at leftExtends
  rw [rightState] at rightExtends
  exact endpointObservation_restricts_to_cursor focal whole leftInput rightInput suffix
    leftIdeal rightIdeal leftValues rightValues leftBindings rightBindings leftCandidates
    rightCandidates leftPc leftClock leftEntered rightPc rightClock rightEntered
    leftExtends rightExtends visible

/-- Exactly the inputs consulted by a fixed focal player response and a fixed
environment response.  The native trace is intentionally absent: neither
policy receives it. -/
def focalServiceInput (runtime : GraphRuntime Player L Δ)
    (focal : Player) (execution : runtime.application.PolicyExecution) :=
  ((execution.principalHistory focal,
      MessageApplication.State.observe runtime.application execution.native focal),
    (execution.environmentHistory,
      MessageApplication.State.environmentView runtime.application execution.native))

/-- Concrete synchronized checkpoint for endpoint-conditioned replay.  It
equates every field consulted by the fixed focal and service responses, while
deliberately omitting foreign ideal cells and foreign candidate meanings. -/
structure FocalReplayCheckpoint (runtime : GraphRuntime Player L Δ) (focal : Player)
    {Γ : VCtx Player L} (suffix : Graph Player L Γ Δ)
    (left right : runtime.application.PolicyExecution) : Type where
  leftIdeal : VEnv L Γ
  rightIdeal : VEnv L Γ
  publicValues : PublicValues Γ
  bindings : Bindings Player
  leftCandidates : CommitmentCandidates Player Slot (Raw L)
  rightCandidates : CommitmentCandidates Player Slot (Raw L)
  pc : Nat
  clock : Nat
  enteredAt : Nat
  leftState : left.native.application =
    .running suffix leftIdeal publicValues bindings leftCandidates pc clock enteredAt
  rightState : right.native.application =
    .running suffix rightIdeal publicValues bindings rightCandidates pc clock enteredAt
  focalObservation : observe focal leftIdeal = observe focal rightIdeal
  focalCandidates : ∀ slot,
    leftCandidates.lookup (focal, slot) = rightCandidates.lookup (focal, slot)
  pool : left.native.pool = right.native.pool
  receipts : left.native.receipts = right.native.receipts
  focalHistory : left.principalHistory focal = right.principalHistory focal
  environmentHistory : left.environmentHistory = right.environmentHistory

namespace FocalReplayCheckpoint

/-- A replay checkpoint supplies exactly equal inputs to both fixed pure
responses. -/
theorem focalServiceInput_eq
    {runtime : GraphRuntime Player L Δ} {focal : Player} {Γ : VCtx Player L}
    {suffix : Graph Player L Γ Δ}
    {left right : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right) :
    focalServiceInput runtime focal left = focalServiceInput runtime focal right := by
  rcases checkpoint with ⟨leftIdeal, rightIdeal, publicValues, bindings,
    leftCandidates, rightCandidates, pc, clock, enteredAt, leftState, rightState,
    focalObservation, focalCandidates, pool, receipts, focalHistory,
    environmentHistory⟩
  unfold focalServiceInput
  apply Prod.ext
  · apply Prod.ext focalHistory
    simp only [MessageApplication.State.observe]
    congr 1
    · simp [MessagePool.observe, pool]
    · rw [leftState, rightState]
      change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
      congr 1
      funext serial
      exact focalCandidates (.prepared serial)
  · apply Prod.ext environmentHistory
    simp only [MessageApplication.State.environmentView]
    congr 1
    rw [leftState, rightState]
    rfl

/-- At a synchronized resolve cursor, a common successful publication value
has one common accepted handle and one common canonical raw opening.  Each
catalogue verifies that raw independently; no foreign-catalogue equality is
assumed. -/
theorem resolve_success_verified
    {runtime : GraphRuntime Player L Δ} {focal owner : Player}
    {outputName bindingName : VarId} {payload : L.Ty}
    {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    {left right : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal
      (.resolve outputName owner bindingName fresh source checks tail) left right)
    (value : L.Val payload)
    (leftSuccess : R.valueEquiv payload (checkpoint.leftIdeal.get source) = .success value)
    (rightSuccess : R.valueEquiv payload (checkpoint.rightIdeal.get source) = .success value)
    (leftProvenance : left.native.application.DisciplinedBindingProvenance)
    (rightProvenance : right.native.application.DisciplinedBindingProvenance) :
    ∃ handle, lookupBinding checkpoint.bindings bindingName = some handle ∧
      checkpoint.leftCandidates.verify handle
          ⟨R.result payload, (R.valueEquiv payload).symm (.success value)⟩ = true ∧
      checkpoint.rightCandidates.verify handle
          ⟨R.result payload, (R.valueEquiv payload).symm (.success value)⟩ = true := by
  have leftDiscipline :
      (State.running (.resolve outputName owner bindingName fresh source checks tail)
        checkpoint.leftIdeal checkpoint.publicValues checkpoint.bindings
        checkpoint.leftCandidates checkpoint.pc checkpoint.clock
        checkpoint.enteredAt).DisciplinedBindingProvenance := by
    rw [← checkpoint.leftState]
    exact leftProvenance
  have rightDiscipline :
      (State.running (.resolve outputName owner bindingName fresh source checks tail)
        checkpoint.rightIdeal checkpoint.publicValues checkpoint.bindings
        checkpoint.rightCandidates checkpoint.pc checkpoint.clock
        checkpoint.enteredAt).DisciplinedBindingProvenance := by
    rw [← checkpoint.rightState]
    exact rightProvenance
  obtain ⟨leftHandle, leftBinding, _, leftVerified⟩ :=
    State.resolveSource_verified fresh source checks tail checkpoint.leftIdeal
      checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates
      checkpoint.pc checkpoint.clock checkpoint.enteredAt leftSuccess leftDiscipline
  obtain ⟨rightHandle, rightBinding, _, rightVerified⟩ :=
    State.resolveSource_verified fresh source checks tail checkpoint.rightIdeal
      checkpoint.publicValues checkpoint.bindings checkpoint.rightCandidates
      checkpoint.pc checkpoint.clock checkpoint.enteredAt rightSuccess rightDiscipline
  have handleEq : rightHandle = leftHandle := by
    exact Option.some.inj (rightBinding.symm.trans leftBinding)
  subst rightHandle
  have leftEncoded : checkpoint.leftIdeal.get source =
      (R.valueEquiv payload).symm (.success value) := by
    rw [← leftSuccess, Equiv.symm_apply_apply]
  have rightEncoded : checkpoint.rightIdeal.get source =
      (R.valueEquiv payload).symm (.success value) := by
    rw [← rightSuccess, Equiv.symm_apply_apply]
  refine ⟨leftHandle, leftBinding, ?_, ?_⟩
  · rwa [leftEncoded] at leftVerified
  · rwa [rightEncoded] at rightVerified

end FocalReplayCheckpoint

/-- Equal focal graph observations seed the concrete replay checkpoint at
initialized native executions, including all focal initial-handle meanings. -/
def initialFocalReplayCheckpoint
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (focal : Player) (leftInput rightInput : VEnv L Γ)
    (visible : observe focal leftInput = observe focal rightInput) :
    FocalReplayCheckpoint runtime focal graph
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial graph leftInput)))
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial graph rightInput))) := by
  let leftState := State.initial graph leftInput
  let rightState := State.initial graph rightInput
  have publicEq : leftState.publicView = rightState.publicView :=
    State.initial_publicView_congr graph leftInput rightInput
      (Graph.publicValues_eq_of_observe_eq focal leftInput rightInput visible)
  have samePublic : (PublicValues.ofVEnv leftInput : PublicValues Γ) =
      (PublicValues.ofVEnv rightInput : PublicValues Γ) :=
    Graph.publicValues_eq_of_observe_eq focal leftInput rightInput visible
  have bindingsEq : leftState.publicView.bindings = rightState.publicView.bindings :=
    congrArg (fun view : PublicView Player L => view.bindings) publicEq
  refine
    { leftIdeal := leftInput
      rightIdeal := rightInput
      publicValues := leftState.publicView.values
      bindings := leftState.publicView.bindings
      leftCandidates := leftState.candidates
      rightCandidates := rightState.candidates
      pc := 0
      clock := 0
      enteredAt := 0
      leftState := ?_
      rightState := ?_
      focalObservation := visible
      focalCandidates := ?_
      pool := rfl
      receipts := rfl
      focalHistory := rfl
      environmentHistory := rfl }
  · change State.initial graph leftInput = .running graph leftInput
      leftState.publicView.values leftState.publicView.bindings leftState.candidates 0 0 0
    rfl
  · change State.initial graph rightInput = .running graph rightInput
      leftState.publicView.values leftState.publicView.bindings rightState.candidates 0 0 0
    change State.initial graph rightInput = .running graph rightInput
      (PublicValues.ofVEnv leftInput) leftState.publicView.bindings rightState.candidates 0 0 0
    rw [samePublic, bindingsEq]
    rfl
  · intro slot
    exact State.initial_candidate_lookup_congr graph focal leftInput rightInput visible slot

/-- Equal initial focal observations give equal complete focal/service inputs,
despite arbitrary differences in foreign sealed initial values. -/
theorem initial_focalServiceInput_eq
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (focal : Player) (left right : VEnv L Γ)
    (visible : observe focal left = observe focal right) :
    focalServiceInput runtime focal (MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application
        (State.initial graph left))) =
    focalServiceInput runtime focal (MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application
        (State.initial graph right))) := by
  have player := State.initial_playerView_congr graph focal left right visible
  have publicEq := State.initial_publicView_congr graph left right
    (Graph.publicValues_eq_of_observe_eq focal left right visible)
  have playerApp : runtime.application.observePlayer (State.initial graph left) focal =
      runtime.application.observePlayer (State.initial graph right) focal := by
    exact player
  have environmentApp : runtime.application.observeEnvironment (State.initial graph left) =
      runtime.application.observeEnvironment (State.initial graph right) := by
    exact publicEq
  have focalView : MessageApplication.State.observe runtime.application
      (MessageApplication.State.initial runtime.application (State.initial graph left)) focal =
      MessageApplication.State.observe runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial graph right)) focal := by
    simp only [MessageApplication.State.observe, MessageApplication.State.initial]
    rw [playerApp]
  have environmentView :
      MessageApplication.State.environmentView runtime.application
        (MessageApplication.State.initial runtime.application (State.initial graph left)) =
      MessageApplication.State.environmentView runtime.application
        (MessageApplication.State.initial runtime.application (State.initial graph right)) := by
    simp only [MessageApplication.State.environmentView, MessageApplication.State.initial]
    rw [environmentApp]
  unfold focalServiceInput MessageApplication.PolicyExecution.initial
  rw [focalView, environmentView]

/-- Consequently, equal endpoint observations force equal deterministic
focal/service seeds at setup, even when the two supported executions used
different policies and schedules. -/
theorem initial_focalServiceInput_eq_of_supported_endpoint
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    (whole : Graph Player L Γ₀ Δ) (leftInput rightInput : VEnv L Γ₀)
    (leftPlayers rightPlayers : Player → runtime.application.PlayerPolicy)
    (leftEnvironment rightEnvironment : runtime.application.EnvironmentPolicy)
    (leftSchedule rightSchedule : List (@MessageApplication.Invocation Player))
    (leftEnd rightEnd : runtime.application.PolicyExecution)
    {target : VCtx Player L} (suffix : Graph Player L target Δ)
    (leftIdeal rightIdeal : VEnv L target)
    (leftValues rightValues : PublicValues target)
    (leftBindings rightBindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftPc leftClock leftEntered rightPc rightClock rightEntered : Nat)
    (leftSupported : leftEnd ∈
      (runtime.application.runPolicies leftPlayers leftEnvironment leftSchedule
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole leftInput)))).support)
    (rightSupported : rightEnd ∈
      (runtime.application.runPolicies rightPlayers rightEnvironment rightSchedule
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole rightInput)))).support)
    (leftState : leftEnd.native.application =
      .running suffix leftIdeal leftValues leftBindings leftCandidates
        leftPc leftClock leftEntered)
    (rightState : rightEnd.native.application =
      .running suffix rightIdeal rightValues rightBindings rightCandidates
        rightPc rightClock rightEntered)
    (visible : observe focal leftIdeal = observe focal rightIdeal) :
    focalServiceInput runtime focal
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole leftInput))) =
      focalServiceInput runtime focal
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole rightInput))) := by
  apply initial_focalServiceInput_eq runtime whole focal
  exact runPolicies_endpointObservation_initial_eq runtime focal whole leftInput rightInput
    leftPlayers rightPlayers leftEnvironment rightEnvironment leftSchedule rightSchedule
    leftEnd rightEnd suffix leftIdeal rightIdeal leftValues rightValues leftBindings
    rightBindings leftCandidates rightCandidates leftPc leftClock leftEntered rightPc
    rightClock rightEntered leftSupported rightSupported leftState rightState visible

/-- A private graph command preserves the environment policy's complete input. -/
private theorem playerStep_private_environmentInput
    (runtime : GraphRuntime Player L Δ) (owner : Player)
    (execution next : runtime.application.PolicyExecution)
    (command : PrivateCommand L)
    (supported : next ∈ (runtime.application.playerStep owner execution
      (.privateCommand command)).support) :
    (next.environmentHistory,
        MessageApplication.State.environmentView runtime.application next.native) =
      (execution.environmentHistory,
        MessageApplication.State.environmentView runtime.application execution.native) := by
  have history := runtime.application.playerStep_environmentHistory owner execution
    (.privateCommand command) next supported
  have native : next.native ∈
      ((runtime.application.playerStep owner execution
        (.privateCommand command)).map
          MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.playerStep_native] at native
  simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.mem_support_pure] at native
  rw [native]
  apply Prod.ext history
  change MessageApplication.State.environmentView runtime.application
      { execution.native with application :=
          runtime.application.privateStep execution.native.application owner command } =
    MessageApplication.State.environmentView runtime.application execution.native
  cases execution.native
  simp only [MessageApplication.State.environmentView,
    GraphRuntime.application, runtime.privateStep_public]

/-- At a synchronized graph cursor, the same focal private command preserves
the focal application view.  Only focal candidate lookups are equated; foreign
candidate meanings remain unconstrained. -/
theorem privateStep_focal_playerView_congr
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    (graph : Graph Player L Γ Δ) (leftIdeal rightIdeal : VEnv L Γ)
    (visible : observe focal leftIdeal = observe focal rightIdeal)
    (values : PublicValues Γ) (bindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (ownCandidates : ∀ serial,
      leftCandidates.lookup (focal, .prepared serial) =
        rightCandidates.lookup (focal, .prepared serial))
    (pc clock enteredAt : Nat) (command : PrivateCommand L) :
    (runtime.privateStep
      (.running graph leftIdeal values bindings leftCandidates pc clock enteredAt)
      focal command).playerView focal =
    (runtime.privateStep
      (.running graph rightIdeal values bindings rightCandidates pc clock enteredAt)
      focal command).playerView focal := by
  cases command with
  | rememberDisclosure disclose =>
      change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
      congr 1
      funext serial
      exact ownCandidates serial
  | prepare slot raw =>
      change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
      congr 1
      funext serial
      by_cases same : serial = slot
      · subst serial
        simp only [CommitmentCandidates.lookup_prepare_self]
        rw [ownCandidates slot]
      · rw [leftCandidates.lookup_prepare_other focal (.prepared slot) raw
            (focal, .prepared serial),
          rightCandidates.lookup_prepare_other focal (.prepared slot) raw
            (focal, .prepared serial)]
        · exact ownCandidates serial
        · intro equal
          exact same (Slot.prepared.inj (congrArg Prod.snd equal))
        · intro equal
          exact same (Slot.prepared.inj (congrArg Prod.snd equal))

/-- The same focal private command preserves the complete focal/service input
at a synchronized checkpoint.  This covers arbitrary unrelated preparation
and dishonest disclosure markers chosen by the native deviator. -/
theorem focal_privateStep_focalServiceInput_eq
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {suffix : Graph Player L Γ Δ}
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (command : PrivateCommand L)
    (leftSupported : leftNext ∈
      (runtime.application.playerStep focal left (.privateCommand command)).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep focal right (.privateCommand command)).support) :
    focalServiceInput runtime focal leftNext =
      focalServiceInput runtime focal rightNext := by
  have inputEq := checkpoint.focalServiceInput_eq
  have oldFocal := congrArg Prod.fst inputEq
  have oldHistory := congrArg Prod.fst oldFocal
  have oldView := congrArg Prod.snd oldFocal
  change left.principalHistory focal = right.principalHistory focal at oldHistory
  change MessageApplication.State.observe runtime.application left.native focal =
    MessageApplication.State.observe runtime.application right.native focal at oldView
  have leftHistory := runtime.application.playerStep_history_self focal left
    (.privateCommand command) leftNext leftSupported
  have rightHistory := runtime.application.playerStep_history_self focal right
    (.privateCommand command) rightNext rightSupported
  have leftNative : leftNext.native ∈
      ((runtime.application.playerStep focal left (.privateCommand command)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨leftNext, leftSupported, rfl⟩
  have rightNative : rightNext.native ∈
      ((runtime.application.playerStep focal right (.privateCommand command)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨rightNext, rightSupported, rfl⟩
  rw [runtime.application.playerStep_native] at leftNative rightNative
  simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.mem_support_pure] at leftNative rightNative
  have nextView : MessageApplication.State.observe runtime.application leftNext.native focal =
      MessageApplication.State.observe runtime.application rightNext.native focal := by
    rw [leftNative, rightNative]
    simp only [MessageApplication.State.observe]
    congr 1
    · simp [MessagePool.observe, checkpoint.pool]
    · rw [checkpoint.leftState, checkpoint.rightState]
      exact privateStep_focal_playerView_congr runtime focal suffix checkpoint.leftIdeal
        checkpoint.rightIdeal checkpoint.focalObservation checkpoint.publicValues
        checkpoint.bindings checkpoint.leftCandidates checkpoint.rightCandidates
        (fun serial => checkpoint.focalCandidates (.prepared serial)) checkpoint.pc
        checkpoint.clock checkpoint.enteredAt command
    · exact checkpoint.receipts
  have nextFocal :
      (leftNext.principalHistory focal,
          MessageApplication.State.observe runtime.application leftNext.native focal) =
        (rightNext.principalHistory focal,
          MessageApplication.State.observe runtime.application rightNext.native focal) := by
    apply Prod.ext
    · rw [leftHistory, rightHistory, oldHistory, oldView]
    · exact nextView
  have leftEnvironment := playerStep_private_environmentInput runtime focal left leftNext
    command leftSupported
  have rightEnvironment := playerStep_private_environmentInput runtime focal right rightNext
    command rightSupported
  unfold focalServiceInput
  exact Prod.ext nextFocal
    (leftEnvironment.trans ((congrArg Prod.snd inputEq).trans rightEnvironment.symm))

/-- Equal environment inputs remain equal after the same player command.
This covers canonical submissions and rebroadcasts without equating the two
hidden graph environments. -/
private theorem playerStep_same_environmentInput
    (runtime : GraphRuntime Player L Δ) (owner : Player)
    (left right leftNext rightNext : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (inputs :
      (left.environmentHistory,
          MessageApplication.State.environmentView runtime.application left.native) =
        (right.environmentHistory,
          MessageApplication.State.environmentView runtime.application right.native))
    (leftSupported : leftNext ∈
      (runtime.application.playerStep owner left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep owner right command).support) :
    (leftNext.environmentHistory,
        MessageApplication.State.environmentView runtime.application leftNext.native) =
      (rightNext.environmentHistory,
        MessageApplication.State.environmentView runtime.application rightNext.native) := by
  have leftHistory := runtime.application.playerStep_environmentHistory owner left command
    leftNext leftSupported
  have rightHistory := runtime.application.playerStep_environmentHistory owner right command
    rightNext rightSupported
  have oldHistory := congrArg Prod.fst inputs
  have oldView := congrArg Prod.snd inputs
  change MessageApplication.State.environmentView runtime.application left.native =
    MessageApplication.State.environmentView runtime.application right.native at oldView
  have leftNative : leftNext.native ∈
      ((runtime.application.playerStep owner left command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨leftNext, leftSupported, rfl⟩
  have rightNative : rightNext.native ∈
      ((runtime.application.playerStep owner right command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨rightNext, rightSupported, rfl⟩
  rw [runtime.application.playerStep_native] at leftNative rightNative
  apply Prod.ext (leftHistory.trans (oldHistory.trans rightHistory.symm))
  cases command with
  | privateCommand privateCommand =>
      have leftPrivate := playerStep_private_environmentInput runtime owner left leftNext
        privateCommand leftSupported
      have rightPrivate := playerStep_private_environmentInput runtime owner right rightNext
        privateCommand rightSupported
      exact congrArg Prod.snd (leftPrivate.trans (inputs.trans rightPrivate.symm))
  | submit payload =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at leftNative rightNative
      rw [leftNative, rightNative]
      simpa only [MessageApplication.State.environmentView] using
        congrArg (fun view : runtime.application.EnvironmentObservation =>
          { view with pool := (view.pool.submit owner payload).2 }) oldView
  | replay id =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at leftNative rightNative
      rw [leftNative, rightNative]
      simpa only [MessageApplication.State.environmentView] using
        congrArg (fun view : runtime.application.EnvironmentObservation =>
          { view with pool := (view.pool.replay owner id).state }) oldView
  | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, FinDist.mem_support_pure]
        at leftNative rightNative
      rw [leftNative, rightNative]
      exact oldView

/-- A fixed focal response's same visible command preserves its complete next
input. Together with `focal_privateStep_focalServiceInput_eq`, this covers
every command constructor available to the arbitrary native deviator. -/
theorem focal_sameCommand_focalServiceInput_eq
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {suffix : Graph Player L Γ Δ}
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (command : runtime.application.PlayerCommand)
    (leftSupported : leftNext ∈
      (runtime.application.playerStep focal left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep focal right command).support) :
    focalServiceInput runtime focal leftNext =
      focalServiceInput runtime focal rightNext := by
  cases command with
  | privateCommand privateCommand =>
      exact focal_privateStep_focalServiceInput_eq runtime focal checkpoint privateCommand
        leftSupported rightSupported
  | submit payload =>
      have inputEq := checkpoint.focalServiceInput_eq
      have oldFocal := congrArg Prod.fst inputEq
      have oldHistory := congrArg Prod.fst oldFocal
      have oldView := congrArg Prod.snd oldFocal
      change left.principalHistory focal = right.principalHistory focal at oldHistory
      change MessageApplication.State.observe runtime.application left.native focal =
        MessageApplication.State.observe runtime.application right.native focal at oldView
      have leftHistory := runtime.application.playerStep_history_self focal left (.submit payload)
        leftNext leftSupported
      have rightHistory := runtime.application.playerStep_history_self focal right
        (.submit payload) rightNext rightSupported
      have leftNative : leftNext.native ∈
          ((runtime.application.playerStep focal left (.submit payload)).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨leftNext, leftSupported, rfl⟩
      have rightNative : rightNext.native ∈
          ((runtime.application.playerStep focal right (.submit payload)).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨rightNext, rightSupported, rfl⟩
      rw [runtime.application.playerStep_native] at leftNative rightNative
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at leftNative rightNative
      have nextView : MessageApplication.State.observe runtime.application leftNext.native focal =
          MessageApplication.State.observe runtime.application rightNext.native focal := by
        rw [leftNative, rightNative]
        simp only [MessageApplication.State.observe]
        congr 1
        · simp [MessagePool.submit, MessagePool.observe, checkpoint.pool]
        · exact congrArg MessageInterface.View.application oldView
        · exact checkpoint.receipts
      have nextFocal :
          (leftNext.principalHistory focal,
              MessageApplication.State.observe runtime.application leftNext.native focal) =
            (rightNext.principalHistory focal,
              MessageApplication.State.observe runtime.application rightNext.native focal) := by
        apply Prod.ext
        · rw [leftHistory, rightHistory, oldHistory, oldView]
        · exact nextView
      have environment := playerStep_same_environmentInput runtime focal left right leftNext
        rightNext (.submit payload) (congrArg Prod.snd inputEq) leftSupported rightSupported
      unfold focalServiceInput
      exact Prod.ext nextFocal environment
  | replay id =>
      have inputEq := checkpoint.focalServiceInput_eq
      have oldFocal := congrArg Prod.fst inputEq
      have oldHistory := congrArg Prod.fst oldFocal
      have oldView := congrArg Prod.snd oldFocal
      change left.principalHistory focal = right.principalHistory focal at oldHistory
      change MessageApplication.State.observe runtime.application left.native focal =
        MessageApplication.State.observe runtime.application right.native focal at oldView
      have leftHistory := runtime.application.playerStep_history_self focal left (.replay id)
        leftNext leftSupported
      have rightHistory := runtime.application.playerStep_history_self focal right (.replay id)
        rightNext rightSupported
      have leftNative : leftNext.native ∈
          ((runtime.application.playerStep focal left (.replay id)).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨leftNext, leftSupported, rfl⟩
      have rightNative : rightNext.native ∈
          ((runtime.application.playerStep focal right (.replay id)).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨rightNext, rightSupported, rfl⟩
      rw [runtime.application.playerStep_native] at leftNative rightNative
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at leftNative rightNative
      have nextView : MessageApplication.State.observe runtime.application leftNext.native focal =
          MessageApplication.State.observe runtime.application rightNext.native focal := by
        rw [leftNative, rightNative]
        simp only [MessageApplication.State.observe]
        congr 1
        · exact congrArg (fun pool => pool.observe focal)
            (congrArg (fun pool => (pool.replay focal id).state) checkpoint.pool)
        · exact congrArg MessageInterface.View.application oldView
        · exact checkpoint.receipts
      have nextFocal :
          (leftNext.principalHistory focal,
              MessageApplication.State.observe runtime.application leftNext.native focal) =
            (rightNext.principalHistory focal,
              MessageApplication.State.observe runtime.application rightNext.native focal) := by
        apply Prod.ext
        · rw [leftHistory, rightHistory, oldHistory, oldView]
        · exact nextView
      have environment := playerStep_same_environmentInput runtime focal left right leftNext
        rightNext (.replay id) (congrArg Prod.snd inputEq) leftSupported rightSupported
      unfold focalServiceInput
      exact Prod.ext nextFocal environment
  | wait =>
      have inputEq := checkpoint.focalServiceInput_eq
      have leftHistory := runtime.application.playerStep_history_self focal left .wait
        leftNext leftSupported
      have rightHistory := runtime.application.playerStep_history_self focal right .wait
        rightNext rightSupported
      have oldFocal := congrArg Prod.fst inputEq
      have oldHistory := congrArg Prod.fst oldFocal
      have oldView := congrArg Prod.snd oldFocal
      change left.principalHistory focal = right.principalHistory focal at oldHistory
      change MessageApplication.State.observe runtime.application left.native focal =
        MessageApplication.State.observe runtime.application right.native focal at oldView
      have leftNative : leftNext.native ∈
          ((runtime.application.playerStep focal left .wait).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨leftNext, leftSupported, rfl⟩
      have rightNative : rightNext.native ∈
          ((runtime.application.playerStep focal right .wait).map
            MessageInterface.PolicyExecution.native).support := by
        rw [FinDist.support_map]
        exact ⟨rightNext, rightSupported, rfl⟩
      rw [runtime.application.playerStep_native] at leftNative rightNative
      simp only [MessageApplication.PlayerCommand.toAction, FinDist.mem_support_pure]
        at leftNative rightNative
      have nextFocal :
          (leftNext.principalHistory focal,
              MessageApplication.State.observe runtime.application leftNext.native focal) =
            (rightNext.principalHistory focal,
              MessageApplication.State.observe runtime.application rightNext.native focal) := by
        rw [leftHistory, rightHistory, leftNative, rightNative, oldHistory, oldView]
      have environment := playerStep_same_environmentInput runtime focal left right leftNext
        rightNext .wait (congrArg Prod.snd inputEq) leftSupported rightSupported
      unfold focalServiceInput
      exact Prod.ext nextFocal environment

/-- Paired canonical visible commands by a nonfocal player preserve the
complete focal/service input.  In particular this applies to the identical
commitment header or normalized disclosure packet reconstructed by the
compiler. -/
theorem nonfocal_sameCommand_focalServiceInput_eq
    (runtime : GraphRuntime Player L Δ) (focal owner : Player)
    (different : focal ≠ owner)
    (left right leftNext rightNext : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (inputs : focalServiceInput runtime focal left =
      focalServiceInput runtime focal right)
    (leftSupported : leftNext ∈
      (runtime.application.playerStep owner left command).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep owner right command).support) :
    focalServiceInput runtime focal leftNext =
      focalServiceInput runtime focal rightNext := by
  have leftFocal := runtime.application.playerStep_other_input owner focal different
    (fun state privateCommand =>
      runtime.privateStep_other_playerView state owner focal different privateCommand)
    left leftNext command leftSupported
  have rightFocal := runtime.application.playerStep_other_input owner focal different
    (fun state privateCommand =>
      runtime.privateStep_other_playerView state owner focal different privateCommand)
    right rightNext command rightSupported
  have environment := playerStep_same_environmentInput runtime owner left right leftNext
    rightNext command (congrArg Prod.snd inputs) leftSupported rightSupported
  change (_, _) = (_, _) at inputs ⊢
  have focalInputs := congrArg Prod.fst inputs
  exact Prod.ext (leftFocal.trans (focalInputs.trans rightFocal.symm)) environment

/-- Paired hidden draws of an unchanged nonfocal player preserve both inputs
that control the deterministic part of the execution.  The two private commands
may contain different bind raw values or different resolve Booleans. -/
theorem nonfocal_privateSteps_focalServiceInput_eq
    (runtime : GraphRuntime Player L Δ) (focal owner : Player)
    (different : focal ≠ owner)
    (left right leftNext rightNext : runtime.application.PolicyExecution)
    (leftCommand rightCommand : PrivateCommand L)
    (inputs : focalServiceInput runtime focal left =
      focalServiceInput runtime focal right)
    (leftSupported : leftNext ∈ (runtime.application.playerStep owner left
      (.privateCommand leftCommand)).support)
    (rightSupported : rightNext ∈ (runtime.application.playerStep owner right
      (.privateCommand rightCommand)).support) :
    focalServiceInput runtime focal leftNext =
      focalServiceInput runtime focal rightNext := by
  have leftFocal := runtime.application.playerStep_other_input owner focal different
    (fun state command => runtime.privateStep_other_playerView state owner focal different command)
    left leftNext (.privateCommand leftCommand) leftSupported
  have rightFocal := runtime.application.playerStep_other_input owner focal different
    (fun state command => runtime.privateStep_other_playerView state owner focal different command)
    right rightNext (.privateCommand rightCommand) rightSupported
  have leftEnvironment := playerStep_private_environmentInput runtime owner left leftNext
    leftCommand leftSupported
  have rightEnvironment := playerStep_private_environmentInput runtime owner right rightNext
    rightCommand rightSupported
  change (_, _) = (_, _) at inputs ⊢
  have focalInputs := congrArg Prod.fst inputs
  have environmentInputs := congrArg Prod.snd inputs
  exact Prod.ext (leftFocal.trans (focalInputs.trans rightFocal.symm))
    (leftEnvironment.trans (environmentInputs.trans rightEnvironment.symm))

/-- The visible bind submission is independent of the privately prepared raw
value and of the owner's earlier private history. -/
theorem compiled_bind_submission_eq
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh next))
    (leftHistory rightHistory : List (Entry runtime))
    (leftView rightView : runtime.application.View) (leftRaw rightRaw : Raw L)
    (leftPc : leftView.application.publicState.pc = site)
    (rightPc : rightView.application.publicState.pc = site)
    (leftPrepared : preparedRaw leftHistory site = some leftRaw)
    (rightPrepared : preparedRaw rightHistory site = some rightRaw)
    (leftUnsubmitted : submittedAt leftHistory site = false)
    (rightUnsubmitted : submittedAt rightHistory site = false) :
    compileAt runtime owner whole (.bind name owner fresh next) policy site
        leftHistory leftView =
      compileAt runtime owner whole (.bind name owner fresh next) policy site
        rightHistory rightView := by
  rw [compileAt_bind_prepared runtime whole site name owner fresh next policy
      leftHistory leftView leftRaw leftPc leftPrepared leftUnsubmitted,
    compileAt_bind_prepared runtime whole site name owner fresh next policy
      rightHistory rightView rightRaw rightPc rightPrepared rightUnsubmitted]

/-- Once a resolve choice has been cached, its visible command depends only on
the eventual accepted publication result and common public address.  Different
private Booleans that both normalize to failure therefore produce the same
packet. -/
theorem compiled_resolve_submission_eq_of_result_eq
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks tail))
    (leftHistory rightHistory : List (Entry runtime))
    (leftNative rightNative : runtime.application.State)
    (leftIdeal rightIdeal : VEnv L Γ) (bindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (site leftClock leftEntered rightClock rightEntered : Nat)
    (leftDisclose rightDisclose : Bool)
    (leftApplication : leftNative.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        leftIdeal (PublicValues.ofVEnv leftIdeal) bindings leftCandidates
        site leftClock leftEntered)
    (rightApplication : rightNative.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        rightIdeal (PublicValues.ofVEnv rightIdeal) bindings rightCandidates
        site rightClock rightEntered)
    (leftRemembered : rememberedDisclosure leftHistory site = some leftDisclose)
    (rightRemembered : rememberedDisclosure rightHistory site = some rightDisclose)
    (leftUnsubmitted : submittedAt leftHistory site = false)
    (rightUnsubmitted : submittedAt rightHistory site = false)
    (sameResult : acceptedResult source checks leftIdeal leftDisclose =
      acceptedResult source checks rightIdeal rightDisclose) :
    compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks tail)
        policy site leftHistory
          (MessageApplication.State.observe runtime.application leftNative owner) =
      compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks tail)
        policy site rightHistory
          (MessageApplication.State.observe runtime.application rightNative owner) := by
  rw [compileAt_resolve_result runtime whole outputName bindingName owner fresh source checks
      tail policy leftHistory leftNative leftIdeal bindings leftCandidates site leftClock
      leftEntered leftDisclose leftApplication leftRemembered leftUnsubmitted,
    compileAt_resolve_result runtime whole outputName bindingName owner fresh source checks
      tail policy rightHistory rightNative rightIdeal bindings rightCandidates site rightClock
      rightEntered rightDisclose rightApplication rightRemembered rightUnsubmitted,
    sameResult]

end Vegas.GraphRuntime
