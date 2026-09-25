/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeOutcome
import Vegas.Pending.ReactiveSelectionObservation

/-! # The receiver's quiet decision cannot depend on the hidden bit

The comparison covers the complete bounded raw response menu. Owner-local
handling and the fixed expiry step determine the same receiver publication
for either hidden bit, including malformed calls and silence.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private theorem quiet_transport (bit : Bool) :
    (quietBob bit).Provenance nativeApp ∧ (quietBob bit).InputRecall nativeApp ∧
      (quietBob bit).network.PendingOrPublished ∧
      (quietBob bit).network.SerialsBeforeNext ∧
      ∀ response, ((quietBob bit).respond nativeApp bob response).SubmissionAudit
        nativeApp ReactivePlayerView.publicView := by
  have raw := nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler
    (quietBobHistory bit).trace
  have audit := nativeApp.submissionAudit_history ReactivePlayerView.publicView
    (fun _ _ => rfl) nativeInitialLaw nativeHorizon nativeScheduler raw
  refine ⟨nativeApp.history_provenance nativeInitialLaw nativeHorizon nativeScheduler raw,
    nativeApp.history_inputRecall nativeInitialLaw nativeHorizon nativeScheduler raw,
    nativeApp.pendingOrPublished_history nativeScheduler nativeInitialLaw nativeHorizon raw,
    nativeApp.serialsBeforeNext_history nativeScheduler nativeInitialLaw nativeHorizon raw, ?_⟩
  intro response
  exact nativeApp.submissionAudit_respond ReactivePlayerView.publicView (fun _ _ => rfl)
    (quietBob bit) bob response audit.1
    (nativeApp.submissionOrigin_next_none_history nativeInitialLaw nativeHorizon
      nativeScheduler _ raw bob) (audit.2 bob rfl)

theorem quiet_reserved_local (bit : Bool) (response : nativeApp.Action)
    (players : Player → nativeApp.Policy) (left right : nativeApp.Execution)
    (leftMem : left ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) ((quietBob bit).respond nativeApp bob response)).support)
    (rightMem : right ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob)
        ((quietBob false).respond nativeApp bob response)).support) :
    left.application.playerView bob = right.application.playerView bob := by
  obtain ⟨leftOrigins, leftRecall, leftRetained, leftSerials, leftAudit⟩ := quiet_transport bit
  obtain ⟨rightOrigins, rightRecall, rightRetained, rightSerials, rightAudit⟩ :=
    quiet_transport false
  have views := nativeRuntime.reactive_playerView_congr nativeLeaks
    (quietBob bit).application (quietBob false).application bob
    (congrArg ReactiveApplication.PlayerView.application (quiet_bob_observation bit)) rfl
  have unique (value : Bool) :
      nativeRuntime.UniqueEventOutput nativeLeaks bob bobPublication
        ((quietBob value).recall bob) := by
    intro first firstMem
    change first ∈ ([] : List (Message Player (WitnessedPacket nativeGraph))) at firstMem
    simp only [List.not_mem_nil] at firstMem
  have law := nativeRuntime.reactive_reserved_playerView_congr nativeLeaks bob
    bobPublication (quietBob bit) (quietBob false) response views rfl rfl
    leftOrigins rightOrigins leftRecall rightRecall leftRetained rightRetained
    (unique bit) (unique false) leftSerials rightSerials (leftAudit response) (rightAudit response)
  dsimp only at law
  rw [nativeRuntime.interaction_includeLatest_environment] at leftMem rightMem
  obtain ⟨next, pureStep⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks bob
    bobPublication ((quietBob bit).respond nativeApp bob response)
  rw [pureStep] at leftMem
  have leftEq := FinDist.mem_support_pure.mp leftMem
  subst left
  rw [pureStep, FinDist.map_pure] at law
  have mapped : right.application.playerView bob ∈
      (FinDist.pure (next.application.playerView bob)).support := by
    rw [law, FinDist.support_map]
    exact ⟨right, rightMem, rfl⟩
  exact (FinDist.mem_support_pure.mp mapped).symm

private theorem maintenance_local (left right nextLeft nextRight : nativeApp.Execution)
    (command : EnvironmentCommand nativeGraph)
    (maintenance : ∀ event, command ≠ .executeSample event)
    (views : left.application.playerView bob = right.application.playerView bob)
    (leftMem : nextLeft ∈ (left.environmentStep nativeApp (.application command)).support)
    (rightMem : nextRight ∈ (right.environmentStep nativeApp (.application command)).support) :
    nextLeft.application.playerView bob = nextRight.application.playerView bob := by
  have law := nativeRuntime.maintenance_playerView_congr left.application right.application bob
    command maintenance views
  have pureStep (execution : nativeApp.Execution) :
      ∃ state, environmentStep nativeRuntime execution.application command =
        FinDist.pure state := by
    cases command with
    | executeSample event => exact (maintenance event rfl).elim
    | grant event => exact ⟨_, rfl⟩
    | advanceClock => exact ⟨_, rfl⟩
    | expire event => exact ⟨_, rfl⟩
  obtain ⟨leftState, leftPure⟩ := pureStep left
  obtain ⟨rightState, rightPure⟩ := pureStep right
  have step (execution : nativeApp.Execution) (state : State nativeGraph)
      (pureLaw : environmentStep nativeRuntime execution.application command = FinDist.pure state)
      (next : nativeApp.Execution)
      (supported : next ∈ (execution.environmentStep nativeApp (.application command)).support) :
      next.application = state := by
    obtain ⟨updated, moved, rfl⟩ := FinDist.support_map .. ▸ supported
    obtain ⟨result, resultMem, rfl⟩ := FinDist.support_map .. ▸ moved
    change result ∈ (environmentStep nativeRuntime execution.application command).support
      at resultMem
    rw [pureLaw] at resultMem
    exact FinDist.mem_support_pure.mp resultMem
  rw [step left leftState leftPure nextLeft leftMem,
    step right rightState rightPure nextRight rightMem]
  rw [leftPure, rightPure, FinDist.map_pure, FinDist.map_pure] at law
  apply FinDist.mem_support_pure.mp
  rw [← law]
  exact FinDist.mem_support_pure.mpr rfl

def quietGuessPlan : List (ServiceInstruction nativeGraph) :=
  [.includeLatest bobPublication bob, .tick, .expire bobPublication]

def quietGuessLaw (bit : Bool) (response : nativeApp.Action)
    (players : Player → nativeApp.Policy) : FinDist nativeApp.Execution :=
  nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork quietGuessPlan
    ((quietBob bit).respond nativeApp bob response)

theorem quiet_guess_owner_local (bit : Bool) (response : nativeApp.Action)
    (players : Player → nativeApp.Policy) (left right : nativeApp.Execution)
    (leftMem : left ∈ (quietGuessLaw bit response players).support)
    (rightMem : right ∈ (quietGuessLaw false response players).support) :
    left.application.playerView bob = right.application.playerView bob := by
  simp only [quietGuessLaw, quietGuessPlan, runInteractionPlan, FinDist.bind_pure]
    at leftMem rightMem
  obtain ⟨leftReserved, leftReservedMem, leftRest⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftMem)
  obtain ⟨rightReserved, rightReservedMem, rightRest⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightMem)
  have reserved := quiet_reserved_local bit response players leftReserved rightReserved
    leftReservedMem rightReservedMem
  obtain ⟨leftTick, leftTickMem, leftExpire⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftRest)
  obtain ⟨rightTick, rightTickMem, rightExpire⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightRest)
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    at leftTickMem rightTickMem leftExpire rightExpire
  change leftTick ∈ ((leftReserved.environmentStep nativeApp (.application .advanceClock)).bind
    FinDist.pure).support at leftTickMem
  change rightTick ∈ ((rightReserved.environmentStep nativeApp (.application .advanceClock)).bind
    FinDist.pure).support at rightTickMem
  change left ∈ ((leftTick.environmentStep nativeApp
    (.application (.expire bobPublication))).bind FinDist.pure).support at leftExpire
  change right ∈ ((rightTick.environmentStep nativeApp
    (.application (.expire bobPublication))).bind FinDist.pure).support at rightExpire
  rw [FinDist.bind_pure] at leftTickMem rightTickMem leftExpire rightExpire
  have ticked := maintenance_local leftReserved rightReserved leftTick rightTick .advanceClock
    (by intro event impossible; cases impossible) reserved leftTickMem rightTickMem
  exact maintenance_local leftTick rightTick left right (.expire bobPublication)
    (by intro event impossible; cases impossible) ticked leftExpire rightExpire

def quietGuess (response : nativeApp.Action) (players : Player → nativeApp.Policy) :
    PublicationResult Bool :=
  (nativeResults
    ((quietGuessLaw false response players).support_nonempty.choose).application.config).bob

theorem quiet_raw_guess_fixed (bit : Bool) (response : nativeApp.Action)
    (players : Player → nativeApp.Policy) (next : nativeApp.Execution)
    (supported : next ∈ (quietGuessLaw bit response players).support) :
    (nativeResults next.application.config).bob = quietGuess response players := by
  have views := quiet_guess_owner_local bit response players next
    (quietGuessLaw false response players).support_nonempty.choose supported
    (quietGuessLaw false response players).support_nonempty.choose_spec
  have observed := congrArg (fun view : PlayerView nativeGraph =>
    bobPublicationRef.get? view.observation.store) views
  change bobPublicationRef.get? (nativeGraph.playerStore bob next.application.config.store) =
    bobPublicationRef.get? (nativeGraph.playerStore bob
      ((quietGuessLaw false response players).support_nonempty.choose).application.config.store)
    at observed
  rw [bobPublicationRef.get?_playerStore bob _ trivial,
    bobPublicationRef.get?_playerStore bob _ trivial] at observed
  exact congrArg (fun value => value.getD .failure) observed

end VegasTests.MonitoredGuessing
