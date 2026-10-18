/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialResponses
import Vegas.Pending.ReactiveSignedCommitments

/-! # The actual initial raw preparations before the clock-two callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem native_eq_of_config_public (left right : EventGraphRuntime.State graph)
    (config : left.config = right.config) (publicView : left.publicView = right.publicView) :
    left = { right with candidates := left.candidates } := by
  have accepted := congrArg PublicView.accepted publicView
  have clock := congrArg PublicView.clock publicView
  have entered := congrArg PublicView.activatedAt publicView
  cases left
  cases right
  cases config
  cases accepted
  cases clock
  cases entered
  rfl

/-- All initial raw preparation is retained, including arbitrary hidden values
and unusable handles. Only its catalogue differs from the initial native frame. -/
def preparedApplication (clock : Nat)
    (candidates : CommitmentCandidates Player (CandidateSlot graph) (Raw simpleExpr)) : app.State :=
  { initialState with current := { initialState.current with native :=
      { initialState.current.native with candidates := candidates, clock := clock } } }

private theorem native_submit_shape (state : EventGraphRuntime.State graph) (owner : Player)
    (material : WitnessedSubmission graph) :
    submitStep (material.call.register state owner) owner material.call.packet =
      { state with candidates :=
          (submitStep (material.call.register state owner) owner
            material.call.packet).candidates } :=
  native_eq_of_config_public _ _
    ((submitStep_config ..).trans (material.call.register_facts owner state).1)
    ((submitStep_publicView ..).trans (material.call.register_facts owner state).2)

private theorem prepared_respond (execution : app.Execution) (clock : Nat)
    (candidates : CommitmentCandidates Player (CandidateSlot graph) (Raw simpleExpr))
    (frame : execution.application = preparedApplication clock candidates)
    (owner : Player) (action : app.Action) :
    ∃ nextCandidates, (execution.respond app owner action).application =
      preparedApplication clock nextCandidates := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨candidates, frame⟩
  | some material =>
      refine ⟨(submitStep (material.call.register execution.application.current.native owner)
        owner material.call.packet).candidates, ?_⟩
      change { execution.application with current := { execution.application.current with
        native := submitStep (material.call.register execution.application.current.native owner)
          owner material.call.packet } } = _
      rw [native_submit_shape, frame]
      rfl

private theorem prepared_normalize (clock : Nat)
    (candidates : CommitmentCandidates Player (CandidateSlot graph) (Raw simpleExpr)) :
    (preparedApplication clock candidates).normalize = preparedApplication clock candidates := by
  let native : EventGraphRuntime.State graph :=
    { State.initial (encodeInputs (Env.empty (CellVal simpleExpr))) with
      candidates := candidates, clock := clock }
  have shaped : preparedApplication clock candidates =
      ⟨[commitmentPhase, publicationPhase], 0,
        ⟨State.initial (encodeInputs (Env.empty (CellVal simpleExpr))), ∅⟩,
        ⟨native, ∅⟩, []⟩ := by rw [preparedApplication, initialState_eq]
  have drained : commitmentPhase.drain (⟨native, ∅⟩ : RecoveryState graph) = ⟨native, ∅⟩ := by
    apply RuntimePhase.drain_eq_of_clear
    intro event eligible
    rcases eligible.2 with ⟨_ready, excluded⟩
    cases actor : graph.actor? event <;> simp [actor] at excluded
  have unfinished : ¬ commitmentPhase.Finished (⟨native, ∅⟩ : RecoveryState graph) := by
    intro finished
    have inside : bindingEvent alice ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase _).mpr
      change 0 ≤ 0 ∧ 0 < 3
      omega
    have member := finished inside
    change bindingEvent alice ∈ (∅ : Finset graph.EventId) at member
    exact Finset.notMem_empty _ member
  rw [shaped, PhaseRuntimeState.normalize, PhaseRuntimeState.settle, drained,
    ite_eq_right unfinished]

theorem advance_prepared (execution : app.Execution) (clock : Nat)
    (candidates : CommitmentCandidates Player (CandidateSlot graph) (Raw simpleExpr))
    (frame : execution.application = preparedApplication clock candidates) :
    (advance execution).application = preparedApplication (clock + 1) candidates := by
  change (PhaseBindingRepair.rawClock runtime leaks execution).application.normalize = _
  have updated : (PhaseBindingRepair.rawClock runtime leaks execution).application =
      preparedApplication (clock + 1) candidates := by
    change { execution.application with current := { execution.application.current with native :=
      { execution.application.current.native with
        clock := execution.application.current.native.clock + 1 } } } = _
    rw [frame]
    rfl
  rw [updated, prepared_normalize]

theorem afterInitialResponses_prepared (first second third : app.Action) :
    ∃ candidates, (afterInitialResponses first second third).application =
      preparedApplication 0 candidates := by
  have initialFrame : initialExecution.application =
      preparedApplication 0 initialState.current.native.candidates := by
    change initialState = preparedApplication 0 initialState.current.native.candidates
    rw [preparedApplication, initialState_eq]
    rfl
  obtain ⟨one, oneFrame⟩ := prepared_respond initialAliceCallback 0 _ initialFrame alice first
  obtain ⟨two, twoFrame⟩ := prepared_respond (initialBobCallback first) 0 _ oneFrame bob second
  exact prepared_respond (initialCarolCallback first second) 0 _ twoFrame carol third

theorem afterInitialResponses_length (first second third : app.Action) :
    (afterInitialResponses first second third).environmentRecall.length = 3 := by
  simp only [afterInitialResponses, initialCarolCallback, initialBobCallback, initialAliceCallback,
    app.respond_environmentRecall, completeActivation,
    ReactiveApplication.Execution.sampledActivation,
    initialExecution, ReactiveApplication.Execution.initial, List.length_append,
    List.length_singleton, List.length_nil]

/-- The physical frame after the same three literal raw actions and two actual
clock commands. No packet is removed and no preparation is replaced. -/
def initialClockTwo (first second third : app.Action) : app.Execution :=
  advance (advance (afterInitialResponses first second third))

theorem initialClockTwo_prepared (first second third : app.Action) :
    ∃ candidates, (initialClockTwo first second third).application =
      preparedApplication 2 candidates := by
  obtain ⟨candidates, frame⟩ := afterInitialResponses_prepared first second third
  exact ⟨candidates, advance_prepared _ 1 candidates (advance_prepared _ 0 candidates frame)⟩

theorem initialClockTwo_publicView (first second third : app.Action) :
    (initialClockTwo first second third).application.publicView =
      quietStart.application.publicView := by
  obtain ⟨candidates, frame⟩ := initialClockTwo_prepared first second third
  rw [frame, quietStart_application]
  rfl

theorem initialClockTwo_length (first second third : app.Action) :
    (initialClockTwo first second third).environmentRecall.length = 5 := by
  change ((afterInitialResponses first second third).environmentRecall ++
    [(⟨(afterInitialResponses first second third).observeEnvironment app,
      .application .advanceClock⟩ : app.EnvironmentEntry)] ++
    [(⟨(advance (afterInitialResponses first second third)).observeEnvironment app,
      .application .advanceClock⟩ : app.EnvironmentEntry)]).length = 5
  rw [List.length_append, List.length_append, afterInitialResponses_length]
  rfl

private theorem initial_advance_choice (seed : Seeds) (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = 3 ∨ execution.environmentRecall.length = 4) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application .advanceClock) := by
  unfold family choose
  change PMF.pure (if execution.application.attempt = originalAttempt then _ else _) = _
  rw [ite_eq_left original]
  rcases position with position | position <;> rw [position] <;> rfl

private theorem initial_advance_round (seed : Seeds) (players : Player → app.Policy)
    (execution : app.Execution) (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = 3 ∨ execution.environmentRecall.length = 4) :
    app.round (family seed) players execution = PMF.pure (advance execution) := by
  unfold ReactiveApplication.round
  rw [initial_advance_choice seed execution original position, PMF.pure_bind,
    ReactiveApplication.dispatch, advance_law, PMF.pure_bind]
  rfl

theorem initial_raw_advances (seed : Seeds) (players : Player → app.Policy)
    (first second third : app.Action) :
    app.runRounds (family seed) players 2 (afterInitialResponses first second third) =
      PMF.pure (initialClockTwo first second third) := by
  obtain ⟨candidates, frame⟩ := afterInitialResponses_prepared first second third
  have original : (afterInitialResponses first second third).application.attempt =
      originalAttempt := by rw [frame]; exact initialState_attempt
  have nextOriginal : (advance (afterInitialResponses first second third)).application.attempt =
      originalAttempt := by rw [advance_prepared _ 0 candidates frame]; exact initialState_attempt
  have nextLength : (advance (afterInitialResponses first second third)).environmentRecall.length =
      4 := by
    change ((afterInitialResponses first second third).environmentRecall ++ [_]).length = 4
    rw [List.length_append, afterInitialResponses_length]
    rfl
  rw [ReactiveApplication.runRounds, initial_advance_round seed players _ original
    (Or.inl (afterInitialResponses_length first second third)), PMF.pure_bind,
      ReactiveApplication.runRounds, initial_advance_round seed players _ nextOriginal
        (Or.inr nextLength), PMF.pure_bind]
  rfl

/-- The entire initial native prefix is independent of the original timing
seed, while retaining the genuine raw response kernels and their hidden material. -/
theorem first_five_rounds (seed : Seeds) (players : Player → app.Policy) :
    app.runRounds (family seed) players 5 initialExecution =
      (players alice [] (initialAliceCallback.observe app alice)).bind fun first =>
        (players bob [] ((initialBobCallback first).observe app bob)).bind fun second =>
          (players carol [] ((initialCarolCallback first second).observe app carol)).map
            (initialClockTwo first second) := by
  rw [show 5 = 3 + 2 by decide, app.runRounds_add, first_three_rounds,
    PMF.bind_bind]
  apply bind_congr_on_support
  intro first _first
  rw [PMF.bind_bind]
  apply bind_congr_on_support
  intro second _second
  rw [PMF.bind_map]
  change (players carol [] ((initialCarolCallback first second).observe app carol)).bind
    (fun third => app.runRounds (family seed) players 2
      (afterInitialResponses first second third)) = _
  simp_rw [initial_raw_advances]
  rfl

theorem first_five_seed_independent (first second : Seeds) (players : Player → app.Policy) :
    app.runRounds (family first) players 5 initialExecution =
      app.runRounds (family second) players 5 initialExecution := by
  rw [first_five_rounds, first_five_rounds]

end Vegas.Examples.CommitSeedBroadcast
