/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperOriginalContinuation

/-! # Original helper-prefix laws from the actual initialized five-command frames -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Every literal initial helper material gives a genuine original native frame.
This is derived from the existing initialized runner, not supplied as an image. -/
theorem initial_helper_frame_native_trace (seed : Seeds) (hidden : Player)
    (material : WitnessedSubmission graph) :
    Nonempty ((app.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - 5, none, initialHelperFrame hidden material⟩)) := by
  let players : Player → app.Policy := fun owner _ _ =>
    PMF.pure (if owner = hidden then ⟨some material⟩ else ⟨none⟩)
  have reached : initialHelperFrame hidden material ∈
      (app.runRounds (family seed) players 5 initialExecution).support := by
    rw [first_five_rounds]
    simp only [players, PMF.pure_bind, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have rounds : initialHelperFrame hidden material ∈
      (app.roundsFrom initial (family seed) players 5).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using reached
  exact app.raw_trace_roundsFrom initial horizon (family seed) players 5
    (by change 5 ≤ 128; omega) _ rounds

private theorem initial_helper_frame_facts (hidden : Player)
    (material : WitnessedSubmission graph) :
    (initialHelperFrame hidden material).application.attempt = originalAttempt ∧
      (initialHelperFrame hidden material).application.current.excluded = ∅ ∧
      (initialHelperFrame hidden material).environmentRecall.length = 5 := by
  obtain ⟨candidates, frame⟩ := initialClockTwo_prepared
    (if alice = hidden then ⟨some material⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some material⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some material⟩ else ⟨none⟩)
  change (initialHelperFrame hidden material).application = preparedApplication 2 candidates
    at frame
  refine ⟨?_, ?_, ?_⟩
  · rw [frame]
    exact initialState_attempt
  · rw [frame]
    change initialState.current.excluded = ∅
    rw [initialState_eq]
  · exact initialClockTwo_length _ _ _

/-- The exact original continuation kernel from the initialized single-helper
frame depends on its public packet, independently of its hidden material.
All unsent raw strategies and the original fixed service seed stay unchanged. -/
theorem initial_helper_original_run_law (seed : Seeds) (players : Player → app.Policy)
    (hidden : Player)
    (waited : ∀ past view, players hidden past view = PMF.pure ⟨none⟩)
    (count : Nat) (bounded : count ≤ 19) (first second : WitnessedSubmission graph)
    (packet : app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second) :
    (app.runRounds (family seed) players count (initialHelperFrame hidden first)).map
        (originalHelperObservation hidden) =
      (app.runRounds (family seed) players count (initialHelperFrame hidden second)).map
        (originalHelperObservation hidden) := by
  obtain ⟨firstTrace⟩ := initial_helper_frame_native_trace seed hidden first
  obtain ⟨secondTrace⟩ := initial_helper_frame_native_trace seed hidden second
  have fuel : (horizon - 5 - count) + count = horizon - 5 := by
    change (128 - 5 - count) + count = 128 - 5
    omega
  have firstNative : (app.protocol initial horizon (family seed)).Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden first⟩) := by
    rw [fuel]
    exact firstTrace
  have secondNative : (app.protocol initial horizon (family seed)).Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden second⟩) := by
    rw [fuel]
    exact secondTrace
  have firstFacts := initial_helper_frame_facts hidden first
  have secondFacts := initial_helper_frame_facts hidden second
  exact original_helper_run_observation seed players hidden waited count (horizon - 5 - count)
    _ _ firstNative secondNative (initial_helper_frame_external hidden first second packet)
    firstFacts.1 secondFacts.1 firstFacts.2.1 secondFacts.2.1
    (by omega) (by omega)

open Classical in
/-- The same-packet preparation comparison retains the complete original
retirement boundary, including every unsent owner's current and recalled inputs.
It stops before any later publication can expose the helper's private value. -/
theorem initial_helper_original_stopped_law (seed : Seeds) (players : Player → app.Policy)
    (hidden : Player)
    (waited : ∀ past view, players hidden past view = PMF.pure ⟨none⟩)
    (count : Nat) (bounded : count ≤ 19) (first second : WitnessedSubmission graph)
    (packet : app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second) :
    (app.runUntil (family seed) players
      (fun current => current.application.attempt ≠ originalAttempt) count
      (initialHelperFrame hidden first)).map (phaseExternalObservation runtime leaks hidden) =
    (app.runUntil (family seed) players
      (fun current => current.application.attempt ≠ originalAttempt) count
      (initialHelperFrame hidden second)).map (phaseExternalObservation runtime leaks hidden) := by
  classical
  obtain ⟨firstTrace⟩ := initial_helper_frame_native_trace seed hidden first
  obtain ⟨secondTrace⟩ := initial_helper_frame_native_trace seed hidden second
  have fuel : (horizon - 5 - count) + count = horizon - 5 := by
    change (128 - 5 - count) + count = 128 - 5
    omega
  have firstNative : (app.protocol initial horizon (family seed)).Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden first⟩) := by
    rw [fuel]
    exact firstTrace
  have secondNative : (app.protocol initial horizon (family seed)).Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden second⟩) := by
    rw [fuel]
    exact secondTrace
  have firstFacts := initial_helper_frame_facts hidden first
  have secondFacts := initial_helper_frame_facts hidden second
  exact original_helper_stopped_observation seed players hidden waited count (horizon - 5 - count)
    _ _ firstNative secondNative (initial_helper_frame_external hidden first second packet)
    firstFacts.1 secondFacts.1 firstFacts.2.1 secondFacts.2.1 (by omega) (by omega)

end Vegas.Examples.CommitSeedBroadcast
