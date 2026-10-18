/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperInitialPreparation
import Interaction.ReactiveServiceRounds
import Interaction.ReactiveRawRoundTrace

/-! # The original helper channel stops before publication can expose its value -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Read only the original commitment experiment. Publication and retry states
are outside this channel, so their later private-value effects are not erased. -/
def originalHelperObservation (hidden : Player) (execution : app.Execution) :=
  if execution.application.attempt = originalAttempt then
    some (phaseExternalObservation runtime leaks hidden execution)
  else none

/-- A retired original namespace cannot return under any physical continuation.
The source is a genuine native prefix, and the original state is not refreshed. -/
theorem original_attempt_stays_retired (selected : app.Scheduler) (before : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some before))
    (retired : before.execution.application.attempt ≠ originalAttempt)
    (players : Player → app.Policy) (count : Nat) (after : app.Execution)
    (reached : after ∈ (app.runRounds selected players count before.execution).support) :
    after.application.attempt ≠ originalAttempt := by
  let start := before.execution.application.attempt
  let predicate : app.Execution → Prop := fun execution =>
    execution.application.Ordered ∧ start.generation ≤ execution.application.attempt.generation ∧
      start.phase ≤ execution.application.attempt.phase
  have invariant : app.ServiceInvariant selected predicate := by
    constructor
    · intro execution actor action valid
      have progress := (phaseApplication_namespace_progress runtime leaks).respond
        execution actor action valid.1
      exact ⟨(phaseApplication_seedOrder runtime leaks).respond execution actor action valid.1,
        valid.2.1.trans progress.1, valid.2.2.trans progress.2⟩
    · intro execution next command valid _selected supported
      have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
        execution next command supported valid.1
      exact ⟨(phaseApplication_seedOrder runtime leaks).environmentStep execution next command
        valid.1 supported, valid.2.1.trans progress.1, valid.2.2.trans progress.2⟩
  have valid : predicate before.execution :=
    ⟨(raw_phase_geometry selected before trace).1.adjacent, Nat.le_refl _, Nat.le_refl _⟩
  have afterValid := invariant.runRounds players count before.execution after valid reached
  intro returned
  have bound : start.generation ≤ 0 ∧ start.phase ≤ 0 := by
    simpa only [returned, originalAttempt] using afterValid.2
  have identity (attempt : CommitAttemptId) (phase : attempt.phase = 0)
      (generation : attempt.generation = 0) : attempt = originalAttempt := by
    rcases attempt with ⟨phaseValue, generationValue⟩
    change phaseValue = 0 at phase
    change generationValue = 0 at generation
    subst phaseValue
    subst generationValue
    rfl
  exact retired (identity start (Nat.eq_zero_of_le_zero bound.2)
    (Nat.eq_zero_of_le_zero bound.1))

/-- The full existing round law has zero original-helper observation after
retirement. This allows the prefix comparison to stop at actual admission,
without claiming hidden preparations remain opaque during publication. -/
theorem retired_helper_observation_run (selected : app.Scheduler) (before : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some before))
    (retired : before.execution.application.attempt ≠ originalAttempt)
    (players : Player → app.Policy) (count : Nat) (hidden : Player) :
    (app.runRounds selected players count before.execution).map
        (originalHelperObservation hidden) = PMF.pure none := by
  calc
    _ = (app.runRounds selected players count before.execution).map (fun _ => none) := by
      apply map_congr_on_support
      intro after reached
      exact ite_eq_right (original_attempt_stays_retired selected before trace retired players count
        after reached)
    _ = _ := PMF.map_const _ _

open Classical in
/-- Stopping the existing evaluator at original retirement changes no
original observation. Later publication effects are not equated. -/
theorem original_observation_rounds_stopped (selected : app.Scheduler)
    (players : Player → app.Policy) (hidden : Player) (count remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon selected).Trace
      (some ⟨remaining + count, none, execution⟩)) :
    (app.runRounds selected players count execution).map (originalHelperObservation hidden) =
      (app.runUntil selected players (fun current => current.application.attempt ≠ originalAttempt)
        count execution).map (originalHelperObservation hidden) := by
  classical
  let stop := fun current : app.Execution => current.application.attempt ≠ originalAttempt
  let deadline := execution.environmentRecall.length + count
  have length : deadline - execution.environmentRecall.length = count := by
    dsimp only [deadline]
    omega
  have rounds : app.runToHorizon selected players deadline execution =
      app.runRounds selected players count execution := by
    rw [ReactiveApplication.runToHorizon, length]
  have stopped : app.runUntilHorizon selected players stop deadline execution =
      app.runUntil selected players stop count execution := by
    rw [ReactiveApplication.runUntilHorizon, length]
  have decomposition := app.runToHorizon_eq_runUntilHorizon_bind selected players stop
    deadline execution
  rw [rounds, stopped] at decomposition
  rw [decomposition, PMF.map_bind]
  change ((app.runUntil selected players stop count execution).bind fun current =>
    (app.runToHorizon selected players deadline current).map (originalHelperObservation hidden)) =
      (app.runUntil selected players stop count execution).map (originalHelperObservation hidden)
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro current reached
  obtain retired | last :=
    app.runUntil_stopped selected players stop count execution current reached
  · obtain ⟨used, within, actual, _position⟩ :=
      app.runUntil_runRounds selected players stop count execution current reached
    have fuel : (remaining + (count - used)) + used = remaining + count := by omega
    have earlier : (app.protocol initial horizon selected).Trace
        (some ⟨(remaining + (count - used)) + used, none, execution⟩) := by
      rw [fuel]
      exact trace
    obtain ⟨currentTrace⟩ := app.raw_trace_runRounds initial horizon selected players
      (remaining + (count - used)) used execution current earlier actual
    change current.application.attempt ≠ originalAttempt at retired
    change (app.runRounds selected players (deadline - current.environmentRecall.length)
      current).map (originalHelperObservation hidden) = _
    rw [retired_helper_observation_run selected
      ⟨remaining + (count - used), none, current⟩ currentTrace retired players
        (deadline - current.environmentRecall.length) hidden]
    simp only [Function.comp_def, originalHelperObservation, retired, ite_false]
  · change current.environmentRecall.length = deadline at last
    rw [ReactiveApplication.runToHorizon, last, Nat.sub_self,
      ReactiveApplication.runRounds, PMF.pure_map]
    rfl

end Vegas.Examples.CommitSeedBroadcast
