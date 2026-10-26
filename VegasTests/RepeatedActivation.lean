/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseService
import Interaction.ReactiveResponseCount

/-! # Responses can outnumber unfinished source events -/

noncomputable section

namespace VegasTests.RepeatedActivation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability
open Vegas.Examples.SequentialPhaseService

def repeatedActivation : app.Scheduler := fun _ _ => PMF.pure (.activate owner)

def silentRound (execution : app.Execution) : app.Execution :=
  { execution.respond app owner ⟨none⟩ with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate owner⟩] }

theorem repeatedActivation_round (execution : app.Execution) :
    app.round repeatedActivation (fun _ => app.silentPolicy) execution =
      PMF.pure (silentRound execution) := by
  simp only [ReactiveApplication.round, repeatedActivation, PMF.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    show app.observePending = leaks from rfl, leaks, PMF.pure_map, MessageNetwork.learn_empty,
    ReactiveApplication.resume, ReactiveApplication.Command.actor?, ReactiveApplication.invoke,
    ReactiveApplication.silentPolicy, PMF.pure_bind, PMF.pure_map]
  rfl

theorem repeatedActivation_run_two (execution : app.Execution) :
    app.runRounds repeatedActivation (fun _ => app.silentPolicy) 2 execution =
      PMF.pure (silentRound (silentRound execution)) := by
  simp only [ReactiveApplication.runRounds, repeatedActivation_round, PMF.pure_bind]

/-- This is a legal prefix of the original source runtime, with two genuine
callbacks while its single publication remains unfinished. An event-count-only
response budget therefore needs additional scheduling hypotheses. -/
theorem responses_exceed_source_events : ∃ control : app.Control,
    Nonempty ((app.protocol initial 2 repeatedActivation).Trace (some control)) ∧
      control.execution.application.current.native.config.cut.Ready event ∧
      app.responseCount (some control) = 2 ∧
      compiled.order.eventCount < app.responseCount (some control) := by
  let starting := ReactiveApplication.Execution.initial app (initialState false)
  let final := silentRound (silentRound starting)
  have supported : final ∈
      (app.roundsFrom initial repeatedActivation (fun _ => app.silentPolicy) 2).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨initialState false, initialState_supported false, ?_⟩
    rw [repeatedActivation_run_two, PMF.mem_support_pure_iff]
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial 2 repeatedActivation
    (fun _ => app.silentPolicy) 2 (Nat.le_refl _) final supported
  refine ⟨⟨0, none, final⟩, ⟨by simpa only [Nat.sub_self] using trace⟩, ?_, ?_, ?_⟩
  · change (initialState false).current.native.config.cut.Ready event
    rw [initialState, PhaseRuntimeState.initial_current_sequential]
    change event ∉ (∅ : Finset compiled.EventId) ∧
      (∅ : Finset compiled.EventId) ⊆ ∅
    exact ⟨by simp, Finset.Subset.refl _⟩
  · change app.responseCount (some ⟨0, none, silentRound (silentRound starting)⟩) = 2
    simp [ReactiveApplication.responseCount, silentRound,
      ReactiveApplication.Execution.respond, starting, ReactiveApplication.Execution.initial]
  · change 1 < app.responseCount (some ⟨0, none, silentRound (silentRound starting)⟩)
    simp [ReactiveApplication.responseCount, silentRound,
      ReactiveApplication.Execution.respond, starting, ReactiveApplication.Execution.initial]

end VegasTests.RepeatedActivation
