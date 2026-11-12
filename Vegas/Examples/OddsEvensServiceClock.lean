module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensService
public import Vegas.Pending.ReactiveServiceProgress
public import Interaction.ReactiveRecordedEnvironment

@[expose] public section

/-! # Clock accounting for the concrete two-player forced-exit service -/

noncomputable section

namespace Vegas.Examples.OddsEvensService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

private theorem pending_head_ticks (view : app.EnvironmentView) :
    (reactiveTicks timeouts) leaks (app.pendingHeadCommand view) = 0 := by
  unfold ReactiveApplication.pendingHeadCommand
  split <;> rfl

theorem command_ticks (cursor : Nat) (view : app.EnvironmentView) :
    (reactiveTicks timeouts) leaks (command cursor view) =
      if cursor % width = width - 1 then 1 else 0 := by
  have bounded : cursor % width < width := Nat.mod_lt _ (by decide)
  dsimp only [command, width, packetBudget, cycles] at *
  split_ifs
  all_goals try rw [pending_head_ticks]
  all_goals simp_all only [reactiveTicks]
  all_goals omega

theorem cursor_cycle_succ (cursor : Nat) :
    (cursor + 1) / width = cursor / width +
      if cursor % width = width - 1 then 1 else 0 := by
  change (cursor + 1) / 71 = cursor / 71 + if cursor % 71 = 70 then 1 else 0
  split_ifs <;> omega

structure ClockAligned (inputs : compiled.Inputs) (origin : Nat) (execution : app.Execution) :
    Prop where
  valid : execution.application.Invariant inputs
  clock : execution.application.clock = origin + execution.environmentRecall.length / width

theorem clock_aligned_invariant (inputs : compiled.Inputs) (origin : Nat) :
    app.ServiceInvariant scheduler (ClockAligned inputs origin) where
  respond execution owner response aligned := by
    refine ⟨(reactiveStateInvariant timeouts leaks inputs).respond execution owner response
      aligned.valid, ?_⟩
    have progress := reactive_respond_progress timeouts leaks inputs execution owner response
      aligned.valid
    rw [progress.clock, Nat.add_zero, app.respond_environmentRecall]
    exact aligned.clock
  environment execution next selected aligned supported moved := by
    refine ⟨(reactiveStateInvariant timeouts leaks inputs).environmentStep execution next
      selected aligned.valid moved, ?_⟩
    have chosen : selected = command execution.environmentRecall.length
        (execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp supported
    have progress := reactive_environment_progress timeouts leaks inputs execution next
      selected aligned.valid moved
    rw [progress.clock, chosen, command_ticks, aligned.clock,
      app.environmentStep_environmentRecall execution next selected moved,
      List.length_append, List.length_singleton, cursor_cycle_succ]
    omega

theorem clock_history (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.application.clock =
      control.execution.environmentRecall.length / width := by
  have invariant : app.ServiceInvariant scheduler
      (fun execution => ∃ inputs, ClockAligned inputs 0 execution) := {
    respond := by
      intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (clock_aligned_invariant inputs 0).respond execution who action valid⟩
    environment := by
      intro execution next selected valid supported moved
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (clock_aligned_invariant inputs 0).environment execution next selected
        valid supported moved⟩ }
  have actual := invariant.history initial horizon (by
    intro state initialized
    rw [initial, Vegas.initialLaw, serviceInitialLaw, PMF.support_map] at initialized
    obtain ⟨input, _, rfl⟩ := initialized
    exact ⟨fixture.eventInputs input, State.initial_invariant _, by
      simp [ReactiveApplication.Execution.initial, State.initial]⟩) trace
  obtain ⟨_, valid⟩ := actual
  simpa only [Nat.zero_add] using valid.clock

end Vegas.Examples.OddsEvensService
