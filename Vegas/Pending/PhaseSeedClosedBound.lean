/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseServiceProgress
import Vegas.Pending.PhaseFrontier

/-! # Ready-time bounds retained by actual closed physical coordinates

A closed tick retains its original namespace and ready clock. Completion may
retire that namespace, but neither an unrelated service nor a private response
can make the same coordinate forget its original deadline comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

structure ClosedCoordinateBound (runtime : EventGraphRuntime graph) (tick entered : Nat)
    (coordinate : CommitAttemptEvent graph) (state : PhaseRuntimeState graph) : Prop where
  clock : tick ≤ state.current.native.clock
  entered_le : entered ≤ tick
  generation : coordinate.attempt.generation ≤ state.attempt.generation
  phase : coordinate.attempt.phase ≤ state.attempt.phase
  event : coordinate.attempt = state.attempt →
    coordinate.event ∈ state.current.native.config.cut.completed ∨
      state.current.native.config.cut.Ready coordinate.event ∧
        state.current.native.activatedAt coordinate.event = some entered ∧
          tick - entered < runtime.deadline coordinate.event

namespace ClosedCoordinateBound

omit [DecidableEq Player] in
private theorem transport {inputs : graph.Inputs} {tick entered : Nat}
    {coordinate : CommitAttemptEvent graph} {before after : PhaseRuntimeState graph}
    (valid : ClosedCoordinateBound runtime tick entered coordinate before)
    (namespaceProgress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (clockProgress : before.current.native.clock ≤ after.current.native.clock)
    (service : before.attempt = after.attempt →
      ∃ ticks, State.ServiceProgress inputs ticks before.current.native after.current.native) :
    ClosedCoordinateBound runtime tick entered coordinate after := by
  refine ⟨valid.clock.trans clockProgress, valid.entered_le,
    valid.generation.trans namespaceProgress.1,
    valid.phase.trans namespaceProgress.2, ?_⟩
  intro current
  have generationEq : before.attempt.generation = after.attempt.generation :=
    Nat.le_antisymm namespaceProgress.1 (by rw [← current]; exact valid.generation)
  have phaseEq : before.attempt.phase = after.attempt.phase :=
    Nat.le_antisymm namespaceProgress.2 (by rw [← current]; exact valid.phase)
  have same : before.attempt = after.attempt :=
    congrArg₂ CommitAttemptId.mk phaseEq generationEq
  obtain ⟨ticks, progress⟩ := service same
  rcases valid.event (current.trans same.symm) with completed | active
  · exact Or.inl (progress.completed completed)
  · obtain ⟨ready, activated, deadline⟩ := active
    by_cases completed : coordinate.event ∈ after.current.native.config.cut.completed
    · exact Or.inl completed
    · right
      have remains := progress.ready_or_completed coordinate.event ready
      rcases remains with impossible | readyAfter
      · exact False.elim (completed impossible)
      · exact ⟨readyAfter, progress.activated coordinate.event entered activated completed,
          deadline⟩

/-- An arbitrary actual player response cannot invalidate an earlier tick's
ready-time bound, even when it prepares unusable raw candidates. -/
theorem respond {inputs : graph.Inputs} {tick entered : Nat} {coordinate : CommitAttemptEvent graph}
    (execution : (app).Execution) (who : Player) (action : (app).Action)
    (valid : execution.application.Invariant inputs) (ordered : execution.application.Ordered)
    (closed : ClosedCoordinateBound runtime tick entered coordinate execution.application) :
    ClosedCoordinateBound runtime tick entered coordinate
      (execution.respond app who action).application := by
  apply transport runtime closed
  · exact (phaseApplication_namespace_progress runtime leaks).respond execution who action ordered
  · exact (phaseApplication_clock_monotone runtime leaks).respond execution who action
  · intro same
    exact (phaseApplication_serviceProgress runtime leaks).respond execution who action
      inputs valid ordered same

/-- Actual inclusion, expiry, sampling, clock and activation commands retain the
bound for every old physical coordinate; newly installed tags cannot match it. -/
theorem environmentStep {inputs : graph.Inputs} {tick entered : Nat}
    {coordinate : CommitAttemptEvent graph} (execution next : (app).Execution)
    (command : (app).Command) (valid : execution.application.Invariant inputs)
    (ordered : execution.application.Ordered)
    (reached : next ∈ (execution.environmentStep app command).support)
    (closed : ClosedCoordinateBound runtime tick entered coordinate execution.application) :
    ClosedCoordinateBound runtime tick entered coordinate next.application := by
  apply transport runtime closed
  · exact (phaseApplication_namespace_progress runtime leaks).environmentStep execution next
      command reached ordered
  · exact (phaseApplication_clock_monotone runtime leaks).environmentStep execution next command
      reached
  · intro same
    exact (phaseApplication_serviceProgress runtime leaks).environmentStep execution next command
      reached inputs valid ordered same

end ClosedCoordinateBound
end Vegas.EventGraphRuntime
