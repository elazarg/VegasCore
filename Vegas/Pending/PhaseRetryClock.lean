/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseActivationOrigin

/-! # Fresh retry timers at the actual physical rollback clock -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

omit [DecidableEq Player] in
private theorem timers_lowerBound_of_origin {inputs : graph.Inputs} {bound : Nat}
    {before after : State graph} (origin : ActivationOrigin before after)
    (valid : after.Invariant inputs)
    (lower : ∀ event entered, before.activatedAt event = some entered → bound ≤ entered)
    (clock : bound ≤ before.clock) :
    ∀ event entered, after.activatedAt event = some entered → bound ≤ entered := by
  intro event entered activated
  have ready := ((valid.activated_iff event).mp
    (by simp only [activated, Option.isSome_some])).1
  rcases origin event entered activated ready.1 with retained | created
  · exact lower event entered retained
  · exact clock.trans created

end State

namespace PhaseRuntimeState

omit [DecidableEq Player] in
private theorem restore_timers_lowerBound (entry current : RecoveryState graph) :
    ∀ event entered, (restore entry current).native.activatedAt event = some entered →
      current.native.clock ≤ entered := by
  intro event entered activated
  have origin := restore_activationOrigin entry
    ({ current with native := { current.native with activatedAt := fun _ => none } } :
      RecoveryState graph)
  rcases origin event entered activated (by
      intro done
      change State.refreshActivated entry.native.config current.native.clock
        (fun _ => none) event = some entered at activated
      simp only [State.refreshActivated, show ¬ entry.native.config.cut.Ready event
        from fun ready => ready.1 done, ↓reduceDIte, reduceCtorEq] at activated) with
    retained | created
  · cases retained
  · exact created

private theorem settle_timers_lowerBound (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (saved : entry.native.Invariant inputs)
    (active : current.native.Invariant inputs) (bound : Nat)
    (lower : ∀ event entered, current.native.activatedAt event = some entered → bound ≤ entered)
    (clock : bound ≤ current.native.clock) :
    ∀ event entered,
      (settle phases generation entry current retired).current.native.activatedAt event =
        some entered →
        bound ≤ entered :=
  State.timers_lowerBound_of_origin (settle_activationOrigin _ _ _ _ _ saved active)
    (settle_invariant _ _ _ _ _ saved active).active lower clock

/-- Whenever normalization increments the global attempt generation, every
live timer belongs to a fresh attempt begun at the entry physical clock. -/
theorem settle_retry_timers (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (saved : entry.native.Invariant inputs)
    (active : current.native.Invariant inputs)
    (changed : (settle phases generation entry current retired).generation ≠ generation) :
    ∀ event entered,
      (settle phases generation entry current retired).current.native.activatedAt event =
        some entered →
        current.native.clock ≤ entered := by
  induction phases generalizing generation entry current retired with
  | nil => exact (changed rfl).elim
  | cons phase remaining ih =>
      have drained := phase.drain_invariant current active
      have restored := restore_invariant entry (phase.drain current) saved
      have rebuilt := phase.drain_invariant _ restored
      have restoring := restore_timers_lowerBound entry (phase.drain current)
      have rebuilding := State.timers_lowerBound_of_origin
        (phase.drain_activationOrigin (restore entry (phase.drain current)) restored)
        rebuilt restoring le_rfl
      have rebuiltClock : current.native.clock =
          (phase.drain (restore entry (phase.drain current))).native.clock := by
        rw [(phase.drain_tables _).2.2]
        exact (phase.drain_tables current).2.2.symm
      simp only [settle] at changed ⊢
      split
      · rename_i finished
        simp only [finished, ↓reduceIte] at changed
        split
        · split
          · simpa only [(phase.drain_tables current).2.2] using rebuilding
          · exact settle_timers_lowerBound _ _ _ _ _ rebuilt rebuilt current.native.clock
              (by simpa only [(phase.drain_tables current).2.2] using rebuilding) rebuiltClock.le
        · rename_i clean
          simp only [clean, ↓reduceIte] at changed
          intro event entered activated
          have lower := ih _ _ _ _ drained drained changed event entered activated
          rwa [(phase.drain_tables current).2.2] at lower
      · rename_i unfinished
        simp only [unfinished, ↓reduceIte, ne_eq, not_true_eq_false] at changed

/-- An actual accepted packet that retires the generation starts all live retry
timers at or after the same physical clock; catalogue and recall remain physical. -/
theorem handle_retry_timers (runtime : EventGraphRuntime graph) {inputs : graph.Inputs}
    (state next : PhaseRuntimeState graph) (valid : state.Invariant inputs)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next)
    (changed : next.generation ≠ state.generation) :
    ∀ event entered, next.current.native.activatedAt event = some entered →
      state.current.native.clock ≤ entered := by
  unfold handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have middle := handle_invariant runtime state.current.native native
      ⟨message.id, message.payload.packet.call⟩ valid.active handled
    have lower := settle_retry_timers _ _ _ _ _ valid.saved middle changed
    intro event entered activated
    have bound := lower event entered activated
    change native.clock ≤ entered at bound
    rwa [(handle_clock_activated runtime state.current.native native
      ⟨message.id, message.payload.packet.call⟩ handled).1] at bound
  · cases accepted

/-- Any physical environment operation that changes the generation begins
new live timers no earlier than the operation's entry clock. -/
theorem environment_retry_timers (runtime : EventGraphRuntime graph) {inputs : graph.Inputs}
    (state next : PhaseRuntimeState graph) (valid : state.Invariant inputs)
    (command : EnvironmentCommand graph)
    (reached : next ∈ (state.environment runtime command).support)
    (changed : next.generation ≠ state.generation) :
    ∀ event entered, next.current.native.activatedAt event = some entered →
      state.current.native.clock ≤ entered := by
  unfold environment at reached
  split at reached
  · rw [PMF.support_map] at reached
    obtain ⟨native, moved, rfl⟩ := reached
    have middle := environmentStep_invariant runtime state.current.native native
      command valid.active moved
    have lower := settle_retry_timers _ _ _ _ _ valid.saved middle changed
    intro event entered activated
    have bound := lower event entered activated
    change native.clock ≤ entered at bound
    rw [environmentStep_clock runtime state.current.native native command moved] at bound
    omega
  · cases (PMF.mem_support_pure_iff _ _).mp reached
    exact (changed rfl).elim

end PhaseRuntimeState
end Vegas.EventGraphRuntime
