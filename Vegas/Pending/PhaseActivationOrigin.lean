/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceProgress
import Vegas.Pending.ReactiveServiceOpportunity

/-! # Activation origins across physical phase rollback

Rollback may discard semantic completion, but every retained timer belongs to
an actually ready middle state. Restored timers begin at the physical clock.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

omit [DecidableEq Player] in
/-- A genuine middle timer allows origin composition even when a reset discards
its semantic completion set. -/
theorem ActivationOrigin.trans_of_invariant {inputs : graph.Inputs}
    {before middle after : State graph} (first : ActivationOrigin before middle)
    (second : ActivationOrigin middle after) (valid : middle.Invariant inputs)
    (clock : before.clock ≤ middle.clock) : ActivationOrigin before after := by
  intro event entered activated unfinished
  rcases second event entered activated unfinished with retained | created
  · exact first event entered retained
      ((valid.activated_iff event).mp (by simp only [retained, Option.isSome_some])).1.1
  · exact Or.inr (clock.trans created)

end State

namespace RuntimePhase

theorem drainFuel_activationOrigin (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ActivationOrigin state.native (phase.drainFuel fuel state).native := by
  induction fuel generalizing state with
  | zero => exact State.activationOrigin_of_activatedEq rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        have eligible := (Classical.choose_spec pending).2
        obtain ⟨owner, acting, _⟩ := eligible.owned
        have first := State.activationOrigin_of_refreshEq
          (state.native.completeFailure_activated _ eligible.1 acting)
        have progress := state.native.completeFailure_progress valid _ eligible.1 acting
        exact first.trans_of_invariant (ih _ progress.invariant) progress.invariant
          (by rw [progress.clock]; omega)
      · exact State.activationOrigin_of_activatedEq rfl

theorem drain_activationOrigin (phase : RuntimePhase graph) (state : RecoveryState graph)
    {inputs : graph.Inputs} (valid : state.native.Invariant inputs) :
    State.ActivationOrigin state.native (phase.drain state).native :=
  phase.drainFuel_activationOrigin _ state valid

end RuntimePhase

namespace PhaseRuntimeState

omit [DecidableEq Player] in
theorem restore_activationOrigin (entry current : RecoveryState graph) :
    State.ActivationOrigin current.native (restore entry current).native := by
  intro event entered activated _
  right
  change State.refreshActivated entry.native.config current.native.clock
    (fun _ => none) event = some entered at activated
  unfold State.refreshActivated at activated
  split at activated
  · cases actor : graph.actor? event with
    | none => simp only [actor, reduceCtorEq] at activated
    | some owner =>
        rw [actor] at activated
        have same : current.native.clock = entered := Option.some.inj activated
        exact same.le
  · simp only [reduceCtorEq] at activated

/-- Every physical phase closure retains an old timer or starts a timer no
earlier than the actual clock at entry, including exhausted and retry closure. -/
theorem settle_activationOrigin (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (saved : entry.native.Invariant inputs)
    (active : current.native.Invariant inputs) :
    State.ActivationOrigin current.native
      (settle phases generation entry current retired).current.native := by
  induction phases generalizing generation entry current retired with
  | nil => exact State.activationOrigin_of_activatedEq rfl
  | cons phase remaining ih =>
      have drained := phase.drain_invariant current active
      have first := phase.drain_activationOrigin current active
      have clock : current.native.clock ≤ (phase.drain current).native.clock := by
        rw [(phase.drain_tables current).2.2]
      simp only [settle]
      split
      · split
        · have restored := restore_invariant entry (phase.drain current) saved
          have rebuilt := phase.drain_invariant _ restored
          have restoring := restore_activationOrigin entry (phase.drain current)
          have rebuilding := phase.drain_activationOrigin
            (restore entry (phase.drain current)) restored
          have throughRestore := first.trans_of_invariant restoring drained clock
          have throughRebuild := throughRestore.trans_of_invariant rebuilding restored clock
          have rebuildClock : current.native.clock ≤
              (phase.drain (restore entry (phase.drain current))).native.clock := by
            rw [(phase.drain_tables _).2.2]
            exact clock
          split
          · exact throughRebuild
          · exact throughRebuild.trans_of_invariant (ih _ _ _ _ rebuilt rebuilt)
              rebuilt rebuildClock
        · exact first.trans_of_invariant (ih _ _ _ _ drained drained) drained clock
      · exact first

end PhaseRuntimeState

/-- Actual private submissions, accepted packets, clock/sample/expiry commands,
and internal rollback all respect physical activation provenance. -/
theorem phaseApplication_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      ∀ inputs, before.Invariant inputs →
        State.ActivationOrigin before.current.native after.current.native) where
  refl _state _ _ := State.activationOrigin_of_activatedEq rfl
  submit state who submission _ valid := State.activationOrigin_of_activatedEq
    (congrArg PublicView.activatedAt ((submitStep_publicView
      (submission.call.register state.current.native who) who submission.call.packet).trans
        (submission.call.register_facts who state.current.native).2))
  handle state message next accepted _ valid := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have first := State.activationOrigin_of_refreshEq
        (handle_clock_activated runtime state.current.native native
          ⟨message.id, message.payload.packet.call⟩ handled).2
      have middle := handle_invariant runtime state.current.native native
        ⟨message.id, message.payload.packet.call⟩ valid.active handled
      exact first.trans_of_invariant
        (PhaseRuntimeState.settle_activationOrigin _ _ _ _ _ valid.saved middle) middle
        (handle_clock_activated runtime state.current.native native
          ⟨message.id, message.payload.packet.call⟩ handled).1.ge
    · cases accepted
  environment state command next reached _ valid := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, moved, rfl⟩ := reached
      have first : State.ActivationOrigin state.current.native native := by
        cases command with
        | advanceClock =>
            cases (PMF.mem_support_pure_iff _ _).mp moved
            exact State.activationOrigin_of_activatedEq rfl
        | executeSample event =>
            obtain ⟨_, stutter | changed⟩ := runtime.environmentStep_executeSample_config_activated
              state.current.native native event moved
            · exact State.activationOrigin_of_activatedEq stutter.2
            · obtain ⟨_, _, _, activated⟩ := changed
              exact State.activationOrigin_of_refreshEq activated
        | expire event =>
            obtain ⟨_, stutter | changed⟩ := runtime.environmentStep_expire_config_activated
              state.current.native native event moved
            · exact State.activationOrigin_of_activatedEq stutter.2
            · obtain ⟨_, _, _, activated⟩ := changed
              exact State.activationOrigin_of_refreshEq activated
      have middle := environmentStep_invariant runtime state.current.native native
        command valid.active moved
      exact first.trans_of_invariant
        (PhaseRuntimeState.settle_activationOrigin _ _ _ _ _ valid.saved middle) middle
        (by rw [environmentStep_clock runtime state.current.native native command moved]; omega)
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact State.activationOrigin_of_activatedEq rfl

end Vegas.EventGraphRuntime
