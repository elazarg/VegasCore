/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeInvariant
import Vegas.EventGraph.PrivateInputs

/-! # One original input environment throughout every retired attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Retired attempts preserve the same original immutable graph inputs. -/
def RetiredInputs (inputs : graph.Inputs) (retired : List (RetiredCommitAttempt graph)) : Prop :=
  ∀ record ∈ retired, record.state.config.inputs = inputs

/-- Actual restore and phase-local completion do not change the original draw. -/
theorem settle_retiredInputs (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (saved : entry.native.Invariant inputs)
    (active : current.native.Invariant inputs) (archives : RetiredInputs inputs retired) :
    RetiredInputs inputs (settle phases generation entry current retired).retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact archives
  | cons phase remaining ih =>
      have drained := phase.drain_invariant current active
      have restored := restore_invariant entry (phase.drain current) saved
      have rebuilt := phase.drain_invariant (restore entry (phase.drain current)) restored
      have recorded : RetiredInputs inputs
          (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) := by
        intro record member
        rcases List.mem_append.mp member with old | new
        · exact archives record old
        · obtain rfl := List.mem_singleton.mp new
          exact drained.reachable.inputs_eq
      simp only [settle]
      split
      · split
        · split
          · exact recorded
          · exact ih _ _ _ _ rebuilt rebuilt recorded
        · exact ih _ _ _ _ drained drained archives
      · exact archives

end PhaseRuntimeState

/-- All physical operations preserve one original input environment in live,
saved and retired native configurations. -/
theorem phaseApplication_retiredInputs (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      ∃ inputs, state.Invariant inputs ∧ PhaseRuntimeState.RetiredInputs inputs state.retired) where
  submit state who material valid := by
    obtain ⟨inputs, native, archives⟩ := valid
    exact ⟨inputs, (phaseApplication_invariant runtime leaks inputs).submit
      state who material native, archives⟩
  handle state message next valid accepted := by
    obtain ⟨inputs, native, archives⟩ := valid
    refine ⟨inputs, (phaseApplication_invariant runtime leaks inputs).handle state message next
      native accepted, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      let nativeMessage : Message Player (Payload graph) :=
        ⟨message.id, message.payload.packet.call⟩
      exact PhaseRuntimeState.settle_retiredInputs _ _ _ _ _ native.saved
        (handle_invariant runtime state.current.native result nativeMessage native.active handled)
        archives
    · cases accepted
  environment state command next valid reached := by
    obtain ⟨inputs, native, archives⟩ := valid
    refine ⟨inputs, (phaseApplication_invariant runtime leaks inputs).environment state command next
      native reached, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact PhaseRuntimeState.settle_retiredInputs _ _ _ _ _ native.saved
        (environmentStep_invariant runtime state.current.native result command native.active
          supported) archives
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact archives

/-- An authentic archived attempt and the current native state share every
original input, including the owner's private setup values. -/
theorem phaseRetiredInputs_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PhaseRuntimeState.RetiredInputs control.execution.application.current.native.config.inputs
      control.execution.application.retired := by
  have invariant := phaseApplication_retiredInputs runtime leaks
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · obtain ⟨draw, native, archives⟩ := result
    rw [native.active.reachable.inputs_eq]
    exact archives
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    refine ⟨input, (PhaseRuntimeState.initial_invariant plan input).1, ?_⟩
    exact PhaseRuntimeState.settle_retiredInputs _ _ _ _ _ (State.initial_invariant input)
      (State.initial_invariant input) (fun _ impossible => by cases impossible)

end Vegas.EventGraphRuntime
