/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseRawCheckpoint
import Vegas.Pending.PhaseBindingSubmittedPreservation

/-! # Archived accepted meanings remain readable in the permanent private catalogue -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Retired native results are genuine binding states. Every fixed archived
candidate keeps its original meaning in the current permanent catalogue. -/
def RetiredBindings (current : State graph) (retired : List (RetiredCommitAttempt graph)) : Prop :=
  ∀ record ∈ retired, record.state.BindingInvariant ∧
    (∃ inputs, record.state.Invariant inputs) ∧ KeepsFixedCandidates record.state current

namespace RetiredBindings

omit [DecidableEq Player] in
/-- Extending a permanent catalogue retains every archived typed meaning. -/
theorem rebase {before after : State graph} {retired : List (RetiredCommitAttempt graph)}
    (valid : RetiredBindings before retired) (fixed : KeepsFixedCandidates before after) :
    RetiredBindings after retired := by
  intro record member
  obtain ⟨binding, native, earlier⟩ := valid record member
  refine ⟨binding, native, ?_⟩
  intro handle known
  have knownBefore : before.candidates.lookup handle ≠ .fresh := by
    rw [earlier handle known]
    exact known
  exact (fixed handle knownBefore).trans (earlier handle known)

omit [DecidableEq Player] in
/-- Appending the actual retired native image records its validity and its
unchanged original candidate meanings. -/
theorem append {current : State graph} {retired : List (RetiredCommitAttempt graph)}
    (valid : RetiredBindings current retired) (record : RetiredCommitAttempt graph)
    (binding : record.state.BindingInvariant) {inputs} (native : record.state.Invariant inputs)
    (fixed : KeepsFixedCandidates record.state current) :
    RetiredBindings current (retired ++ [record]) := by
  intro other member
  rcases List.mem_append.mp member with old | new
  · exact valid other old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨binding, ⟨inputs, native⟩, fixed⟩

end RetiredBindings

/-- Settlement records the actual valid native result and preserves candidate
meanings through restore, automatic rebuild, and every later phase closure. -/
theorem settle_retiredBindings (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs} (savedNative : entry.native.Invariant inputs)
    (activeNative : current.native.Invariant inputs)
    (savedBinding : entry.native.BindingInvariant) (activeBinding : current.native.BindingInvariant)
    (fixed : KeepsFixedCandidates entry.native current.native)
    (archives : RetiredBindings current.native retired) :
    RetiredBindings (settle phases generation entry current retired).current.native
      (settle phases generation entry current retired).retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact archives
  | cons phase remaining ih =>
      have drainedNative := phase.drain_invariant current activeNative
      have drainedBinding := phase.drain_bindingInvariant current activeBinding
      have drainedFixed : KeepsFixedCandidates current.native (phase.drain current).native := by
        intro handle known
        rw [(phase.drain_tables current).2.1]
      have savedFixed : KeepsFixedCandidates entry.native (phase.drain current).native := by
        intro handle known
        rw [(phase.drain_tables current).2.1]
        exact fixed handle known
      have restoredNative := restore_invariant entry (phase.drain current) savedNative
      have restoredBinding := restore_bindingInvariant entry (phase.drain current)
        savedBinding savedFixed
      have rebuiltNative := phase.drain_invariant (restore entry (phase.drain current))
        restoredNative
      have rebuiltBinding := phase.drain_bindingInvariant (restore entry (phase.drain current))
        restoredBinding
      have rebuiltFixed : KeepsFixedCandidates (phase.drain current).native
          (phase.drain (restore entry (phase.drain current))).native := by
        intro handle known
        rw [(phase.drain_tables _).2.1]
        rfl
      have drainedArchives := archives.rebase drainedFixed
      have rebuiltArchives := (drainedArchives.rebase rebuiltFixed).append
        ⟨⟨phase.low, generation⟩, (phase.drain current).native⟩ drainedBinding drainedNative
          rebuiltFixed
      simp only [settle]
      split
      · split
        · split
          · exact rebuiltArchives
          · exact ih _ _ _ _ rebuiltNative rebuiltNative rebuiltBinding rebuiltBinding
              (fun _ _ => rfl) rebuiltArchives
        · exact ih _ _ _ _ drainedNative drainedNative drainedBinding drainedBinding
            (fun _ _ => rfl) drainedArchives
      · exact drainedArchives

end PhaseRuntimeState

/-- Every actual operation retains the archived native binding meanings,
including arbitrary raw private preparation and semantic rollback. -/
theorem phaseApplication_retiredBindings (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      (∃ inputs, state.Invariant inputs) ∧ state.BindingRecord ∧
        PhaseRuntimeState.RetiredBindings state.current.native state.retired) where
  submit state who material valid := by
    obtain ⟨⟨inputs, native⟩, binding, archives⟩ := valid
    refine ⟨⟨inputs, (phaseApplication_invariant runtime leaks inputs).submit state who material
      native⟩, (phaseApplication_bindingInvariant runtime leaks).submit state who material binding,
      ?_⟩
    exact archives.rebase ((phaseApplication_preservesFixedCandidates runtime leaks).submit
      state who material)
  handle state message next valid accepted := by
    obtain ⟨⟨inputs, native⟩, binding, archives⟩ := valid
    refine ⟨⟨inputs, (phaseApplication_invariant runtime leaks inputs).handle state message next
      native accepted⟩, (phaseApplication_bindingInvariant runtime leaks).handle state message next
        binding accepted, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      let nativeMessage : Message Player (Payload graph) :=
        ⟨message.id, message.payload.packet.call⟩
      have rawBinding := binding.inclusionResult runtime state nativeMessage result handled
      have rawNative := handle_invariant runtime state.current.native result nativeMessage
        native.active handled
      have currentFixed : KeepsFixedCandidates state.current.native result := by
        intro handle known
        exact handle_lookup_of_not_fresh runtime _ result nativeMessage handle known handled
      exact PhaseRuntimeState.settle_retiredBindings _ _ _ _ _ native.saved rawNative
        rawBinding.saved rawBinding.active rawBinding.fixed (archives.rebase currentFixed)
    · cases accepted
  environment state command next valid reached := by
    obtain ⟨⟨inputs, native⟩, binding, archives⟩ := valid
    refine ⟨⟨inputs, (phaseApplication_invariant runtime leaks inputs).environment state
      command next native reached⟩,
      (phaseApplication_bindingInvariant runtime leaks).environment state command next
        binding reached, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      have rawBinding := binding.environmentResult runtime state command result supported
      have rawNative := environmentStep_invariant runtime state.current.native result command
        native.active supported
      have currentFixed : KeepsFixedCandidates state.current.native result := by
        intro handle known
        rw [(environmentStep_tables runtime _ result command supported).2]
      exact PhaseRuntimeState.settle_retiredBindings _ _ _ _ _ native.saved rawNative
        rawBinding.saved rawBinding.active rawBinding.fixed (archives.rebase currentFixed)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact archives

/-- Every archived attempt at an authentic initialized raw history is reachable,
binding-valid, and readable from the current immutable candidate catalogue. -/
theorem phaseRetiredBindings_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PhaseRuntimeState.RetiredBindings control.execution.application.current.native
      control.execution.application.retired := by
  have invariant := phaseApplication_retiredBindings runtime leaks
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact result.2.2
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    refine ⟨⟨input, (PhaseRuntimeState.initial_invariant plan input).1⟩,
      PhaseRuntimeState.initial_bindingRecord plan input, ?_⟩
    exact PhaseRuntimeState.settle_retiredBindings _ _ _ _ _
      (State.initial_invariant input) (State.initial_invariant input)
      (State.initial_bindingInvariant input)
      (State.initial_bindingInvariant input) (fun _ _ => rfl)
      (fun _ impossible => by cases impossible)

end Vegas.EventGraphRuntime
