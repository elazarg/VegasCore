/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseExclusionRecord

/-! # Exact closed commitment intervals of retired attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Each retired native image ends at the high boundary of the commitment
phase named by its attempt address. -/
def RetiredBindingInterval (retired : List (RetiredCommitAttempt graph)) : Prop :=
  ∀ record ∈ retired, ∃ phase : RuntimePhase graph,
    record.attempt.phase = phase.low ∧ phase.kind = .commitment ∧
      record.state.config.cut.IsPrefix phase.high

omit [DecidableEq Player] in
/-- Recording a genuinely closed commitment phase retains the interval property. -/
theorem RetiredBindingInterval.append {retired : List (RetiredCommitAttempt graph)}
    (valid : RetiredBindingInterval retired) (phase : RuntimePhase graph)
    (generation : Nat) (state : State graph) (kind : phase.kind = .commitment)
    (closed : state.config.cut.IsPrefix phase.high) :
    RetiredBindingInterval (retired ++ [⟨⟨phase.low, generation⟩, state⟩]) := by
  intro record member
  rcases List.mem_append.mp member with old | added
  · exact valid record old
  · obtain rfl := List.mem_singleton.mp added
    exact ⟨phase, rfl, kind, closed⟩

/-- Actual settlement only archives the finished current commitment interval. -/
theorem settle_retiredBindingInterval (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : Frontier (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph))
    (archives : RetiredBindingInterval retired) :
    RetiredBindingInterval (settle phases generation entry current retired).retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact archives
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := frontier
      have drainedWithin := phase.drain_within current within
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          have recorded := archives.append phase generation (phase.drain current).native failure.1
            (phase.finished_prefix _ drainedWithin finished)
          have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
              phase.low phase.high := saved.within phase.nonempty.le
          have rebuiltWithin := phase.drain_within (restore entry (phase.drain current))
            restoredWithin
          split
          · exact recorded
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner member
              by_contra missing
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨member, missing⟩⟩
            have rebuiltFinished := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin rebuiltFinished)
            exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩ recorded
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩ archives
      · exact archives

end PhaseRuntimeState

/-- All raw application transitions preserve exact archived commitment intervals. -/
theorem phaseApplication_retiredBindingInterval (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.Frontier ∧ PhaseRuntimeState.RetiredBindingInterval state.retired) where
  submit state who material valid :=
    ⟨PhaseRuntimeState.submit_frontier state who material valid.1, valid.2⟩
  handle state message next valid accepted := by
    refine ⟨PhaseRuntimeState.handle_frontier runtime state next message valid.1 accepted, ?_⟩
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      exact PhaseRuntimeState.settle_retiredBindingInterval _ _ _ _ _
        (PhaseRuntimeState.raw_handle_frontier runtime state valid.1 _ native authorized handled)
        valid.2
    · cases accepted
  environment state command next valid reached := by
    refine ⟨PhaseRuntimeState.environment_frontier runtime state next command valid.1 reached, ?_⟩
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact PhaseRuntimeState.settle_retiredBindingInterval _ _ _ _ _
        (PhaseRuntimeState.raw_environment_frontier runtime state valid.1 _ native
          allowed supported)
        valid.2
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid.2

/-- Every retired attempt at an actual initialized raw history has the exact
closed commitment interval needed by the public binding-word readout. -/
theorem phaseRetiredBindingInterval_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PhaseRuntimeState.RetiredBindingInterval control.execution.application.retired := by
  have invariant := phaseApplication_retiredBindingInterval runtime leaks
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact result.2
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    refine ⟨PhaseRuntimeState.initial_frontier plan input, ?_⟩
    exact PhaseRuntimeState.settle_retiredBindingInterval _ _ _ _ _
      (PhaseRuntimeState.initial_checkpoint_frontier plan input)
      (fun _ impossible => by cases impossible)

end Vegas.EventGraphRuntime
