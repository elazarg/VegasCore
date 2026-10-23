/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.SuffixExclusionRecord
import Vegas.Pending.PhaseFrontier

/-! # Actual public misses at every installed phase and retry

Inherited exclusion is the checkpoint's permanent set. Actual new exclusion is
reconstructed from public failures in the current suffix, even after old failed
attempts have been removed from the semantic store and permanently archived.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Receipt provenance and rank-scoped public failures accompany the actual
saved/live frontiers. Retired failures are accounted for by inherited exclusion. -/
structure ExclusionRecord (state : PhaseRuntimeState graph) : Prop where
  frontier : state.Frontier
  saved : state.entry.native.ReceiptsComplete
  active : state.current.native.ReceiptsComplete
  installed : ∀ phase ∈ state.phases.head?,
    SuffixExclusionRecord phase.low state.entry.excluded state.current

omit [DecidableEq Player] in
theorem fresh_exclusionRecord (phases : List (RuntimePhase graph)) (generation : Nat)
    (current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : Frontier
      (⟨phases, generation, current, current, retired⟩ : PhaseRuntimeState graph))
    (receipts : current.native.ReceiptsComplete) :
    ExclusionRecord
      (⟨phases, generation, current, current, retired⟩ : PhaseRuntimeState graph) := by
  refine ⟨frontier, receipts, receipts, ?_⟩
  intro phase member
  cases phases with
  | nil => cases member
  | cons first rest =>
      have same : phase = first := by
        symm
        simpa only [List.head?_cons, Option.mem_some_iff] using member
      subst phase
      exact SuffixExclusionRecord.of_prefix receipts frontier.positioned.1 rfl

/-- Automatic retirement, restoration and arbitrary chains of fully excluded
phases preserve exact rank-scoped evidence for the next visible phase. -/
theorem settle_exclusionRecord (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : ExclusionRecord
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    (settle phases generation entry current retired).ExclusionRecord := by
  induction phases generalizing generation entry current retired with
  | nil => exact valid
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := valid.frontier
      have record := valid.installed phase (by simp only [List.head?_cons, Option.mem_some_iff])
      have drained := record.phase_drain phase
      have drainedWithin := phase.drain_within current within
      have restoredReceipts : (restore entry (phase.drain current)).native.ReceiptsComplete := by
        intro event candidate installed
        exact valid.saved event candidate installed
      have restoredRecord := SuffixExclusionRecord.of_prefix restoredReceipts saved rfl
      have rebuilt := restoredRecord.phase_drain phase
      have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
          phase.low phase.high := saved.within phase.nonempty.le
      have rebuiltWithin := phase.drain_within (restore entry (phase.drain current)) restoredWithin
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          split
          · refine ⟨⟨adjacent, last, saved, rebuiltWithin⟩, restoredReceipts, rebuilt.receipts, ?_⟩
            intro target member
            have same : target = phase := by
              symm
              simpa only [List.head?_cons, Option.mem_some_iff] using member
            exact same ▸ rebuilt
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner member
              by_contra outside
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨member, outside⟩⟩
            have completed := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin completed)
            exact ih _ _ _ _ (fresh_exclusionRecord _ _ _ _
              ⟨next.adjacent, next.last, next.positioned⟩ rebuilt.receipts)
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ (fresh_exclusionRecord _ _ _ _
            ⟨next.adjacent, next.last, next.positioned⟩ drained.receipts)
      · refine ⟨⟨adjacent, last, saved, drainedWithin⟩, valid.saved, drained.receipts, ?_⟩
        intro target member
        have same : target = phase := by
          symm
          simpa only [List.head?_cons, Option.mem_some_iff] using member
        exact same ▸ drained

/-- The real native initial configuration supplies the entire exclusion record. -/
theorem initial_exclusionRecord (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).ExclusionRecord := by
  apply settle_exclusionRecord
  have rawFrontier : Frontier (⟨plan.phases, 0, ⟨State.initial inputs, ∅⟩,
      ⟨State.initial inputs, ∅⟩, []⟩ : PhaseRuntimeState graph) := by
    refine ⟨plan.adjacent, plan.last, ?_⟩
    cases phases : plan.phases with
    | nil =>
        have noEvents := plan.empty phases
        constructor
        · omega
        · intro event
          exact Fin.elim0 (noEvents ▸ event)
    | cons phase remaining =>
        have low := plan.first phase (by simp only [phases, List.head?_cons, Option.mem_some_iff])
        have atLow : (State.initial inputs).config.cut.IsPrefix phase.low := by
          constructor
          · omega
          · intro event
            simp only [State.initial, Config.initial, EventOrder.Cut.empty, Finset.notMem_empty,
              low, Nat.not_lt_zero]
        exact ⟨atLow, atLow.within phase.nonempty.le⟩
  exact fresh_exclusionRecord _ _ _ _ rawFrontier (State.ReceiptsComplete.initial inputs)

theorem raw_handle_frontier (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.Frontier)
    (message : Message Player (Payload graph)) (native : State graph)
    (authorized : state.allows message.payload = true)
    (accepted : EventGraphRuntime.handle runtime state.current.native message = some native) :
    Frontier { state with current := state.current.inclusionResult message.payload native } := by
  obtain ⟨phase, member, event, named, inside⟩ := allows_event state _ authorized
  obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
    handle_config_mem_step runtime state.current.native native message accepted
  have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
  subst actual
  cases phases : state.phases with
  | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
  | cons current remaining =>
      simp only [phases, List.head?_cons, Option.mem_some_iff] at member
      subst current
      refine ⟨?_, ?_, ?_⟩
      · simpa only [phases] using valid.adjacent
      · simpa only [phases] using valid.last
      have positioned := valid.positioned
      rw [phases] at positioned
      exact ⟨positioned.1, native_step_within phase _ _ positioned.2 event inside
        ready action supported⟩

theorem raw_environment_frontier (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.Frontier)
    (command : EnvironmentCommand graph) (native : State graph)
    (allowed : state.commandAllowed command = true)
    (supported : native ∈ (environmentStep runtime state.current.native command).support) :
    Frontier { state with current := state.current.environmentResult command native } := by
  rcases command_effect runtime state command native allowed supported with same |
    ⟨phase, member, event, inside, ready, action, reached⟩
  · exact valid.copy_current _ same
  · cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current remaining =>
        simp only [phases, List.head?_cons, Option.mem_some_iff] at member
        subst current
        refine ⟨?_, ?_, ?_⟩
        · simpa only [phases] using valid.adjacent
        · simpa only [phases] using valid.last
        have positioned := valid.positioned
        rw [phases] at positioned
        exact ⟨positioned.1, native_step_within phase _ _ positioned.2 event inside
          ready action reached⟩

end PhaseRuntimeState

/-- Primitive application operations preserve the actual exclusion record. -/
theorem phaseApplication_exclusionRecord (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.ExclusionRecord where
  submit state who material valid := by
    have same := (submitStep_publicView (material.call.register state.current.native who) who
      material.call.packet).trans (material.call.register_facts who state.current.native).2
    have configEq : (state.current.submit who material).native.config =
        state.current.native.config :=
      by rw [RecoveryState.submit, submitStep_config, (material.call.register_facts who _).1]
    refine ⟨PhaseRuntimeState.submit_frontier state who material valid.frontier, valid.saved,
      valid.active.step (Or.inl ⟨configEq, congrArg PublicView.accepted same,
        congrArg PublicView.activatedAt same⟩), ?_⟩
    intro phase member
    exact (valid.installed phase member).submit who material
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      apply PhaseRuntimeState.settle_exclusionRecord
      refine ⟨PhaseRuntimeState.raw_handle_frontier runtime state valid.frontier _ native authorized
        handled, valid.saved,
        valid.active.step (completionStep_handle runtime _ native _ handled), ?_⟩
      intro phase member
      exact (valid.installed phase member).inclusionResult runtime _ native handled
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_exclusionRecord
      refine ⟨PhaseRuntimeState.raw_environment_frontier runtime state valid.frontier command native
        allowed supported, valid.saved,
        valid.active.step (completionStep_environmentStep runtime _ native command supported), ?_⟩
      intro phase member
      exact (valid.installed phase member).environmentResult runtime command native supported
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every actual physical history, including every archived retry, has exact
public omission provenance relative to its current saved phase. -/
theorem phaseExclusionRecord_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.ExclusionRecord :=
  (phaseApplication_exclusionRecord runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_exclusionRecord plan draw) trace

end Vegas.EventGraphRuntime
