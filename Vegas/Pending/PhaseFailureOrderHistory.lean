/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFailureOrder

/-! # Actual recovery histories respect source-ordered publication failure -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

structure PublicFailureOrder (state : PhaseRuntimeState graph) : Prop where
  frontier : state.Frontier
  coverage : state.FailureCoverage
  publicationOrder : ∀ phase ∈ state.phases.head?,
    state.current.OrderedPublicFailures phase.low state.entry.excluded

omit [DecidableEq Player] in
theorem fresh_publicFailureOrder (phases : List (RuntimePhase graph)) (generation : Nat)
    (current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : Frontier
      (⟨phases, generation, current, current, retired⟩ : PhaseRuntimeState graph))
    (coverage : current.FailureCoverage) :
    PublicFailureOrder
      (⟨phases, generation, current, current, retired⟩ : PhaseRuntimeState graph) := by
  refine ⟨frontier, ⟨coverage, coverage, Finset.Subset.refl _⟩, ?_⟩
  intro phase member
  cases phases with
  | nil => cases member
  | cons current remaining =>
      have same : phase = current :=
        (by simpa only [List.head?_cons, Option.mem_some_iff] using member : current = phase).symm
      subst phase
      exact RecoveryState.orderedPublicFailures_of_prefix current.low _ _ frontier.positioned.1

theorem settle_publicFailureOrder (ordered : graph.RevealRelaxedOrdered)
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (valid : PublicFailureOrder
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    (settle phases generation entry current retired).PublicFailureOrder := by
  induction phases generalizing generation entry current retired with
  | nil => exact valid
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := valid.frontier
      have coverage := valid.coverage
      have sourceOrder := valid.publicationOrder phase
        (by simp only [List.head?_cons, Option.mem_some_iff])
      have drainedOrder := phase.orderedPublicFailures_drain phase.low entry.excluded current
        sourceOrder coverage.active coverage.inherited ordered
      have drainedCoverage := coverage.active.drain phase
      have drainedWithin := phase.drain_within current within
      have inheritedDrained : entry.excluded ⊆ (phase.drain current).excluded := by
        rw [phase.drain_excluded]
        exact coverage.inherited
      have restoredCoverage := restore_failureCoverage entry (phase.drain current)
        coverage.saved inheritedDrained
      have rebuiltCoverage := restoredCoverage.drain phase
      have restoredPrefix : (restore entry (phase.drain current)).native.config.cut.IsPrefix
          phase.low := saved
      have restoredOrder := RecoveryState.orderedPublicFailures_of_prefix phase.low
        (phase.drain current).excluded (restore entry (phase.drain current)) restoredPrefix
      have rebuiltOrder := phase.orderedPublicFailures_drain phase.low
        (phase.drain current).excluded _ restoredOrder restoredCoverage
        (Finset.Subset.refl _) ordered
      have restoredWithin := restoredPrefix.within phase.nonempty.le
      have rebuiltWithin := phase.drain_within _ restoredWithin
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          split
          · refine ⟨⟨adjacent, last, saved, rebuiltWithin⟩,
              ⟨restoredCoverage, rebuiltCoverage, ?_⟩, ?_⟩
            · rw [phase.drain_excluded]
            · intro target member
              have same : target = phase :=
                (by simpa only [List.head?_cons, Option.mem_some_iff] using member :
                  phase = target).symm
              exact same ▸ rebuiltOrder
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner member
              by_contra outside
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨member, outside⟩⟩
            have completed := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin completed)
            exact ih _ _ _ _ (fresh_publicFailureOrder _ _ _ _
              ⟨next.adjacent, next.last, next.positioned⟩ rebuiltCoverage)
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ (fresh_publicFailureOrder _ _ _ _
            ⟨next.adjacent, next.last, next.positioned⟩ drainedCoverage)
      · refine ⟨⟨adjacent, last, saved, drainedWithin⟩,
          ⟨coverage.saved, drainedCoverage, inheritedDrained⟩, ?_⟩
        intro target member
        have same : target = phase :=
          (by simpa only [List.head?_cons, Option.mem_some_iff] using member :
            phase = target).symm
        exact same ▸ drainedOrder

theorem initial_publicFailureOrder (ordered : graph.RevealRelaxedOrdered)
    (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).PublicFailureOrder :=
  settle_publicFailureOrder ordered _ _ _ _ _
    (fresh_publicFailureOrder _ _ _ _ (initial_checkpoint_frontier plan inputs)
      (RecoveryState.FailureCoverage.initial inputs))

end PhaseRuntimeState

theorem phaseApplication_publicFailureOrder (ordered : graph.RevealRelaxedOrdered)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.PublicFailureOrder where
  submit state who material valid := by
    have same := (submitStep_publicView (material.call.register state.current.native who) who
      material.call.packet).trans (material.call.register_facts who state.current.native).2
    have config : (state.current.submit who material).native.config =
        state.current.native.config := by
      rw [RecoveryState.submit, submitStep_config, (material.call.register_facts who _).1]
    exact ⟨state.submit_frontier who material valid.frontier,
      ⟨valid.coverage.saved, valid.coverage.active.submit who material, valid.coverage.inherited⟩,
      fun phase member => (valid.publicationOrder phase member).copy config
        (congrArg PublicView.accepted same)⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      have permitted : state.current.excludedCall message.payload.packet.call = false := by
        cases flag : state.current.excludedCall message.payload.packet.call with
        | false => rfl
        | true =>
            have negative := (Bool.and_eq_true_iff.mp allowed).2
            rw [flag] at negative
            cases negative
      apply PhaseRuntimeState.settle_publicFailureOrder ordered
      exact ⟨state.raw_handle_frontier runtime valid.frontier _ native authorized handled,
        ⟨valid.coverage.saved, valid.coverage.active.inclusionResult runtime _ native handled,
          valid.coverage.inherited.trans (state.current.inclusionResult_excluded_subset _ _)⟩,
        fun phase member => (valid.publicationOrder phase member).inclusionResult
          valid.coverage.active valid.coverage.inherited ordered runtime _ native permitted handled⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      apply PhaseRuntimeState.settle_publicFailureOrder ordered
      exact ⟨state.raw_environment_frontier runtime valid.frontier command native allowed supported,
        ⟨valid.coverage.saved, valid.coverage.active.environmentResult runtime command native
          supported, valid.coverage.inherited.trans
            (state.current.environmentResult_excluded_subset _ _)⟩,
        fun phase member => (valid.publicationOrder phase member).environmentResult
          valid.coverage.active valid.coverage.inherited ordered runtime command native supported⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

theorem phasePublicFailureOrder_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.PublicFailureOrder :=
  (phaseApplication_publicFailureOrder ordered runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_publicFailureOrder ordered plan draw) trace

/-- The raw accepted result retains source-ordered suppression before the
dispatcher retires the finished phase and installs another checkpoint. -/
theorem phase_inclusion_failureOrder_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (head : control.execution.application.phases.head? = some phase)
    (message : Message Player (Payload graph)) (native : State graph)
    (permitted : control.execution.application.current.excludedCall message.payload = false)
    (handled : EventGraphRuntime.handle runtime control.execution.application.current.native
      message = some native) :
    RecoveryState.OrderedPublicFailures phase.low control.execution.application.entry.excluded
      (phase.drain
        (control.execution.application.current.inclusionResult message.payload native)) := by
  have valid := phasePublicFailureOrder_history runtime leaks ordered plan inputs horizon scheduler
    trace
  have covered := valid.coverage.active.inclusionResult runtime message native handled
  have inherited := valid.coverage.inherited.trans
    (control.execution.application.current.inclusionResult_excluded_subset message.payload native)
  exact phase.orderedPublicFailures_drain _ _ _
    ((valid.publicationOrder phase head).inclusionResult valid.coverage.active
      valid.coverage.inherited ordered runtime message native permitted handled)
    covered inherited ordered

/-- An actual environment result has the same source-order law before the
automatic dispatcher normalizes its completed phase. -/
theorem phase_environment_failureOrder_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (head : control.execution.application.phases.head? = some phase)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime control.execution.application.current.native
      command).support) :
    RecoveryState.OrderedPublicFailures phase.low control.execution.application.entry.excluded
      (phase.drain (control.execution.application.current.environmentResult command native)) := by
  have valid := phasePublicFailureOrder_history runtime leaks ordered plan inputs horizon scheduler
    trace
  have covered := valid.coverage.active.environmentResult runtime command native reached
  have inherited := valid.coverage.inherited.trans
    (control.execution.application.current.environmentResult_excluded_subset command native)
  exact phase.orderedPublicFailures_drain _ _ _
    ((valid.publicationOrder phase head).environmentResult valid.coverage.active
      valid.coverage.inherited ordered runtime command native reached)
    covered inherited ordered

end Vegas.EventGraphRuntime
