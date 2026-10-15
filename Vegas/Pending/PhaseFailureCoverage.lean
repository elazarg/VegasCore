/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseExclusionRecord

/-! # Every surviving public failure has permanently excluded its owner

Rollback may remove the public witness of an old exclusion. The converse
survives: a failure still present in either semantic checkpoint has an owner
already in permanent exclusion. This is derived from actual command effects.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

/-- Present public failures are covered by permanent exclusion. -/
structure FailureCoverage (state : RecoveryState graph) : Prop where
  receipts : state.native.ReceiptsComplete
  covered : ∀ event owner, graph.actor? event = some owner →
    state.native.PublicFailure event → owner ∈ state.excluded

namespace FailureCoverage

variable {state : RecoveryState graph}

omit [DecidableEq Player] in
private theorem suffixRecord (valid : state.FailureCoverage) :
    SuffixExclusionRecord 0 state.excluded state := by
  refine ⟨valid.receipts, fun _ impossible => (Nat.not_lt_zero _ impossible).elim,
    fun owner => ⟨Or.inl, ?_⟩⟩
  rintro (member | ⟨event, lower, acting, failed⟩)
  · exact member
  · exact valid.covered event owner acting failed

omit [DecidableEq Player] in
private theorem of_suffix {inherited : Finset Player} {after : RecoveryState graph}
    (valid : SuffixExclusionRecord 0 inherited after) : after.FailureCoverage :=
  ⟨valid.receipts, fun event owner acting failed =>
    (valid.excluded owner).mpr (Or.inr ⟨event, Nat.zero_le _, acting, failed⟩)⟩

theorem initial (inputs : graph.Inputs) :
    (⟨State.initial inputs, ∅⟩ : RecoveryState graph).FailureCoverage := by
  have valid := PublicExclusionRecord.initial inputs
  exact ⟨valid.receipts, fun event owner acting failed =>
    (valid.excluded owner).mpr ⟨event, acting, failed⟩⟩

omit [DecidableEq Player] in
theorem completeAutomatic (valid : state.FailureCoverage) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).FailureCoverage :=
  of_suffix (valid.suffixRecord.completeAutomatic event eligible)

theorem drain (valid : state.FailureCoverage) (phase : RuntimePhase graph) :
    (phase.drain state).FailureCoverage := of_suffix (valid.suffixRecord.phase_drain phase)

theorem inclusionResult (valid : state.FailureCoverage) (runtime : EventGraphRuntime graph)
    (message : Message Player (Payload graph)) (native : State graph)
    (accepted : EventGraphRuntime.handle runtime state.native message = some native) :
    (state.inclusionResult message.payload native).FailureCoverage :=
  of_suffix (valid.suffixRecord.inclusionResult runtime message native accepted)

theorem environmentResult (valid : state.FailureCoverage) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    (state.environmentResult command native).FailureCoverage :=
  of_suffix (valid.suffixRecord.environmentResult runtime command native reached)

theorem submit (valid : state.FailureCoverage) (who : Player)
    (material : WitnessedSubmission graph) : (state.submit who material).FailureCoverage :=
  of_suffix (valid.suffixRecord.submit who material)

end FailureCoverage

end RecoveryState

namespace PhaseRuntimeState

/-- Saved and live public failures remain covered, and the saved permanent set
is contained in the current physical permanent set. -/
structure FailureCoverage (state : PhaseRuntimeState graph) : Prop where
  saved : state.entry.FailureCoverage
  active : state.current.FailureCoverage
  inherited : state.entry.excluded ⊆ state.current.excluded

omit [DecidableEq Player] in
theorem restore_failureCoverage (entry current : RecoveryState graph)
    (saved : entry.FailureCoverage) (inherited : entry.excluded ⊆ current.excluded) :
    (restore entry current).FailureCoverage := by
  refine ⟨fun event candidate installed => saved.receipts event candidate installed, ?_⟩
  intro event owner acting failed
  apply inherited
  apply saved.covered event owner acting
  exact (State.PublicFailure.congr event Iff.rfl rfl rfl).mp failed

/-- Every normalization branch either retains live coverage or restores a
covered checkpoint under the larger permanent exclusion set. -/
theorem settle_failureCoverage (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (saved : entry.FailureCoverage) (active : current.FailureCoverage)
    (inherited : entry.excluded ⊆ current.excluded) :
    (settle phases generation entry current retired).FailureCoverage := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active, inherited⟩
  | cons phase remaining ih =>
      have drained := active.drain phase
      have inheritedDrained : entry.excluded ⊆ (phase.drain current).excluded := by
        rw [phase.drain_excluded]
        exact inherited
      have restored := restore_failureCoverage entry (phase.drain current) saved inheritedDrained
      have rebuilt := restored.drain phase
      simp only [settle]
      split
      · split
        · split
          · refine ⟨restored, rebuilt, ?_⟩
            rw [phase.drain_excluded]
          · exact ih _ _ _ _ rebuilt rebuilt (Finset.Subset.refl _)
        · exact ih _ _ _ _ drained drained (Finset.Subset.refl _)
      · exact ⟨saved, drained, inheritedDrained⟩

theorem initial_failureCoverage (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).FailureCoverage :=
  settle_failureCoverage _ _ _ _ _ (RecoveryState.FailureCoverage.initial inputs)
    (RecoveryState.FailureCoverage.initial inputs) (Finset.Subset.refl _)

end PhaseRuntimeState

/-- Actual physical commands preserve coverage of every surviving public
failure, including failures in a saved prefix before the current phase. -/
theorem phaseApplication_failureCoverage (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.FailureCoverage where
  submit state who material valid :=
    ⟨valid.saved, valid.active.submit who material, valid.inherited⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_failureCoverage _ _ _ _ _ valid.saved
        (valid.active.inclusionResult runtime _ native handled)
        (valid.inherited.trans (state.current.inclusionResult_excluded_subset _ _))
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      exact PhaseRuntimeState.settle_failureCoverage _ _ _ _ _ valid.saved
        (valid.active.environmentResult runtime command native supported)
        (valid.inherited.trans (state.current.environmentResult_excluded_subset _ _))
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- No active owner can have any surviving completed binding without an
accepted handle, including a binding in an earlier saved source phase. -/
theorem phaseFailureCoverage_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.FailureCoverage :=
  (phaseApplication_failureCoverage runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_failureCoverage plan draw) trace

end Vegas.EventGraphRuntime
