/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication

/-! # Actual remaining descriptors are a suffix of the installed phase plan -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every application operation preserves the original descriptor suffix,
including retries, exhausted blocks and chains of automatic completions. -/
theorem phaseApplication_planSuffix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) :
    (phaseApplication runtime leaks).Invariant (fun state => state.phases <:+ plan.phases) where
  submit _ _ _ valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact (PhaseRuntimeState.settle_suffix _ _ _ _ _).trans valid
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, _supported, rfl⟩ := reached
      exact (PhaseRuntimeState.settle_suffix _ _ _ _ _).trans valid
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every initialized legal history retains only an actual suffix of the
original plan, for arbitrary schedulers and unrestricted player responses. -/
theorem phasePlanSuffix_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.phases <:+ plan.phases :=
  (phaseApplication_planSuffix runtime leaks plan).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.settle_suffix _ _ _ _ _) trace

omit [DecidableEq Player] in
/-- A suffix inherits adjacency, the final graph boundary and maximal adjacent
kinds from the original plan. No execution or source correspondence is assumed. -/
theorem RuntimePhasePlan.suffix_geometry (plan : RuntimePhasePlan graph)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (remaining : List (RuntimePhase graph)) (suffix : remaining <:+ plan.phases) :
    (remaining.IsChain fun before after => before.high = after.low) ∧
      (∀ final ∈ remaining.getLast?, final.high = graph.order.eventCount) ∧
      (remaining.IsChain fun before after =>
        before.kind ≠ after.kind ∨ before.kind = .sample) := by
  refine ⟨plan.adjacent.suffix suffix, ?_, maximal.suffix suffix⟩
  intro final member
  have nonempty : remaining ≠ [] := by
    rintro rfl
    cases member
  obtain ⟨prior, append⟩ := suffix
  apply plan.last final
  rw [← append, List.getLast?_append_of_ne_nil prior nonempty]
  exact member

/-- Actual current phases retain all structural hypotheses needed by the
compiler's maximal-block identification at every initialized history. -/
theorem phasePlanGeometry_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    (control.execution.application.phases.IsChain fun before after => before.high = after.low) ∧
      (∀ final ∈ control.execution.application.phases.getLast?,
        final.high = graph.order.eventCount) ∧
      (control.execution.application.phases.IsChain fun before after =>
        before.kind ≠ after.kind ∨ before.kind = .sample) :=
  plan.suffix_geometry maximal _
    (phasePlanSuffix_history runtime leaks plan inputs horizon scheduler trace)

end Vegas.EventGraphRuntime
