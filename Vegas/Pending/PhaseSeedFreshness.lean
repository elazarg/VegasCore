/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNamespace
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveResponseAccounting

/-! # Fresh attempt namespaces are absent from actual earlier scheduler recall

The application namespace order transports through the existing service-history
invariant. At an actual namespace change every previously recorded command
belongs to an older namespace, including the command that triggered rollback.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

namespace PhaseSeedFreshness

structure NamespacePast (execution : (app).Execution) : Prop where
  ordered : execution.application.Ordered
  earlier : ∀ entry ∈ execution.environmentRecall,
    entry.beforeView.application.attempt.generation ≤ execution.application.attempt.generation ∧
      entry.beforeView.application.attempt.phase ≤ execution.application.attempt.phase

theorem initial_namespacePast (state : PhaseRuntimeState graph) (ordered : state.Ordered) :
    NamespacePast runtime leaks (ReactiveApplication.Execution.initial app state) :=
  ⟨ordered, by intro entry impossible; cases impossible⟩

/-- Genuine response, inclusion, expiry, sample, clock and automatic retry
steps all preserve the bound on past public namespace observations. -/
theorem namespacePast_invariant (scheduler : (app).Scheduler) :
    (app).ServiceInvariant scheduler (NamespacePast runtime leaks) where
  respond execution who action valid := by
    have ordered := (phaseApplication_seedOrder runtime leaks).respond execution who action
      valid.ordered
    have progress := (phaseApplication_namespace_progress runtime leaks).respond execution who
      action valid.ordered
    refine ⟨ordered, ?_⟩
    intro entry member
    rw [(app).respond_environmentRecall] at member
    have previous := valid.earlier entry member
    exact ⟨previous.1.trans progress.1, previous.2.trans progress.2⟩
  environment execution next command valid _chosen reached := by
    have ordered := (phaseApplication_seedOrder runtime leaks).environmentStep execution next
      command valid.ordered reached
    have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep execution
      next command reached valid.ordered
    refine ⟨ordered, ?_⟩
    intro entry member
    rw [(app).environmentStep_environmentRecall execution next command reached,
      List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · have prior := valid.earlier entry previous
      exact ⟨prior.1.trans progress.1, prior.2.trans progress.2⟩
    · exact progress

/-- The namespace provenance covers all initialized legal histories and all
player deviations, with no scheduler-specific service premise. -/
theorem namespacePast_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) : NamespacePast runtime leaks control.execution := by
  exact (namespacePast_invariant runtime leaks scheduler).history _ horizon (by
    intro state supported
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact initial_namespacePast runtime leaks _
      (PhaseRuntimeState.initial_ordered plan input)) trace

/-- A real namespace change is strictly later in at least one component. -/
theorem changed_namespace_strict (execution next : (app).Execution) (command : (app).Command)
    (ordered : execution.application.Ordered)
    (reached : next ∈ (execution.environmentStep app command).support)
    (different : execution.application.attempt ≠ next.application.attempt) :
    execution.application.attempt.generation < next.application.attempt.generation ∨
      execution.application.attempt.phase < next.application.attempt.phase := by
  have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep execution
    next command reached ordered
  by_cases generations : execution.application.attempt.generation =
      next.application.attempt.generation
  · right
    have phases : execution.application.attempt.phase ≠ next.application.attempt.phase := by
      intro same
      apply different
      cases first : execution.application.attempt
      cases second : next.application.attempt
      simp only [first, second] at generations same
      simp only [CommitAttemptId.mk.injEq]
      exact ⟨same, generations⟩
    omega
  · left
    omega

/-- The newly installed namespace cannot occur at any earlier actual command,
including the failure command whose native effect installed that namespace. -/
theorem fresh_after_environment (execution next : (app).Execution) (command : (app).Command)
    (valid : NamespacePast runtime leaks execution)
    (reached : next ∈ (execution.environmentStep app command).support)
    (different : execution.application.attempt ≠ next.application.attempt) :
    ∀ entry ∈ next.environmentRecall,
      next.application.attempt ≠ entry.beforeView.application.attempt := by
  have strict := changed_namespace_strict runtime leaks execution next command valid.ordered
    reached different
  intro entry member same
  rw [(app).environmentStep_environmentRecall execution next command reached,
    List.mem_append, List.mem_singleton] at member
  have previous : entry.beforeView.application.attempt.generation ≤
        execution.application.attempt.generation ∧
      entry.beforeView.application.attempt.phase ≤ execution.application.attempt.phase := by
    rcases member with old | rfl
    · exact valid.earlier entry old
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have generation := congrArg CommitAttemptId.generation same
  have phase := congrArg CommitAttemptId.phase same
  rcases strict with strict | strict <;> omega

end PhaseSeedFreshness
end Vegas.EventGraphRuntime
