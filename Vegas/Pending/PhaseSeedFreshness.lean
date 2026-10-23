/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseNamespace

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

end PhaseSeedFreshness
end Vegas.EventGraphRuntime
