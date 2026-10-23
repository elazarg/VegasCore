/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochWorkMonotone
import Vegas.Pending.PhaseTimelyResolution

/-! # Live requests persist while semantic work is unchanged -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
theorem namespace_eq_of_flat (before after : PhaseRuntimeState graph)
    (progress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (budget : after.SeedBudget) (flat : workRemaining after = workRemaining before) :
    before.attempt = after.attempt := by
  by_contra different
  have strict := work_decreases_of_namespace before after progress.2 progress.1
    (PhaseRuntimeState.phaseLow_le_count after.phases) budget.generation_le_card different
  omega

include leaks in
theorem work_decreases_of_resolved_handle {inputs : graph.Inputs}
    (before after : PhaseRuntimeState graph) (valid : WorkValid inputs before)
    (message : Message Player (CommitAttemptPacket graph))
    (handled : before.handle runtime message = some after)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.SeedRequest owner coordinate)
    (resolved : before.attempt ≠ after.attempt ∨
      coordinate.event ∈ after.current.native.config.cut.completed) :
    workRemaining after < workRemaining before := by
  have progress := (phaseApplication_namespace_progress runtime leaks).handle
    before message after handled valid.2.1
  have budget := (phaseApplication_seedBudget runtime leaks).handle
    before message after valid.2.2 handled
  by_cases same : before.attempt = after.attempt
  · have native := before.handle_progress_of_same_namespace runtime after message
      valid.1 valid.2.1 handled same
    exact work_decreases_of_completion before after same native.completed coordinate.event
      request.2.2.1.1 (resolved.resolve_left (not_not_intro same))
  · exact work_decreases_of_namespace before after progress.2 progress.1
      (PhaseRuntimeState.phaseLow_le_count after.phases) budget.generation_le_card same

/-- Flat semantic work rules out both physical completion and namespace retirement.
This fact covers every raw response, not merely count-permitted packets. -/
theorem flat_request_relation (ordered : graph.RevealRelaxedOrdered) :
    (app).StepRelation (fun before after => ∀ inputs, WorkValid inputs before →
      ∀ owner coordinate, before.SeedRequest owner coordinate →
        workRemaining after = workRemaining before → after.SeedRequest owner coordinate) where
  refl _ _ _ _ _ request _ := request
  submit _ actor material _ _ _ _ request _ := request.submit actor material
  handle before message after handled inputs valid owner coordinate request flat := by
    rcases PhaseRuntimeState.handle_request_or_own_completion runtime ordered before after valid.1
      message handled owner coordinate request with retained |
      ⟨native, ready, action, _sender, _addressed, _accepted, stepped, normalized⟩
    · exact retained
    · have completed : coordinate.event ∈ native.config.cut.completed := by
        rw [before.current.native.config.step_cut coordinate.event ready action
          native.config stepped]
        simp
      have resolved := PhaseRuntimeState.settle_resolves before.phases before.generation
        before.entry (before.current.inclusionResult message.payload.packet.call native)
        before.retired valid.2.1 coordinate.event completed
      let intermediate : PhaseRuntimeState graph :=
        {before with current := before.current.inclusionResult message.payload.packet.call native}
      change before.attempt ≠ intermediate.normalize.attempt ∨
        coordinate.event ∈ intermediate.normalize.current.native.config.cut.completed at resolved
      change after = intermediate.normalize at normalized
      rw [← normalized] at resolved
      have strict := work_decreases_of_resolved_handle runtime leaks before after valid message
        handled owner coordinate request resolved
      omega
  environment before command after moved inputs valid owner coordinate request flat := by
    rcases PhaseRuntimeState.environment_request_or_expiry runtime ordered before after command
      moved owner coordinate request with retained | expiry
    · exact retained
    · subst command
      by_cases due : runtime.deadline coordinate.event ≤ before.current.native.clock -
          (before.current.native.activatedAt coordinate.event).getD before.current.native.clock
      · have strict := expiry_work_decreases runtime leaks before after valid.1 valid.2.1
          valid.2.2 owner coordinate request due moved
        omega
      · have activatedSome := (valid.1.active.activated_iff coordinate.event).mpr
          ⟨request.2.2.1, by simp only [request.2.2.2.1, Option.isSome_some]⟩
        have timely : before.current.native.WithinDeadline runtime coordinate.event := by
          cases activated : before.current.native.activatedAt coordinate.event with
          | none => simp only [activated, Option.isSome_none, Bool.false_eq_true] at activatedSome
          | some entered =>
              simpa only [State.WithinDeadline, activated, Option.getD_some] using
                Nat.lt_of_not_ge due
        exact PhaseRuntimeState.expiry_request_before_deadline runtime before after owner coordinate
          request timely moved

end Vegas.EventGraphRuntime.ReservedEpoch
