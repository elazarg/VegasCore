/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionServiceProgress
import Interaction.ReactiveRecallInvariant

/-! # Remembered submissions before a physical clock cut -/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => recoveryApplication runtime leaks

/-- A response remembered with an earlier clock was already present before the
cut. This holds after exclusion as well as along honest execution. -/
theorem old_response_mem_before (inputs : graph.Inputs) (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (before after : (app).Execution)
    (valid : before.application.native.Invariant inputs)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (owner : Player) (entry : (app).PlayerEntry) (recorded : entry ∈ after.recall owner)
    (old : entry.beforeView.application.1.publicView.clock <
      before.application.native.clock) : entry ∈ before.recall owner := by
  let predicate := fun execution : (app).Execution =>
    execution.application.native.Invariant inputs ∧
      before.application.native.clock ≤ execution.application.native.clock ∧
      ∀ who remembered, remembered ∈ execution.recall who →
        remembered ∈ before.recall who ∨ before.application.native.clock ≤
          remembered.beforeView.application.1.publicView.clock
  have invariant : (app).PolicyInvariant players predicate := {
    respond := by
      intro execution actor action prior _
      have progress := respond_progress runtime leaks inputs execution actor action prior.1
      have monotone : execution.application.native.clock ≤
          (execution.respond app actor action).application.native.clock := by
        rw [progress.clock]
        omega
      refine ⟨progress.invariant, prior.2.1.trans monotone, ?_⟩
      intro who remembered member
      rcases (app).respond_entry_origin execution actor who action remembered member with
        earlier | fresh
      · exact prior.2.2 who remembered earlier
      · right
        rw [fresh.2]
        exact prior.2.1
    environment := by
      intro execution next command prior moved
      have progress := environmentStep_progress runtime leaks inputs execution next command
        prior.1 moved
      have monotone : execution.application.native.clock ≤ next.application.native.clock := by
        rw [progress.clock]
        omega
      refine ⟨progress.invariant, prior.2.1.trans monotone, ?_⟩
      intro who remembered member
      rw [(app).environmentStep_recall execution next command moved] at member
      exact prior.2.2 who remembered member }
  have cut := invariant.runRounds scheduler count before after
    ⟨valid, le_rfl, fun _ _ member => Or.inl member⟩ reached
  exact (cut.2.2 owner entry recorded).resolve_right (Nat.not_le_of_lt old)

end Vegas.EventGraphRuntime.Recovery
