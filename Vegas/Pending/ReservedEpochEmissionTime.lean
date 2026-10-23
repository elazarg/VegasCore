/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFrontier
import Interaction.ReactiveRecallInvariant
import Interaction.ReactivePolicyInvariant

/-! # Old response records precede a later physical clock cut -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def EmissionCut (origin : (app).Execution) (execution : (app).Execution) : Prop :=
  origin.application.current.native.clock ≤ execution.application.current.native.clock ∧
    ∀ owner entry, entry ∈ execution.recall owner → entry ∈ origin.recall owner ∨
      origin.application.current.native.clock ≤ entry.beforeView.application.1.publicView.clock

theorem emission_cut_invariant (players : Player → (app).Policy) (origin : (app).Execution) :
    (app).PolicyInvariant players (EmissionCut runtime leaks origin) where
  respond execution actor action cut _ := by
    have monotone := (phaseApplication_clock_monotone runtime leaks).respond execution actor action
    refine ⟨cut.1.trans monotone, ?_⟩
    intro owner entry member
    rcases (app).respond_entry_origin execution actor owner action entry member with old | fresh
    · exact cut.2 owner entry old
    · right
      rw [fresh.2]
      exact cut.1
  environment execution next command cut reached := by
    have monotone := (phaseApplication_clock_monotone runtime leaks).environmentStep
      execution next command reached
    refine ⟨cut.1.trans monotone, ?_⟩
    intro owner entry member
    rw [(app).environmentStep_recall execution next command reached] at member
    exact cut.2 owner entry member

theorem old_response_mem_before (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (before after : (app).Execution)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (owner : Player) (entry : (app).PlayerEntry) (recorded : entry ∈ after.recall owner)
    (old : entry.beforeView.application.1.publicView.clock <
      before.application.current.native.clock) :
    entry ∈ before.recall owner := by
  have cut := (emission_cut_invariant runtime leaks players before).runRounds scheduler count
    before after ⟨le_rfl, fun _ _ member => Or.inl member⟩ reached
  exact (cut.2 owner entry recorded).resolve_right (Nat.not_le_of_lt old)

end Vegas.EventGraphRuntime.ReservedEpoch
