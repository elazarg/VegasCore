/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedScheduler
import Interaction.ReactiveServiceRounds

/-! # A phased source choice is sampled only at its first callback

Own recall records silence as well as packets. Repeated callbacks therefore
cannot redraw a sampled physical omission; a new attempt remains a new choice.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Own recall contains a response to this exact physical coordinate,
including a response that deliberately emitted nothing. -/
def ResponseRecorded (owner : Player) (coordinate : CommitAttemptEvent graph)
    (past : List (app).PlayerEntry) : Prop :=
  ∃ entry ∈ past, PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate

theorem ResponseRecorded.mono {owner : Player} {coordinate : CommitAttemptEvent graph}
    {past more : List (app).PlayerEntry} (recorded : ResponseRecorded runtime leaks owner
      coordinate past) (contains : past ⊆ more) : ResponseRecorded runtime leaks owner
      coordinate more := by
  obtain ⟨entry, member, request⟩ := recorded
  exact ⟨entry, contains member, request⟩

/-- Once recorded, a decision remains in own information under arbitrary
future player policies, environment commands, retirement and rollback. -/
theorem ResponseRecorded.runRounds {owner : Player} {coordinate : CommitAttemptEvent graph}
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (recorded : ResponseRecorded runtime leaks owner coordinate (execution.recall owner))
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    ResponseRecorded runtime leaks owner coordinate (next.recall owner) := by
  have invariant : (app).ServiceInvariant scheduler (fun state =>
      ResponseRecorded runtime leaks owner coordinate (state.recall owner)) := {
    respond := fun current who response valid => ResponseRecorded.mono runtime leaks valid
      ((app).respond_recall_mono current who owner response)
    environment := fun current future command valid _ moved => by
      rw [(app).environmentStep_recall current future command moved]
      exact valid }
  exact invariant.runRounds players count execution next recorded reached
end Vegas.EventGraphRuntime.PhaseCount
