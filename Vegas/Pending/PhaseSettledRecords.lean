/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFrontier
import Vegas.Pending.ReactiveSettledVerdict

/-! # Settled physical outcomes retained across semantic rollback

Each retired record is the genuine completed result of a binding phase. Its
public projection remains paired with the permanent physical receipts; no
rollback or phase advance can erase those accepting or rejecting receipts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Every retired namespace identifies the completed binding interval it voided. -/
def ArchivesSettled (state : PhaseRuntimeState graph) : Prop :=
  ∀ record ∈ state.retired, ∃ phase : RuntimePhase graph,
    phase.kind = .commitment ∧ phase.low = record.attempt.phase ∧
      phase.events ⊆ record.state.config.cut.completed

/-- A retired physical snapshot has the original settled public record carrier.
The receipt list is supplied by the same permanent reactive execution. -/
def archivedRecord (record : RetiredCommitAttempt graph)
    (receipts : List (MessageId Player × Bool)) : SettledRecord graph :=
  ⟨record.state.publicView, receipts⟩

omit [DecidableEq Player] in
/-- Every binding of the archived phase occurs in its actual settled completion order. -/
theorem archivedRecord_completed (record : RetiredCommitAttempt graph)
    (receipts : List (MessageId Player × Bool)) (phase : RuntimePhase graph)
    (finished : phase.events ⊆ record.state.config.cut.completed)
    (event : graph.EventId) (inside : event ∈ phase.events) :
    event ∈ (archivedRecord record receipts).view.observation.completionOrder :=
  (record.state.config.history_exact event).mpr (finished inside)

omit [DecidableEq Player] in
/-- Archived acceptance uses the unchanged global accepting-receipt evidence. -/
theorem archivedRecord_accepts (record : RetiredCommitAttempt graph)
    (receipts : List (MessageId Player × Bool)) (id : MessageId Player) :
    (archivedRecord record receipts).Accepts id ↔ (id, true) ∈ receipts := Iff.rfl

/-- Actual normalization adds an archive only under a completed binding-phase
guard, and retains every earlier settled outcome through recursive advancement. -/
theorem settle_archives (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (old : ArchivesSettled
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    ArchivesSettled (settle phases generation entry current retired) := by
  induction phases generalizing generation entry current retired with
  | nil => exact old
  | cons phase remaining ih =>
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          have archived : ∀ record ∈ retired ++
              [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
              ∃ saved : RuntimePhase graph, saved.kind = .commitment ∧
                saved.low = record.attempt.phase ∧
                  saved.events ⊆ record.state.config.cut.completed := by
            intro record member
            rcases List.mem_append.mp member with prior | new
            · exact old record prior
            · rw [List.mem_singleton.mp new]
              exact ⟨phase, failure.1, rfl, finished⟩
          split
          · exact archived
          · exact ih _ _ _ _ archived
        · exact ih _ _ _ _ old
      · exact old

/-- The actual initialized archive is empty, then gains only settled phase outcomes. -/
theorem initial_archives (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).ArchivesSettled := by
  apply settle_archives
  intro record impossible
  exact (List.not_mem_nil impossible).elim

end Vegas.EventGraphRuntime.PhaseRuntimeState

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- All retired physical results remain settled along actual raw executions,
independently of count cleanliness, value correctness, or scheduler behavior. -/
theorem phaseApplication_archives (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.ArchivesSettled where
  submit _ _ _ valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_archives _ _ _ _ _ valid
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      exact PhaseRuntimeState.settle_archives _ _ _ _ _ valid
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

end Vegas.EventGraphRuntime
