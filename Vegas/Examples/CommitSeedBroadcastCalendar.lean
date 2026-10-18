/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalCalendar
import Interaction.ReactiveRecordedEnvironmentPrefix

/-! # The unique callback turn of an actual continuation namespace -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def tailTurn (owner : Player) : Nat := 2 * owner.val

theorem tail_activation_turn (seeds : Seeds) (current : app.Control)
    (_trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate)
    (selected : choose seeds current.execution.environmentRecall
      (current.execution.observeEnvironment app) = .activate owner) :
    tailIndex current.execution.environmentRecall (current.execution.observeEnvironment app) =
      tailTurn owner := by
  have notOriginal : current.execution.application.attempt ≠ originalAttempt := by
    rwa [← request.1]
  change (current.execution.observeEnvironment app).application.attempt ≠ originalAttempt
    at notOriginal
  unfold choose at selected
  rw [ite_eq_right notOriginal] at selected
  split at selected
  all_goals first
    | exact tail_activation _ _ _ _ _ selected
    | cases selected

private theorem first_namespace_index_le (past : List app.EnvironmentEntry)
    (index : Nat) (bounded : index < past.length) (attempt : CommitAttemptId)
    (same : past[index].beforeView.application.attempt = attempt) :
    past.findIdx (fun entry => entry.beforeView.application.attempt = attempt) ≤ index := by
  classical
  by_contra greater
  have earlier := List.not_of_lt_findIdx (p := fun entry : app.EnvironmentEntry =>
    entry.beforeView.application.attempt = attempt) (by omega :
      index < past.findIdx (fun entry => entry.beforeView.application.attempt = attempt))
  simp only [same, decide_true] at earlier
  cases earlier

private theorem recorded_tail_turn (menu : app.ResponseMenu) (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (index : Nat) (bounded : index < execution.environmentRecall.length)
    (callback : PhaseSeedScheduler.callback runtime leaks coordinate owner
      execution.environmentRecall[index]) :
    index = execution.environmentRecall.findIdx (fun entry =>
      entry.beforeView.application.attempt = coordinate.attempt) + tailTurn owner := by
  classical
  let entry := execution.environmentRecall[index]
  have recorded : execution.environmentRecall = execution.environmentRecall.take index ++
      entry :: execution.environmentRecall.drop (index + 1) := by
    rw [List.getElem_cons_drop bounded, List.take_append_drop]
  obtain ⟨used, before, _within, ⟨beforeTrace⟩, _supported, recalled, viewed⟩ :=
    menu.recorded_environment_prefix initial horizon (family seeds) remaining execution
      trace (execution.environmentRecall.take index) entry
        (execution.environmentRecall.drop (index + 1)) recorded
  have raw := menu.toRawTrace initial horizon (family seeds) beforeTrace
  have valid := raw_native_valid (family seeds) _ raw
  have publicRequest := callback.2
  change PhaseRuntimeState.requests entry.beforeView.application owner coordinate
    at publicRequest
  rw [viewed] at publicRequest
  change PhaseRuntimeState.requests before.application.publicView owner coordinate
    at publicRequest
  have request := (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mp publicRequest
  have commands := family_commands seeds _ (menu.toRawTrace initial horizon
    (family seeds) trace)
  rw [recorded] at commands
  have splitCommands := (app.commandConsistentFrom_append choose seeds []
    (execution.environmentRecall.take index)
      (entry :: execution.environmentRecall.drop (index + 1))).mp commands
  have selected : choose seeds before.environmentRecall
      (before.observeEnvironment app) = .activate owner := by
    have chosen := splitCommands.2.1
    have activated : entry.command = .activate owner := callback.1
    rw [activated] at chosen
    simpa only [List.nil_append, ← recalled, viewed] using chosen
  have turn := tail_activation_turn seeds _ raw coordinate owner retired request selected
  have same : entry.beforeView.application.attempt = coordinate.attempt := callback.2.1.symm
  have firstLe := first_namespace_index_le execution.environmentRecall index bounded
    coordinate.attempt same
  rw [tailIndex, recalled, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt bounded), List.findIdx_take] at turn
  have currentAttempt : (before.observeEnvironment app).application.attempt =
      coordinate.attempt := request.1.symm
  simp only [currentAttempt, Nat.min_eq_right firstLe] at turn
  omega

/-- A genuine continuation coordinate has only one owner callback in the
complete original physical history. The index is measured in actual environment
recall, so retirement, rollback and later foreign commands cannot add another. -/
theorem tail_callback_index_unique (menu : app.ResponseMenu)
    (silence : ∀ owner past view,
      (⟨none⟩ : app.Action) ∈ menu.actions owner past view) (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (first second : Nat)
    (firstBound : first < current.execution.environmentRecall.length)
    (secondBound : second < current.execution.environmentRecall.length)
    (firstCallback : PhaseSeedScheduler.callback runtime leaks coordinate owner
      current.execution.environmentRecall[first])
    (secondCallback : PhaseSeedScheduler.callback runtime leaks coordinate owner
      current.execution.environmentRecall[second]) : first = second := by
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none =>
      exact (recorded_tail_turn menu seeds remaining execution trace coordinate owner retired first
        firstBound firstCallback).trans
          (recorded_tail_turn menu seeds remaining execution trace coordinate owner retired second
            secondBound secondCallback).symm
  | some actor =>
      obtain ⟨responded⟩ := menu.trace_respond initial horizon (family seeds) remaining
        execution actor ⟨none⟩ trace (silence actor _ _)
      have firstTurn := recorded_tail_turn menu seeds remaining (execution.respond app actor ⟨none⟩)
        responded coordinate owner retired first
        (by simpa only [app.respond_environmentRecall] using firstBound)
        (by simpa only [app.respond_environmentRecall] using firstCallback)
      have secondTurn := recorded_tail_turn menu seeds remaining
        (execution.respond app actor ⟨none⟩)
        responded coordinate owner retired second
        (by simpa only [app.respond_environmentRecall] using secondBound)
        (by simpa only [app.respond_environmentRecall] using secondCallback)
      exact firstTurn.trans secondTurn.symm

end Vegas.Examples.CommitSeedBroadcast
