/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveStopping
import Interaction.ReactiveSchedulerTranscript
import Interaction.ReactiveServiceRounds
import Interaction.ReactiveResponseAccounting

/-! # Recorded environment entries retain actual round-prefix witnesses -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Seed : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Actual rounds append exactly their command records to the existing complete
recall. The existing prefix is never reconstructed from a projected state. -/
theorem runRounds_environmentRecall_append (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution next : app.Execution)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    ∃ later, next.environmentRecall = execution.environmentRecall ++ later ∧
      later.length = count := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨[], (List.append_nil _).symm, rfl⟩
  | succ count ih =>
      obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨later, recalled, length⟩ := ih middle tail
      refine ⟨⟨execution.observeEnvironment app, command⟩ :: later, ?_, ?_⟩
      · rw [recalled, app.dispatch_environmentRecall players command execution middle dispatched]
        simp only [List.append_assoc, List.singleton_append]
      · simp only [List.length_cons, length]

/-- An entry in the actual appended environment recall identifies a supported
prefix, its real command transition, and the supported remaining rounds. -/
theorem runRounds_recorded_entry (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution next : app.Execution)
    (reached : next ∈ (app.runRounds scheduler players count execution).support)
    (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry)
    (after : List app.EnvironmentEntry)
    (recorded : next.environmentRecall = execution.environmentRecall ++ before ++ entry :: after) :
    ∃ used remaining prior middle,
      used + 1 + remaining = count ∧
      prior ∈ (app.runRounds scheduler players used execution).support ∧
      prior.environmentRecall = execution.environmentRecall ++ before ∧
      entry.beforeView = prior.observeEnvironment app ∧
      entry.command ∈ (scheduler prior.environmentRecall (prior.observeEnvironment app)).support ∧
      middle ∈ (app.dispatch players entry.command prior).support ∧
      next ∈ (app.runRounds scheduler players remaining middle).support := by
  induction count generalizing execution before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have impossible := congrArg List.length recorded
      simp only [List.length_append, List.length_cons] at impossible
      omega
  | succ count ih =>
      obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨later, recalled, _⟩ :=
        app.runRounds_environmentRecall_append scheduler players count middle next tail
      have middleRecall :=
        app.dispatch_environmentRecall players command execution middle dispatched
      have entries : (⟨execution.observeEnvironment app, command⟩ : app.EnvironmentEntry) ::
          later =
          before ++ entry :: after := by
        apply List.append_cancel_left (as := execution.environmentRecall)
        simpa only [recalled, middleRecall, List.append_assoc, List.singleton_append]
          using recorded
      cases before with
      | nil =>
          have firstEq : (⟨execution.observeEnvironment app, command⟩ : app.EnvironmentEntry) =
              entry := (List.cons.inj entries).1
          cases firstEq
          refine ⟨0, count, execution, middle, by omega, ?_, ?_, rfl, chosen, dispatched, tail⟩
          · exact (PMF.mem_support_pure_iff _ _).mpr rfl
          · exact (List.append_nil _).symm
      | cons first before =>
          have firstEq := (List.cons.inj entries).1
          have laterEq := (List.cons.inj entries).2
          have tailRecord : next.environmentRecall = middle.environmentRecall ++
              before ++ entry :: after := by
            rw [recalled, laterEq]
            exact (List.append_assoc middle.environmentRecall before (entry :: after)).symm
          obtain ⟨used, remaining, prior, following, length, priorReached, priorRecall,
            view, selected, nextReached, finalReached⟩ := ih middle tail before tailRecord
          refine ⟨used + 1, remaining, prior, following, by omega, ?_, ?_, view, selected,
            nextReached, finalReached⟩
          · change prior ∈ ((app.round scheduler players execution).bind
                (app.runRounds scheduler players used)).support
            rw [PMF.support_bind]
            exact Set.mem_iUnion₂.mpr ⟨middle, moved, priorReached⟩
          · rw [priorRecall, middleRecall]
            simp only [List.append_assoc, List.singleton_append, firstEq]

/-- Every command recorded by a fixed original seed is consistent with that
seed at its complete actual earlier recall. -/
theorem deterministic_transcript_invariant
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (seed : Seed) : app.ServiceInvariant (fun past view => PMF.pure (choose seed past view))
      (fun execution => app.commandConsistentFrom choose seed [] execution.environmentRecall) where
  respond execution who action valid := by
    rw [app.respond_environmentRecall]
    exact valid
  environment execution next command valid selected reached := by
    rw [app.environmentStep_environmentRecall execution next command reached,
      app.commandConsistent_snoc]
    exact ⟨valid, ((PMF.mem_support_pure_iff _ _).mp selected).symm⟩

end Interaction.ReactiveApplication
