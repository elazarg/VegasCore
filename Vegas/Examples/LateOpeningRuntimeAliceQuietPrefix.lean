/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstDecision
import Vegas.Examples.LateOpeningRuntimeProtectedOpening
import Vegas.Pending.ReactiveOpeningEvidence
import Vegas.Pending.ReactiveAssociationPersistence
import Interaction.ReactiveRoundTrace

/-! # Silence leads to an actual final opening decision

After Alice emits no packet at her first late callback, the next three
complete rounds permit arbitrary Bob responses and protected Bob service.
The following Alice activation is a legal bounded raw history with her
initial opening still ready and timely. No opponent policy, pending packet
classification or posterior restriction is assumed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem no_alice_command (execution : app.Execution)
    (position : 4 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length < 7) (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall (execution.observeEnvironment app)).support) :
    command.actor? app ≠ some alice := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
    (execution.observeEnvironment app)).support at selected
  generalize cursorEq : execution.environmentRecall.length = cursor at selected position early
  interval_cases cursor <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals subst command
  · decide
  · unfold latestAuthor
    split <;> simp [ReactiveApplication.Command.actor?]
  · decide

private theorem resume_recall (players : Player → app.Policy)
    (actor : Option Player) (execution next : app.Execution)
    (absent : actor ≠ some alice)
    (reached : next ∈ (app.resume players actor execution).support) :
    next.recall alice = execution.recall alice := by
  cases actor with
  | none => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | some who =>
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact app.respond_recall_other execution who alice
        (fun same => absent (congrArg some same.symm)) response

private theorem before_final_recall (players : Player → app.Policy)
    (count : Nat) (execution next : app.Execution)
    (position : 4 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length + count ≤ 7)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : next.recall alice = execution.recall alice := by
  induction count generalizing execution with
  | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨observed, sampled, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have absent := no_alice_command weight nonnegative execution position (by omega)
        command selected
      have framed := (resume_recall players _ observed middle absent resumed).trans
        (congrFun (app.environmentStep_recall execution observed command sampled) alice)
      have length := app.dispatch_environmentRecall players command execution middle dispatched
      have counts : middle.environmentRecall.length = execution.environmentRecall.length + 1 := by
        rw [length, List.length_append, List.length_singleton]
      exact (ih middle (by omega) (by omega) continued).trans framed

/-- An actual supported continuation after first-late silence produces the
full final-opening interface and a legal bounded raw trace. -/
theorem final_decision_of_silence
    (first : LateOpeningRuntimeAliceFirstDecision.DecisionHistory weight nonnegative)
    (bounded : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨22, some alice, first.execution⟩))
    (players : Player → app.Policy)
    (admissible : ∀ who, rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (players who))
    (middle next : app.Execution)
    (reached : middle ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 3 (first.execution.respond app alice ⟨none⟩)).support)
    (activated : next ∈ (middle.environmentStep app (.activate alice)).support) :
    ∃ final : LateOpeningRuntimeAliceEmptyDecision.DecisionHistory weight nonnegative,
      final.execution = next ∧ final.bit = first.bit ∧
      Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨18, some alice, next⟩)) := by
  classical
  let silent := first.execution.respond app alice ⟨none⟩
  have cursor : silent.environmentRecall.length = 4 := by
    rw [app.respond_environmentRecall]
    exact LateOpeningRuntimeAliceFirstDecision.decision_cursor weight nonnegative first
  have available : (⟨none⟩ : app.Action) ∈ rawMenu.actions alice
      (first.execution.recall alice) (first.execution.observe app alice) := by
    exact bounds.silent_available LateOpeningRuntimeService.runtime leaks alice _ _
  obtain ⟨responded⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 22 first.execution alice ⟨none⟩
      bounded available
  obtain ⟨intermediate⟩ := rawMenu.trace_runRounds_of_admissible initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      players admissible 19 3 silent middle responded reached
  have middleCursor : middle.environmentRecall.length = 7 := by
    have counts := app.runRounds_environmentRecall_length
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 3 silent middle reached
    omega
  have selected : (.activate alice : app.Command) ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative middle.environmentRecall
        (middle.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative middle.environmentRecall.length _).support
    rw [middleCursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨finalTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 middle next (.activate alice)
      intermediate selected activated
  have rawTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) finalTrace
  have nextRecall : next.recall alice = silent.recall alice :=
    (congrFun (app.environmentStep_recall middle next (.activate alice) activated) alice).trans
      (before_final_recall weight nonnegative players 3 silent middle
        (by omega) (by omega) reached)
  have quiet : app.outputs (next.recall alice) = [] := by
    rw [nextRecall]
    simpa [silent, ReactiveApplication.Execution.respond, ReactiveApplication.outputs,
      List.filterMap_append, ReactiveApplication.PlayerEntry.emitted] using first.quiet
  have pending := LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty weight nonnegative
    ⟨18, some alice, next⟩ rawTrace (by simp) quiet
  have stillUnfinished : aliceEvent ∉ middle.application.config.cut.completed := by
    rw [LateOpeningRuntimeProtectedOpening.before_lottery_completed weight nonnegative
      players 3 silent middle (by omega) (by omega) reached]
    rw [(LateOpeningRuntimeService.runtime.reactive_respond_application
      leaks first.execution alice ⟨none⟩).1]
    exact first.ready.1
  have sameConfig : next.application.config = middle.application.config := by
    obtain ⟨sampled, moved, rfl⟩ := PMF.support_map .. ▸ activated
    obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ moved
    rfl
  have ready : next.application.config.cut.Ready aliceEvent := by
    refine ⟨?_, ?_⟩
    · rwa [sameConfig]
    · change ∅ ⊆ next.application.config.cut.completed
      exact Finset.empty_subset _
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨18, some alice, next⟩ rawTrace
  have nextCursor : next.environmentRecall.length = 8 := by
    have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace
    change next.environmentRecall.length + 18 = 26 at accounted
    omega
  have clock : next.application.clock = 2 := by
    rw [clock_history weight nonnegative _ rawTrace, nextCursor]
    decide
  have timely : next.application.WithinDeadline LateOpeningRuntimeService.runtime aliceEvent := by
    have active := (valid.activated_iff aliceEvent).mpr ⟨ready, rfl⟩
    obtain ⟨entered, entry⟩ := Option.isSome_iff_exists.mp active
    change (match next.application.activatedAt aliceEvent with
      | none => False | some entered => next.application.clock - entered < 3)
    rw [entry, clock]
    omega
  have lift (predicate : app.State → Prop) (invariant : app.Invariant predicate)
      (holds : predicate first.execution.application) : predicate next.application :=
    invariant.environmentStep middle next (.activate alice)
      ((ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 3 silent middle
          (invariant.respond first.execution alice ⟨none⟩ holds) reached) activated
  have bound : aliceBinding.get? next.application.config.store = some (.success first.bit) := by
    exact lift _ (LateOpeningRuntimeService.runtime.reactiveStoreInvariant
      leaks aliceBinding.field (.success first.bit)) first.bound
  have associationInvariant := LateOpeningRuntimeService.runtime.reactiveAssociationInvariant
    leaks aliceBinding.field aliceCandidate
  have linked := associationInvariant.history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (by
      intro state supported
      change state ∈ (setup.initialLaw.map (fun source =>
        EventGraphRuntime.State.initial (graph := nativeGraph) (setup.eventInputs source))).support
          at supported
      obtain ⟨source, selected, rfl⟩ := PMF.support_map .. ▸ supported
      obtain ⟨initialBit, initialLabel, rfl⟩ := (initialLaw_support source).mp selected
      exact ⟨EventGraphRuntime.State.initial_bindingInvariant _, rfl⟩) first.trace
  have associated := (lift _ associationInvariant linked).2
  have fixed := lift _ (LateOpeningRuntimeService.runtime.reactiveCandidateInvariant
    leaks aliceCandidate (⟨.bool, first.bit⟩ : Raw simpleExpr)) first.fixed
  exact ⟨⟨next, rawTrace, first.bit, quiet, pending, ready, timely, bound, associated, fixed⟩,
    rfl, rfl, ⟨finalTrace⟩⟩

end Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix
