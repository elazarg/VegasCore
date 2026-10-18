/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialResponses
import Interaction.ReactiveProvenance
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactivePolicyInvariant

/-! # Original raw declarations recovered from the shared early snapshot -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem response_inputs_empty (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    (execution.respond app owner response).network.inputs = [] ↔
      execution.network.inputs = [] ∧ response.transmission = none := by
  rcases response with ⟨material⟩
  cases material <;> simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]

private theorem response_silent (response : app.Action) :
    response.transmission = none ↔ response = ⟨none⟩ := by
  cases response with
  | mk material => cases material <;> simp

/-- Empty initial traffic is exactly three literal initial WAIT responses. -/
theorem afterInitialResponses_inputs_empty (first second third : app.Action) :
    (afterInitialResponses first second third).network.inputs = [] ↔
      first = ⟨none⟩ ∧ second = ⟨none⟩ ∧ third = ⟨none⟩ := by
  rw [afterInitialResponses, response_inputs_empty]
  change (((initialBobCallback first).respond app bob second).network.inputs = [] ∧
    third.transmission = none) ↔ _
  rw [response_inputs_empty]
  change (((initialAliceCallback.respond app alice first).network.inputs = [] ∧
    second.transmission = none) ∧ third.transmission = none) ↔ _
  rw [response_inputs_empty]
  have initialInputs : initialAliceCallback.network.inputs = [] := rfl
  simp only [initialInputs, true_and, response_silent, and_assoc]

private theorem response_public (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    (execution.respond app owner response).application.publicView =
      execution.application.publicView := by
  rcases response with ⟨material⟩
  cases material with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

private theorem initial_recorded_view (first second third : app.Action) (owner : Player)
    (entry : app.PlayerEntry)
    (recorded : entry ∈ (afterInitialResponses first second third).recall owner) :
    entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
  have atAlice : initialAliceCallback.application.publicView = initialState.publicView := rfl
  have atBob : (initialBobCallback first).application.publicView = initialState.publicView :=
    response_public initialAliceCallback alice first
  have atCarol : (initialCarolCallback first second).application.publicView =
      initialState.publicView :=
    (response_public (initialBobCallback first) bob second).trans atBob
  have zero (execution : app.Execution)
      (same : execution.application.publicView = initialState.publicView) :
      (execution.observe app owner).application.2.attempt = originalAttempt ∧
        (execution.observe app owner).application.1.publicView.clock = 0 := by
    have attempt := congrArg PhasePublicView.attempt same
    have clock := congrArg (fun view : PhasePublicView graph => view.native.clock) same
    exact ⟨attempt.trans initialState_attempt, clock.trans initialState_clock⟩
  rcases app.respond_entry_origin (initialCarolCallback first second) carol owner third entry
      recorded with before | fresh
  · change entry ∈ ((initialBobCallback first).respond app bob second).recall owner at before
    rcases app.respond_entry_origin (initialBobCallback first) bob owner second entry before with
      prior | fresh
    · change entry ∈ (initialAliceCallback.respond app alice first).recall owner at prior
      rcases app.respond_entry_origin initialAliceCallback alice owner first entry prior with
        absent | fresh
      · exact (List.not_mem_nil absent).elim
      · rw [fresh.2]
        exact zero initialAliceCallback atAlice
    · rw [fresh.2]
      exact zero (initialBobCallback first) atBob
  · rw [fresh.2]
    exact zero (initialCarolCallback first second) atCarol

private theorem recall_retained (selected : app.Scheduler) (players : Player → app.Policy)
    (count : Nat) (first last : app.Execution)
    (supported : last ∈ (app.runRounds selected players count first).support) :
    ∀ owner, first.recall owner ⊆ last.recall owner := by
  let property : app.Execution → Prop := fun current =>
    ∀ owner, first.recall owner ⊆ current.recall owner
  have invariant : app.PolicyInvariant players property := by
    constructor
    · intro current actor action valid _selected owner
      exact List.Subset.trans (valid owner) (app.respond_recall_mono current actor owner action)
    · intro current next command valid reached owner
      rw [app.environmentStep_recall current next command reached]
      exact valid owner
  exact invariant.runRounds selected count first last (fun _ => List.Subset.refl _) supported

/-- Every snapshot packet is its sender's literal original clock-zero
raw declaration, still recalled after any later retry or phase advance. -/
theorem snapshot_packet_original_clock_zero (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[3]? = some snapshot)
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ snapshot.beforeView.network.inputs) (authored : message.sender = owner) :
    ∃ entry ∈ execution.recall owner, ∃ material,
      entry.action.transmission = some material ∧ entry.emitted = some message ∧
        entry.beforeView.application.2.attempt = originalAttempt ∧
          entry.beforeView.application.1.publicView.clock = 0 := by
  classical
  let players := ReactiveApplication.anchoredPolicy execution (fun _ => app.silentPolicy)
  have actual := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace initial horizon
    (family seed) (fun _ => app.silentPolicy) trace
  have initialized : execution ∈ (app.runRounds (family seed) players (horizon - remaining)
      initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actual.2
  obtain ⟨bounded, snapshotEq⟩ := List.getElem?_eq_some_iff.mp selected
  have recorded : execution.environmentRecall = execution.environmentRecall.take 3 ++
      snapshot :: execution.environmentRecall.drop 4 := by
    rw [← snapshotEq, List.getElem_cons_drop bounded, List.take_append_drop]
  obtain ⟨used, rest, before, middle, _length, prior, recalled, viewed,
    chosen, dispatched, future⟩ := app.runRounds_recorded_entry (family seed) players
      (horizon - remaining) initialExecution execution initialized
        (execution.environmentRecall.take 3) snapshot (execution.environmentRecall.drop 4)
          (by simpa only [initialExecution, ReactiveApplication.Execution.initial,
            List.nil_append] using recorded)
  change before.environmentRecall = execution.environmentRecall.take 3 at recalled
  have count : before.environmentRecall.length = 3 := by
    rw [recalled, List.length_take, Nat.min_eq_left (Nat.le_of_lt bounded)]
  have usedEq : used = 3 := by
    have accounted := app.runRounds_environmentRecall_length (family seed) players used
      initialExecution before prior
    change before.environmentRecall.length = 0 + used at accounted
    omega
  have beforeFrom : before ∈ (app.roundsFrom initial (family seed) players used).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialState, by rw [initial]; simp, prior⟩
  have within : used ≤ horizon := by rw [usedEq]; decide
  obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seed) players used
    within before beforeFrom
  have beforeInput : message ∈ before.network.inputs := by
    rw [viewed] at input
    exact input
  obtain ⟨entry, member, material, transmitted, emitted, _state, _known, _packet⟩ :=
    (app.history_provenance initial horizon (family seed) beforeTrace).inputs message beforeInput
  rw [authored] at member
  have firstRound : middle ∈ (app.round (family seed) players before).support := by
    rw [ReactiveApplication.round, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨snapshot.command, chosen, dispatched⟩
  have suffix : execution ∈ (app.runRounds (family seed) players (rest + 1) before).support := by
    change execution ∈ ((app.round (family seed) players before).bind
      (app.runRounds (family seed) players rest)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨middle, firstRound, future⟩
  have retained := recall_retained (family seed) players (rest + 1) before execution suffix
    owner member
  rw [usedEq, first_three_rounds] at prior
  obtain ⟨first, _firstSupport, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ prior)
  obtain ⟨second, _secondSupport, thirdLaw⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  obtain ⟨third, _thirdSupport, actual⟩ := PMF.support_map .. ▸ thirdLaw
  have geometry : entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
    rw [← actual] at member
    exact initial_recorded_view first second third owner entry member
  exact ⟨entry, retained, material, transmitted, emitted, geometry⟩

end Vegas.Examples.CommitSeedBroadcast
