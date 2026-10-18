/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingEarlySnapshot
import Vegas.Examples.CommitSeedSignallingPrivacy
import Interaction.ReactiveProvenance

/-! # The actual early snapshot retains original clock-zero declarations -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem first_two_entries_clock_zero (first second : app.Action) (owner : Player)
    (entry : app.PlayerEntry) (member : entry ∈ (afterFirstTwo first second).recall owner) :
    entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
  rcases app.respond_entry_origin (bobFirst first) bob owner second entry member with
    earlier | fresh
  · change entry ∈ (aliceResponded first).recall owner at earlier
    rcases app.respond_entry_origin aliceFirst alice owner first entry earlier with prior | fresh
    · rw [aliceFirst_recall owner] at prior
      exact (List.not_mem_nil prior).elim
    · rw [fresh.2]
      constructor
      · change aliceFirst.application.attempt = originalAttempt
        rw [aliceFirst_application]
        exact initialState_attempt
      · change aliceFirst.application.current.native.clock = 0
        rw [aliceFirst_application]
        exact initialState_clock
  · rw [fresh.2]
    constructor
    · change (aliceResponded first).application.attempt = originalAttempt
      exact aliceResponded_attempt first
    · change (aliceResponded first).application.current.native.clock = 0
      have same := congrArg (fun view : PhasePublicView graph => view.native.clock)
        (aliceResponded_public first)
      change (aliceResponded first).application.current.native.clock =
        initialState.current.native.clock at same
      exact same.trans initialState_clock

/-- Every own envelope in the early snapshot comes from its actual original
clock-zero raw declaration, retained in the final own recall through every
later reset. This imposes no policy, counted-menu or final-live hypothesis. -/
theorem snapshot_packet_original_clock_zero (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (snapshot : app.EnvironmentEntry) (selected : execution.environmentRecall[2]? = some snapshot)
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ snapshot.beforeView.network.inputs) (authored : message.sender = owner) :
    ∃ entry ∈ execution.recall owner, ∃ material,
      entry.action.transmission = some material ∧ entry.emitted = some message ∧
        entry.beforeView.application.2.attempt = originalAttempt ∧
          entry.beforeView.application.1.publicView.clock = 0 := by
  classical
  let players := rawMenu.uniformResponses
  obtain ⟨bounded, snapshotEq⟩ := List.getElem?_eq_some_iff.mp selected
  have recorded : execution.environmentRecall = execution.environmentRecall.take 2 ++
      snapshot :: execution.environmentRecall.drop 3 := by
    rw [← snapshotEq, List.getElem_cons_drop bounded, List.take_append_drop]
  have supported := rawMenu.roundSupported_uniform initial horizon (family seeds) trace
  have initialized := supported.2
  rw [ReactiveApplication.roundsFrom, PMF.support_bind] at initialized
  obtain ⟨state, stateSupport, initialized⟩ := Set.mem_iUnion₂.mp initialized
  rw [initial_eq_pure, PMF.mem_support_pure_iff] at stateSupport
  subst state
  obtain ⟨used, rest, before, middle, _length, prior, recalled, viewed,
    chosen, dispatched, future⟩ := app.runRounds_recorded_entry (family seeds) players
      execution.environmentRecall.length initialExecution execution initialized
        (execution.environmentRecall.take 2) snapshot (execution.environmentRecall.drop 3)
          (by simpa only [initialExecution, ReactiveApplication.Execution.initial,
            List.nil_append] using recorded)
  change before.environmentRecall = execution.environmentRecall.take 2 at recalled
  have count : before.environmentRecall.length = 2 := by
    rw [recalled, List.length_take, Nat.min_eq_left (Nat.le_of_lt bounded)]
  have usedEq : used = 2 := by
    have accounted := app.runRounds_environmentRecall_length (family seeds) players used
      initialExecution before prior
    change before.environmentRecall.length = 0 + used at accounted
    omega
  have beforeFrom : before ∈ (app.roundsFrom initial (family seeds) players used).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialState, by rw [initial_eq_pure]; simp, prior⟩
  have within : used ≤ horizon := by rw [usedEq]; decide
  obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seeds) players used
    within before beforeFrom
  have beforeInput : message ∈ before.network.inputs := by
    rw [viewed] at input
    exact input
  obtain ⟨entry, member, material, transmitted, emitted, _state, _known, _packet⟩ :=
    (app.history_provenance initial horizon (family seeds) beforeTrace).inputs message beforeInput
  rw [authored] at member
  have firstRound : middle ∈ (app.round (family seeds) players before).support := by
    rw [ReactiveApplication.round, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨snapshot.command, chosen, dispatched⟩
  have suffix : execution ∈ (app.runRounds (family seeds) players (rest + 1) before).support := by
    change execution ∈ ((app.round (family seeds) players before).bind
      (app.runRounds (family seeds) players rest)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨middle, firstRound, future⟩
  have retained := runRounds_recall_mono (family seeds) players (rest + 1) before execution suffix
    owner member
  rw [usedEq, first_two_rounds] at prior
  obtain ⟨first, _firstSupport, secondLaw⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ prior)
  obtain ⟨second, _secondSupport, actual⟩ := PMF.support_map .. ▸ secondLaw
  have geometry : entry.beforeView.application.2.attempt = originalAttempt ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
    rw [← actual] at member
    exact first_two_entries_clock_zero first second owner entry member
  exact ⟨entry, retained, material, transmitted, emitted, geometry⟩

end Vegas.Examples.CommitSeedSignalling
