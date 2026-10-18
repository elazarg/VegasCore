/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperMiss
import Vegas.Examples.CommitSeedSignallingSnapshotOrigin

/-! # Initial own WAIT excludes an early Alice packet on every raw continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- An original zero-clock Alice record is the actual first response record,
including in raw histories with arbitrary later traffic and resets. -/
theorem alice_original_zero_clock_record_first (current : app.Control)
    (mixed : rawProtocol.Trace (some current))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall alice)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.1.publicView.clock = 0) :
    ∃ later, current.execution.recall alice = entry :: later := by
  obtain ⟨before, prior, _kept, active, observed, _allowed, later, recalled⟩ :=
    rawMenu.recorded_response_prefix initial horizon scheduler current mixed alice entry recorded
  have originalBefore : before.execution.application.attempt = originalAttempt := by
    rw [observed] at original
    exact original
  have zeroBefore : before.execution.application.current.native.clock = 0 := by
    rw [observed] at clock
    exact clock
  obtain (⟨_owner, first⟩ | ⟨impossible, _⟩) := original_zero_clock_decision before alice
    (rawMenu.toRawTrace initial horizon scheduler prior) active originalBefore zeroBefore
  · have initialRecall : before.execution.recall alice = [] := by
      rw [first]
      exact aliceFirst_recall alice
    rw [initialRecall, List.nil_append] at recalled
    exact ⟨later, recalled⟩
  · exact ((by decide : alice ≠ bob) impossible).elim

/-- The initial silent record is an observable own-recall condition. It
excludes an EARLY Alice envelope even when the foreign raw history is charged. -/
theorem alice_initial_wait_snapshot_empty (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, none, execution⟩))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice) :
    ∀ snapshot, execution.environmentRecall[2]? = some snapshot →
      ∀ message ∈ snapshot.beforeView.network.inputs, message.sender ≠ alice := by
  intro snapshot selected message input sender
  obtain ⟨entry, recorded, material, transmitted, _emitted, original, clock⟩ :=
    snapshot_packet_original_clock_zero seed remaining execution fixed snapshot selected alice
      message input sender
  obtain ⟨later, recalled⟩ := alice_original_zero_clock_record_first
    ⟨remaining, none, execution⟩ mixed entry recorded original clock
  obtain ⟨quietLater, quietRecall⟩ := alice_original_zero_clock_record_first
    ⟨remaining, none, execution⟩ mixed (originalResponseEntry aliceFirst alice ⟨none⟩) quiet
      initialState_attempt initialState_clock
  have same := (List.cons.inj (recalled.symm.trans quietRecall)).1
  rw [same] at transmitted
  change none = some material at transmitted
  cases transmitted

/-- The wrong-slot exclusion theorem uses the actual remembered initial
WAIT, rather than a separate hypothesis about an unobserved network snapshot. -/
theorem alice_wrong_packet_excluded_of_initial_wait (seed : Seeds) (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨0, none, execution⟩))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (bit : seedBits seed alice = true) (clean : OwnPermitted alice execution)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (request : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true) :
    alice ∈ execution.application.current.excluded :=
  alice_wrong_first_packet_excluded seed execution fixed bit clean entry recorded request clock
    message emitted packet (alice_initial_wait_snapshot_empty seed 0 execution mixed fixed quiet)

end Vegas.Examples.CommitSeedSignalling
