/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialResponsePrefix
import Vegas.Examples.CommitSeedBroadcastInitialQuietReplay
import Vegas.Examples.CommitSeedBroadcastFirstLateEmptyLedger

/-! # Exact original history density on the quiet initial subevent -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The actual quiet snapshot fixes all three literal initial own records. -/
theorem original_quiet_initial_records (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (late : 5 ≤ execution.environmentRecall.length) (quiet : EmptyEarlySnapshot execution) :
    ∀ observer, ∃ later, execution.recall observer = initialWaitEntry observer :: later := by
  obtain ⟨first, second, third, snapshot, selected, inputs, records⟩ :=
    original_initial_response_prefix seed remaining execution owner trace late
  have empty := quiet snapshot (Option.mem_def.mpr selected)
  rw [inputs] at empty
  obtain ⟨firstWait, secondWait, thirdWait⟩ :=
    (afterInitialResponses_inputs_empty first second third).mp empty
  subst first
  subst second
  subst third
  intro observer
  obtain ⟨later, recalled⟩ := records observer
  refine ⟨later, ?_⟩
  have initialRecord :
      (afterInitialResponses ⟨none⟩ ⟨none⟩ ⟨none⟩).recall observer =
        [initialWaitEntry observer] := by
    fin_cases observer <;> rfl
  rw [initialRecord] at recalled
  simpa only [List.singleton_append] using recalled.symm

/-- The factor is the original probability of the three initial WAITs. The
same genuine native trace and the same nature coefficient occur on both sides. -/
theorem original_quiet_history_density
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : rawProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (fixed : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (late : 5 ≤ execution.environmentRecall.length) (quiet : EmptyEarlySnapshot execution) :
    (rawModel.historyReachWeight profile ⟨_, trace⟩).toReal =
      initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile) *
        (rawModel.historyReachWeight (initialQuietProfile profile) ⟨_, trace⟩).toReal :=
  initialQuietProfile_historyReach profile ⟨remaining, some owner, execution⟩ trace
    (original_quiet_initial_records seed remaining execution owner fixed late quiet)

/-- A bad original first-late history with empty receipts has this exact
quiet-prefix density, without conditioning the reference experiment on a future event. -/
theorem original_bad_firstLate_history_density
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : rawProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (fixed : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 2)
    (bad : seed.2 owner = false) (empty : execution.receipts = []) :
    (rawModel.historyReachWeight profile ⟨_, trace⟩).toReal =
      initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile) *
        (rawModel.historyReachWeight (initialQuietProfile profile) ⟨_, trace⟩).toReal := by
  have placement := original_first_late_input_placement seed
    ⟨remaining, some owner, execution⟩ fixed owner rfl original clock
  have quiet := bad_firstLate_empty_receipts_snapshot seed
    ⟨remaining, some owner, execution⟩ fixed owner rfl original clock bad empty
  have late : 5 ≤
      (⟨remaining, some owner, execution⟩ : app.Control).execution.environmentRecall.length := by
    rcases placement with good | failed <;> omega
  exact original_quiet_history_density profile seed remaining execution owner trace fixed late quiet

end Vegas.Examples.CommitSeedBroadcast
