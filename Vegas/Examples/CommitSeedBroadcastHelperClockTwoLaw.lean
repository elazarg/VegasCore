/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperClockTwoValue

/-! # Original-posterior values of waiting at the receipted first-late input -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The unchanged original seed posterior identifies the bad slot from the
current receipt signal, and the whole proper continuation is nonnegative. -/
theorem counted_helper_clock_two_finish_value_nonnegative
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (receipted : execution.receipts ≠ [])
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 3 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    0 ≤ expect (app.finish initial horizon scheduler players
      (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner) := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  rw [native_finish_original_seed_law, expect_bind_tower_bounded _ _ _ bounded]
  apply expect_nonneg
  intro seed supported
  obtain ⟨_original, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some owner, execution⟩ trace seed supported
  have bad : seed.2 owner = false := by
    cases bit : seed.2 owner with
    | false => rfl
    | true =>
        exact (receipted (original_good_firstLate_receipts_empty seed _
          (countedMenu.toRawTrace initial horizon (family seed) fixed) owner rfl request.1.symm
            clock bit)).elim
  exact proper_bad_clock_two_finish_value_nonnegative seed remaining execution owner fixed
    request clock bad first word firstRequest silent zero players selected covered

end Vegas.Examples.CommitSeedBroadcast
