/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperTimingValue
import Vegas.Examples.CommitSeedBroadcastHelperPublicPackets

/-! # Proper continuation values after a remembered service signal -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A remembered clock-two receipt identifies the owner's original bad bit,
even when the current ledger and physical namespace have changed. -/
theorem remembered_receipted_firstLate_seed_bad (menu : app.ResponseMenu)
    (seed : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (earlier : List app.PlayerEntry) (entry : app.PlayerEntry)
    (later : List app.PlayerEntry)
    (recorded : current.execution.recall owner = earlier ++ entry :: later)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ []) : seed.2 owner = false := by
  obtain ⟨before, beforeTrace, _retained, active, _past, viewed, _allowed⟩ :=
    menu.recorded_response_at initial horizon (family seed) current trace owner earlier entry later
      recorded
  have originalBefore : before.execution.application.attempt = originalAttempt :=
    (congrArg (fun view : app.PlayerView => view.application.2.attempt) viewed).symm.trans original
  have clockBefore : before.execution.application.current.native.clock = 2 :=
    (congrArg (fun view : app.PlayerView => view.application.2.native.clock)
      viewed).symm.trans clock
  cases bit : seed.2 owner with
  | false => rfl
  | true =>
      have empty := original_good_firstLate_receipts_empty seed before
        (menu.toRawTrace initial horizon (family seed) beforeTrace) owner active originalBefore
          clockBefore bit
      have observed := congrArg ReactiveApplication.PlayerView.receipts viewed
      exact (receipted (observed.trans empty)).elim

/-- Sending at the seed's eligible physical clock and then following the
proper continuation gives nonnegative actual terminal payoff. -/
theorem proper_eligible_fixed_finish_value_nonnegative (slot : Nat)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = slot)
    (eligible : slot = lateClock (seed.2 owner))
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy slot owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (past : (scheduledProperPolicy slot owner).Consistent (execution.recall owner)) :
    0 ≤ expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner) := by
  apply expect_nonneg
  intro state reached
  obtain ⟨after, _continued, equal⟩ := PMF.support_map .. ▸ reached
  subst state
  have survives := scheduled_proper_eligible_finish_survives slot seed remaining execution owner
    trace request clock eligible unsent players selected covered past after reached
  obtain ⟨actual⟩ := countedMenu.finish_trace initial horizon (family seed) players covered
    (some ⟨remaining, some owner, execution⟩) trace (app.finished after) reached
  rw [counted_fixed_endpoint_payoff seed after actual owner, ite_eq_right survives.2]
  split <;> norm_num

/-- At a later original clock-three input, the recalled receipt signal makes
the whole proper continuation nonnegative under the actual original posterior. -/
theorem counted_proper_clock_three_finish_value_nonnegative
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 3)
    (earlier : List app.PlayerEntry) (entry : app.PlayerEntry) (later : List app.PlayerEntry)
    (recorded : execution.recall owner = earlier ++ entry :: later)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (firstClock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ [])
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 3 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (past : (scheduledProperPolicy 3 owner).Consistent (execution.recall owner)) :
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
  have bad := remembered_receipted_firstLate_seed_bad countedMenu seed
    ⟨remaining, some owner, execution⟩ fixed owner earlier entry later recorded original
      firstClock receipted
  exact proper_eligible_fixed_finish_value_nonnegative 3 seed remaining execution owner fixed
    request clock (by rw [bad]; rfl) unsent players selected covered past

end Vegas.Examples.CommitSeedBroadcast
