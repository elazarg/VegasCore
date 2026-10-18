/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperEarlyTiming

/-! # Nonnegative value of the proper initial transmission -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The actual fixed-seed proper initial continuation has nonnegative value
under arbitrary counted opponents, including unusable foreign preparations. -/
theorem proper_early_fixed_finish_value_nonnegative
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 0 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    0 ≤ expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner) := by
  apply expect_nonneg
  intro state reached
  obtain ⟨after, _continued, equal⟩ := PMF.support_map .. ▸ reached
  subst state
  have survives := scheduled_proper_early_finish_survives seed remaining execution owner trace
    request clock word players selected covered after reached
  obtain ⟨actual⟩ := countedMenu.finish_trace initial horizon (family seed) players covered
    (some ⟨remaining, some owner, execution⟩) trace (app.finished after) reached
  rw [counted_fixed_endpoint_payoff seed after actual owner, ite_eq_right survives.2]
  split <;> norm_num

/-- Averaging over the original native posterior preserves that lower bound;
there is no prescribed initial belief or source-value assumption. -/
theorem counted_proper_early_finish_value_nonnegative
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 0)
    (word : execution.recall owner = [])
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 0 owner)
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
  exact proper_early_fixed_finish_value_nonnegative seed remaining execution owner fixed
    request clock word players selected covered

end Vegas.Examples.CommitSeedBroadcast
