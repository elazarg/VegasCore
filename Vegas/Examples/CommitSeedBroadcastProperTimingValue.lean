/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperTiming
import Vegas.Examples.CommitSeedBroadcastNativeTimingWaitContext
import Interaction.ReactiveMenuFinishTrace

/-! # Actual original-posterior payoff bounds for proper first-late continuations -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  GameTheory.Enforcement

/-- Every genuine fixed-family counted terminal endpoint has zero audit
charge and the program's literal fixed-exclusion payoff. -/
theorem counted_fixed_endpoint_payoff (seed : Seeds) (after : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, after⟩)) (owner : Player) :
    netPayoff (app.finished after) owner =
      if owner ∈ after.application.current.excluded then -(3 / 2) else
        if ∃ other : Player, other ≠ owner ∧
          RecoveryState.publicationFailed after.application.current.native
            (revealEvent other) = true then 1 else 0 := by
  have complete := family_completesPlay seed ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace) ⟨rfl, rfl⟩
  have zero := PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
    (family seed) evidenceService ⟨some ⟨0, none, after⟩, trace⟩ owner
  change TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, after⟩) owner = 0 at zero
  change basePayoff (some ⟨0, none, after⟩) owner -
    TerminalAudit.charge app.stateTraffic audit (some ⟨0, none, after⟩) owner * deposit owner = _
  rw [zero, zero_mul, sub_zero]
  exact basePayoff_terminal_formula ⟨0, none, after⟩ complete owner

/-- Every counted continuation stays above the exclusion payoff, including
at an off-path pending response and with arbitrary foreign preparations. -/
theorem counted_fixed_finish_value_lower
    (seed : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    -(3 / 2 : ℝ) ≤ expect (app.finish initial horizon (family seed) players (some current))
      (fun state => netPayoff state owner) := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  rw [← expect_constant (app.finish initial horizon (family seed) players (some current))
    (-(3 / 2 : ℝ))]
  apply expect_mono ?_ (payoffIntegrable_constant _ _)
    (payoffIntegrable_of_bounded _ _ bounded)
  intro state reached
  obtain ⟨after, _continued, equal⟩ := PMF.support_map .. ▸ reached
  subst state
  obtain ⟨actual⟩ := countedMenu.finish_trace initial horizon (family seed) players covered
    (some current) trace (app.finished after) reached
  rw [counted_fixed_endpoint_payoff seed after actual owner]
  split_ifs <;> norm_num

/-- The same complete physical continuation has nonnegative value on every
good original seed when the focal owner uses the proper clock-two policy. -/
theorem proper_clock_two_good_fixed_finish_value_nonnegative
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (good : seed.2 owner = true)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 2 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (past : (scheduledProperPolicy 2 owner).Consistent (execution.recall owner)) :
    0 ≤ expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner) := by
  apply expect_nonneg
  intro state reached
  obtain ⟨after, _continued, equal⟩ := PMF.support_map .. ▸ reached
  subst state
  have survives := scheduled_proper_eligible_finish_survives 2 seed remaining execution owner trace
    request clock (by rw [good]; rfl) unsent players selected covered past after reached
  obtain ⟨actual⟩ := countedMenu.finish_trace initial horizon (family seed) players covered
    (some ⟨remaining, some owner, execution⟩) trace (app.finished after) reached
  rw [counted_fixed_endpoint_payoff seed after actual owner, ite_eq_right survives.2]
  split <;> norm_num

/-- The actual mixed continuation averages the original prefix posterior.
Its lower bound is expressed in the native history's unobserved bad-slot mark. -/
theorem counted_proper_clock_two_finish_value_lower
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 2 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (past : (scheduledProperPolicy 2 owner).Consistent (execution.recall owner)) :
    -(3 / 2 : ℝ) * firstLateBadValue (some ⟨remaining, some owner, execution⟩) ≤
      expect (app.finish initial horizon scheduler players
        (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner) := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  rw [native_finish_original_seed_law, expect_bind_tower_bounded _ _ _ bounded]
  have comparison := expect_mono (μ := implementation.posterior execution.environmentRecall)
    (f := fun seed => -(3 / 2 : ℝ) * (if seed.2 owner = false then 1 else 0))
    (g := fun seed => expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner))
    (fun seed supported => by
      obtain ⟨_original, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
        ⟨remaining, some owner, execution⟩ trace seed supported
      cases good : seed.2 owner with
      | false =>
          simpa only [good, ite_true, mul_one] using counted_fixed_finish_value_lower seed
            ⟨remaining, some owner, execution⟩ fixed owner players covered
      | true =>
          simpa only [good, Bool.true_eq_false, ite_false, mul_zero] using
            proper_clock_two_good_fixed_finish_value_nonnegative seed remaining execution owner
              fixed request clock good unsent players selected covered past)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_const_mul,
    counted_first_late_original_bad_value remaining execution owner trace request clock]
      at comparison
  exact comparison

end Vegas.Examples.CommitSeedBroadcast
