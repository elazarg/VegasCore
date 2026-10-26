/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedCharge

/-! # Signed continuation residuals of the actual stopped runner

The target continuation value is evaluated under the source one-step law.
Its signed Bellman residual accumulates exactly to the difference of the two
stopped values. Positive and negative local discrepancies are retained rather
than replaced by their absolute values. The start may be any legal history;
bounded horizon and bounded payoff supply all integrability obligations.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

open Classical in
/-- Target continuation evaluated after a source step, minus its present value.
The residual is zero at the actual common stopping or terminal boundary. -/
def stoppedContinuationResidual (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped : E.History → Prop)
    (payoff : E.History → ℝ) (history : E.History) : ℝ :=
  if stopped history ∨ E.terminal history.state then 0 else
    expect (M.runBehavioralFrom source 1 history)
      (fun next => expect (M.runBehavioralUntil certificate target stopped next) payoff) -
        expect (M.runBehavioralUntil certificate target stopped history) payoff

theorem stoppedContinuationResidual_abs_le (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped : E.History → Prop)
    (payoff : E.History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) (history : E.History) :
    |M.stoppedContinuationResidual certificate source target stopped payoff history| ≤
      2 * bound := by
  classical
  unfold stoppedContinuationResidual
  split
  · simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) boundNonneg
  · have bounded : ∀ current,
        |expect (M.runBehavioralUntil certificate target stopped current) payoff| ≤ bound :=
      fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
    have localBound := expect_abs_le_of_bounded (μ := M.runBehavioralFrom source 1 history)
      boundNonneg bounded
    have subtract := abs_sub_le
      (expect (M.runBehavioralFrom source 1 history)
        (fun next => expect (M.runBehavioralUntil certificate target stopped next) payoff))
      0 (expect (M.runBehavioralUntil certificate target stopped history) payoff)
    simp only [sub_zero, zero_sub, abs_neg] at subtract
    exact subtract.trans ((add_le_add localBound (bounded history)).trans
      (by ring_nf; exact le_rfl))

/-- Exact performance difference at every starting history for the existing
stopped evaluator. No finite history carrier or finite nature is required. -/
theorem expect_runBehavioralUntil_sub_eq_expectedCharge {horizon : Nat}
    (bounded : E.BoundedHorizon horizon) (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped : E.History → Prop)
    (payoff : E.History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) (start : E.History) :
    expect (M.runBehavioralUntil certificate source stopped start) payoff -
        expect (M.runBehavioralUntil certificate target stopped start) payoff =
      M.expectedCharge certificate source stopped
        (M.stoppedContinuationResidual certificate source target stopped payoff) start := by
  classical
  let value := fun profile current =>
    expect (M.runBehavioralUntil certificate profile stopped current) payoff
  let residual := M.stoppedContinuationResidual certificate source target stopped payoff
  let total := M.expectedCharge certificate source stopped residual
  have valueBounded : ∀ profile current, |value profile current| ≤ bound :=
    fun _ _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have residualBounded : ∀ current, |residual current| ≤ 2 * bound :=
    M.stoppedContinuationResidual_abs_le certificate source target stopped payoff boundNonneg
      payoffBounded
  induction start using certificate.induction with
  | _ history ih =>
  by_cases halt : stopped history
  · simp only [M.runBehavioralUntil_of_stopped certificate source halt,
      M.runBehavioralUntil_of_stopped certificate target halt, expectedCharge,
      expect_pure, sub_self]
  by_cases ended : E.terminal history.state
  · simp only [M.runBehavioralUntil_of_terminal certificate source ended,
      M.runBehavioralUntil_of_terminal certificate target ended, expectedCharge,
      expect_pure, sub_self]
  let step := M.runBehavioralFrom source 1 history
  have drift := M.expectedCharge_drift_of_abs_le bounded certificate source stopped residual
    residualBounded history halt ended
  have matched : expect step (fun next => value source next - value target next) =
      expect step total := by
    apply expect_congr_on_support
    intro next member
    exact ih next (M.mem_support_runBehavioralFrom_one source ended member).1
  rw [M.runBehavioralUntil_of_running certificate source halt ended,
    expect_bind_tower_bounded _ _ _ payoffBounded]
  change expect step (value source) - value target history = total history
  calc
    _ = residual history + expect step (fun next => value source next - value target next) := by
      dsimp only [residual, stoppedContinuationResidual]
      rw [ite_eq_right (not_or_intro halt ended),
        expect_sub (payoffIntegrable_of_bounded step _ (valueBounded source))
          (payoffIntegrable_of_bounded step _ (valueBounded target))]
      change _ = (_ - value target history) + (_ - _)
      ring
    _ = total history := by rw [matched]; exact drift

end GameTheory.Protocol.InformationModel
