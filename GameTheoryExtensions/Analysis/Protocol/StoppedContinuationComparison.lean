/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Comparing stopped continuation expectations

One-step laws close along a preserved reference region give close stopped
expectations, with error accumulated over a decreasing depth.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

/-- One-step total variation errors accumulate only along reference continuations. -/
theorem abs_expect_runBehavioralUntil_sub_le_of_stepTV
    (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped inside : E.History → Prop)
    (payoff : E.History → ℝ) {bound error : ℝ}
    (boundNonneg : 0 ≤ bound) (errorNonneg : 0 ≤ error)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) (depth : E.History → ℕ)
    (closed : ∀ history next, inside history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom source 1 history).support →
      inside next)
    (descends : ∀ history next, inside history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom source 1 history).support →
      depth next + 1 ≤ depth history)
    (close : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      PMF.WithinTV error (M.runBehavioralFrom source 1 history)
        (M.runBehavioralFrom target 1 history)) :
    ∀ start, inside start →
      |expect (M.runBehavioralUntil certificate source stopped start) payoff -
        expect (M.runBehavioralUntil certificate target stopped start) payoff| ≤
          (2 * bound * error) * depth start := by
  classical
  let value := fun policies history =>
    expect (M.runBehavioralUntil certificate policies stopped history) payoff
  have bounded : ∀ policies history, |value policies history| ≤ bound :=
    fun _ _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have nonnegative : 0 ≤ 2 * bound * error := by positivity
  intro start
  induction start using certificate.induction with
  | _ history ih =>
  intro holds
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate source halt,
      M.runBehavioralUntil_of_stopped certificate target halt, sub_self, abs_zero]
    exact mul_nonneg nonnegative (Nat.cast_nonneg _)
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate source ended,
      M.runBehavioralUntil_of_terminal certificate target ended, sub_self, abs_zero]
    exact mul_nonneg nonnegative (Nat.cast_nonneg _)
  let step := M.runBehavioralFrom source 1 history
  let other := M.runBehavioralFrom target 1 history
  let gap := fun next => value source next - value target next
  have gapIntegrable : PayoffIntegrable step gap :=
    payoffIntegrable_sub
      (payoffIntegrable_of_bounded _ _ (C := bound) (bounded source))
      (payoffIntegrable_of_bounded _ _ (C := bound) (bounded target))
  obtain ⟨witness, witnessed⟩ := step.support_nonempty
  have positive : 1 ≤ depth history := by
    have := descends history witness holds halt ended witnessed
    omega
  have remainingNonneg : 0 ≤ (depth history : ℝ) - 1 := by
    have : (1 : ℝ) ≤ depth history := by exact_mod_cast positive
    linarith
  have gapBound : |expect step gap| ≤
      (2 * bound * error) * (depth history - 1 : ℝ) := by
    rw [expect_congr_on_support (g := fun next =>
      if next ∈ step.support then gap next else 0)
      (fun next member => by rw [ite_eq_left member ..])]
    apply expect_abs_le_of_bounded (mul_nonneg nonnegative remainingNonneg)
    intro next
    split
    · rename_i member
      have deeper := descends history next holds halt ended member
      have cast : (depth next : ℝ) ≤ (depth history : ℝ) - 1 := by
        have : ((depth next + 1 : ℕ) : ℝ) ≤ (depth history : ℝ) := by
          exact_mod_cast deeper
        push_cast at this
        linarith
      exact (ih next (M.mem_support_runBehavioralFrom_one source ended member).1
        (closed history next holds halt ended member)).trans
          (mul_le_mul_of_nonneg_left cast nonnegative)
    · rw [abs_zero]
      exact mul_nonneg nonnegative remainingNonneg
  have stepBound : |expect step (value target) - expect other (value target)| ≤
      2 * bound * error := by
    have first := (close history holds halt ended).expect_sub_le (value target) (-bound)
      (2 * bound) fun next _ => by
        have := abs_le.mp (bounded target next)
        constructor <;> linarith
    have second := (close history holds halt ended).symm.expect_sub_le (value target)
      (-bound) (2 * bound) fun next _ => by
        have := abs_le.mp (bounded target next)
        constructor <;> linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [M.runBehavioralUntil_of_running certificate source halt ended,
    M.runBehavioralUntil_of_running certificate target halt ended,
    expect_bind_tower_bounded _ _ _ payoffBounded,
    expect_bind_tower_bounded _ _ _ payoffBounded]
  change |expect step (value source) - expect other (value target)| ≤ _
  have splitEq : expect step (value source) - expect other (value target) =
      expect step gap + (expect step (value target) - expect other (value target)) := by
    rw [show gap = fun next => value source next - value target next from rfl,
      expect_sub
        (payoffIntegrable_of_bounded _ _ (C := bound) (bounded source))
        (payoffIntegrable_of_bounded _ _ (C := bound) (bounded target))]
    ring
  rw [splitEq]
  calc
    _ ≤ |expect step gap| +
        |expect step (value target) - expect other (value target)| := abs_add_le _ _
    _ ≤ (2 * bound * error) * (depth history - 1 : ℝ) + 2 * bound * error :=
      add_le_add gapBound stepBound
    _ = (2 * bound * error) * depth history := by ring

end GameTheory.Protocol.InformationModel
