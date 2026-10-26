/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import GameTheoryExtensions.Math.Probability.TotalVariation
import GameTheoryExtensions.Math.Probability.ExpectationContraction

/-! # Comparing stopped continuation expectations

Local continuation errors are paid by a nonnegative integrable potential on
a preserved reference region. A decreasing-depth estimate is a specialization.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

/-- A potential pays for local comparison errors and its expected continuation.
Only reference steps must preserve the region. Integrability is required there;
neither the history carrier nor the potential has to be finite or bounded. -/
theorem abs_expect_runBehavioralUntil_sub_le_of_potential
    (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped inside : E.History → Prop)
    (payoff : E.History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound)
    (charge potential : E.History → ℝ)
    (nonnegative : ∀ history, inside history → 0 ≤ potential history)
    (closed : ∀ history next, inside history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom source 1 history).support →
      inside next)
    (integrable : ∀ history, inside history → ¬ stopped history →
      ¬ E.terminal history.state →
      PayoffIntegrable (M.runBehavioralFrom source 1 history) potential)
    (pays : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      charge history + expect (M.runBehavioralFrom source 1 history) potential ≤
        potential history)
    (localError : ∀ history, inside history → ¬ stopped history →
      ¬ E.terminal history.state →
      |expect (M.runBehavioralFrom source 1 history) (fun next =>
          expect (M.runBehavioralUntil certificate target stopped next) payoff) -
        expect (M.runBehavioralFrom target 1 history) (fun next =>
          expect (M.runBehavioralUntil certificate target stopped next) payoff)| ≤
        charge history) :
    ∀ start, inside start →
      |expect (M.runBehavioralUntil certificate source stopped start) payoff -
        expect (M.runBehavioralUntil certificate target stopped start) payoff| ≤
        potential start := by
  classical
  let value := fun policies history =>
    expect (M.runBehavioralUntil certificate policies stopped history) payoff
  have bounded : ∀ policies history, |value policies history| ≤ bound :=
    fun _ _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  intro start
  induction start using certificate.induction with
  | _ history ih =>
  intro holds
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate source halt,
      M.runBehavioralUntil_of_stopped certificate target halt, sub_self, abs_zero]
    exact nonnegative history holds
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate source ended,
      M.runBehavioralUntil_of_terminal certificate target ended, sub_self, abs_zero]
    exact nonnegative history holds
  let step := M.runBehavioralFrom source 1 history
  let other := M.runBehavioralFrom target 1 history
  let gap := fun next => value source next - value target next
  have gapIntegrable : PayoffIntegrable step gap :=
    payoffIntegrable_sub
      (payoffIntegrable_of_bounded _ _ (C := bound) (bounded source))
      (payoffIntegrable_of_bounded _ _ (C := bound) (bounded target))
  have gapBound : |expect step gap| ≤ expect step potential := by
    apply (abs_expect_le_expect_abs step gap gapIntegrable).trans
    apply expect_mono _ (by simpa only [PayoffIntegrable, abs_abs] using gapIntegrable)
      (integrable history holds halt ended)
    intro next member
    exact ih next (M.mem_support_runBehavioralFrom_one source ended member).1
      (closed history next holds halt ended member)
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
  exact (abs_add_le _ _).trans ((add_le_add gapBound (localError history holds halt ended)).trans
    (by simpa only [add_comm] using pays history holds halt ended))

/-- Step-dependent total variation errors can be charged to an integrable
potential. No uniform depth or uniform one-step error is required. -/
theorem abs_expect_runBehavioralUntil_sub_le_of_stepTV_potential
    (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped inside : E.History → Prop)
    (payoff : E.History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound)
    (error potential : E.History → ℝ)
    (nonnegative : ∀ history, inside history → 0 ≤ potential history)
    (closed : ∀ history next, inside history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom source 1 history).support →
      inside next)
    (integrable : ∀ history, inside history → ¬ stopped history →
      ¬ E.terminal history.state →
      PayoffIntegrable (M.runBehavioralFrom source 1 history) potential)
    (pays : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      2 * bound * error history + expect (M.runBehavioralFrom source 1 history) potential ≤
        potential history)
    (close : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      PMF.WithinTV (error history) (M.runBehavioralFrom source 1 history)
        (M.runBehavioralFrom target 1 history)) :
    ∀ start, inside start →
      |expect (M.runBehavioralUntil certificate source stopped start) payoff -
        expect (M.runBehavioralUntil certificate target stopped start) payoff| ≤
        potential start := by
  apply M.abs_expect_runBehavioralUntil_sub_le_of_potential certificate source target
    stopped inside
    payoff boundNonneg payoffBounded (fun history => 2 * bound * error history) potential
    nonnegative closed integrable pays
  intro history holds halt ended
  have bounded : ∀ next,
      |expect (M.runBehavioralUntil certificate target stopped next) payoff| ≤ bound :=
    fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have stepBound := (close history holds halt ended).abs_expect_sub_le_interval
    (fun next => expect (M.runBehavioralUntil certificate target stopped next) payoff)
    (-bound) (2 * bound) (fun next _ => by
      have := abs_le.mp (bounded next)
      constructor <;> linarith)
  nlinarith [stepBound]

/-- An interval of width `width` incurs `width` times the local TV error.
Centering the payoff preserves the difference of the stopped expectations. -/
theorem abs_expect_runBehavioralUntil_sub_le_of_stepTV_interval_potential
    (certificate : E.WellFoundedHistories)
    (source target : ∀ who, M.BehavioralPolicy who) (stopped inside : E.History → Prop)
    (payoff : E.History → ℝ) {low width : ℝ} (widthNonneg : 0 ≤ width)
    (payoffBounded : ∀ history, low ≤ payoff history ∧ payoff history ≤ low + width)
    (error potential : E.History → ℝ)
    (nonnegative : ∀ history, inside history → 0 ≤ potential history)
    (closed : ∀ history next, inside history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom source 1 history).support →
      inside next)
    (integrable : ∀ history, inside history → ¬ stopped history →
      ¬ E.terminal history.state →
      PayoffIntegrable (M.runBehavioralFrom source 1 history) potential)
    (pays : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      width * error history + expect (M.runBehavioralFrom source 1 history) potential ≤
        potential history)
    (close : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      PMF.WithinTV (error history) (M.runBehavioralFrom source 1 history)
        (M.runBehavioralFrom target 1 history)) :
    ∀ start, inside start →
      |expect (M.runBehavioralUntil certificate source stopped start) payoff -
        expect (M.runBehavioralUntil certificate target stopped start) payoff| ≤
        potential start := by
  let center := low + width / 2
  have centered : ∀ history, |payoff history - center| ≤ width / 2 := by
    intro history
    obtain ⟨lower, upper⟩ := payoffBounded history
    dsimp only [center]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have originalIntegrable (law : PMF E.History) : PayoffIntegrable law payoff := by
    apply payoffIntegrable_of_bounded law _ (C := width / 2 + |center|)
    intro history
    calc |payoff history| = |payoff history - center + center| := by congr 1; ring
      _ ≤ |payoff history - center| + |center| := abs_add_le _ _
      _ ≤ width / 2 + |center| := add_le_add (centered history) le_rfl
  have factor : 2 * (width / 2) = width := by ring
  have comparison := M.abs_expect_runBehavioralUntil_sub_le_of_stepTV_potential certificate
    source target stopped inside (fun history => payoff history - center)
    (by positivity) centered error potential nonnegative closed integrable
    (fun history holds halt ended => by
      simpa only [factor] using pays history holds halt ended) close
  intro start holds
  have estimate := comparison start holds
  rw [expect_sub (originalIntegrable _) (payoffIntegrable_constant _ _),
    expect_sub (originalIntegrable _) (payoffIntegrable_constant _ _),
    expect_constant, expect_constant] at estimate
  convert estimate using 1
  congr 1
  ring

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
  let scale := 2 * bound * error
  have nonnegative : 0 ≤ scale := by dsimp [scale]; positivity
  apply M.abs_expect_runBehavioralUntil_sub_le_of_stepTV_potential certificate source target
    stopped inside payoff boundNonneg payoffBounded (fun _ => error)
    (fun history => scale * depth history)
    (fun _ _ => mul_nonneg nonnegative (Nat.cast_nonneg _)) closed _ _ close
  · intro history holds halt ended
    apply payoffIntegrable_of_bounded_on_support _ _ (C := scale * depth history)
    intro next member
    rw [abs_of_nonneg (mul_nonneg nonnegative (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (by
      exact_mod_cast
        (Nat.le_of_succ_le (descends history next holds halt ended member))) nonnegative
  · intro history holds halt ended
    have estimate : ∀ next ∈ (M.runBehavioralFrom source 1 history).support,
        scale * (depth next : ℝ) ≤ scale * ((depth history : ℝ) - 1) := by
      intro next member
      apply mul_le_mul_of_nonneg_left _ nonnegative
      have cast : ((depth next + 1 : ℕ) : ℝ) ≤ depth history := by
        exact_mod_cast (descends history next holds halt ended member)
      push_cast at cast
      linarith
    have integrable := payoffIntegrable_of_bounded_on_support
      (M.runBehavioralFrom source 1 history) (fun next => scale * (depth next : ℝ))
      (C := scale * depth history) (fun next member => by
        rw [abs_of_nonneg (mul_nonneg nonnegative (Nat.cast_nonneg _))]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast
          (Nat.le_of_succ_le (descends history next holds halt ended member))) nonnegative)
    have averaged := expect_le_const _ _ integrable _ estimate
    dsimp [scale] at averaged ⊢
    nlinarith [averaged]

end GameTheory.Protocol.InformationModel
