/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Errors accumulated at the exits of a region

Play until a stopping set from a history inside a region either stays in the
region, or leaves it at some step. When a payoff vanishes at the stops inside
the region, and every step from inside the region moves at most `κ` of the
expected payoff through the histories outside it, the expected payoff at the
stops is at most `κ` times a depth that every step decreases
(`GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_le_of_exits`).
Under a bounded horizon, the steps left before the horizon are such a depth
(`GameTheory.Protocol.InformationModel.length_of_mem_support_runBehavioralFrom_one`).
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} [Fintype ι] {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)

/-- One step of play from a nonterminal history extends its trace by one
transition. -/
theorem length_of_mem_support_runBehavioralFrom_one (policies : (i : ι) → M.BehavioralPolicy i)
    {history next : E.History} (running : ¬ E.terminal history.state)
    (member : next ∈ (M.runBehavioralFrom policies 1 history).support) :
    next.trace.length = history.trace.length + 1 := by
  rw [M.runBehavioralFrom_succ_of_not_terminal policies 0 running,
    PMF.mem_support_bind_iff] at member
  obtain ⟨draw, _, stepped⟩ := member
  rw [PMF.mem_support_bindOnSupport_iff] at stepped
  obtain ⟨target, realized, reached⟩ := stepped
  change next ∈ (PMF.pure _).support at reached
  rw [PMF.mem_support_pure_iff] at reached
  subst reached
  rfl

/-- **Errors accumulated at the exits of a region.** Let a payoff bounded by
`bound` vanish at the stopped and terminal histories of a region `inside`. Let
every one-step extension of an unstopped nonterminal history inside the region
decrease `depth`, and let the expected payoff of play until the stopping set
from the extensions outside the region, weighted by the step, be at most `κ`.
Then from every history inside the region the expected payoff of play until
the stopping set is at most `κ` times its depth. -/
theorem abs_expect_runBehavioralUntil_le_of_exits (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped inside : E.History → Prop)
    [DecidablePred inside] (payoff : E.History → ℝ) {bound κ : ℝ}
    (payoffBounded : ∀ history, |payoff history| ≤ bound) (nonnegative : 0 ≤ κ)
    (depth : E.History → ℕ)
    (atEnd : ∀ history, inside history → (stopped history ∨ E.terminal history.state) →
      payoff history = 0)
    (descends : ∀ history next, inside history → ¬ stopped history →
      ¬ E.terminal history.state → next ∈ (M.runBehavioralFrom policies 1 history).support →
      depth next + 1 ≤ depth history)
    (exits : ∀ history, inside history → ¬ stopped history → ¬ E.terminal history.state →
      |expect (M.runBehavioralFrom policies 1 history) (fun next => if inside next then 0
        else expect (M.runBehavioralUntil certificate policies stopped next) payoff)| ≤ κ) :
    ∀ history, inside history →
      |expect (M.runBehavioralUntil certificate policies stopped history) payoff| ≤
        κ * depth history := by
  classical
  have boundNonneg : ∀ history, 0 ≤ bound := fun history =>
    (abs_nonneg _).trans (payoffBounded history)
  have untilBounded : ∀ history,
      |expect (M.runBehavioralUntil certificate policies stopped history) payoff| ≤ bound :=
    fun history => expect_abs_le_of_bounded (boundNonneg history) payoffBounded
  intro start
  induction start using certificate.induction with
  | _ history ih =>
  intro holds
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies halt, expect_pure,
      atEnd history holds (Or.inl halt), abs_zero]
    exact mul_nonneg nonnegative (Nat.cast_nonneg _)
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended, expect_pure,
      atEnd history holds (Or.inr ended), abs_zero]
    exact mul_nonneg nonnegative (Nat.cast_nonneg _)
  let step := M.runBehavioralFrom policies 1 history
  let later := fun next => expect (M.runBehavioralUntil certificate policies stopped next) payoff
  let within := fun next => if inside next then later next else 0
  let outside := fun next => if inside next then 0 else later next
  obtain ⟨witness, witnessed⟩ := step.support_nonempty
  have positive : 1 ≤ depth history := by
    have := descends history witness holds halt ended witnessed
    omega
  have withinBound : ∀ next ∈ step.support, |within next| ≤ κ * (depth history - 1 : ℝ) := by
    intro next member
    simp only [within]
    split
    · rename_i nextInside
      have deeper := descends history next holds halt ended member
      have cast : (depth next : ℝ) ≤ (depth history : ℝ) - 1 := by
        have : ((depth next + 1 : ℕ) : ℝ) ≤ (depth history : ℝ) := by exact_mod_cast deeper
        push_cast at this
        linarith
      exact (ih next (M.mem_support_runBehavioralFrom_one policies ended member).1
        nextInside).trans (mul_le_mul_of_nonneg_left cast nonnegative)
    · rw [abs_zero]
      exact mul_nonneg nonnegative (by
        have : (1 : ℝ) ≤ depth history := by exact_mod_cast positive
        linarith)
  have withinIntegrable : PayoffIntegrable step within :=
    payoffIntegrable_of_bounded _ _ (C := bound) fun next => by
      simp only [within]
      split
      · exact untilBounded next
      · rw [abs_zero]
        exact boundNonneg next
  have outsideIntegrable : PayoffIntegrable step outside :=
    payoffIntegrable_of_bounded _ _ (C := bound) fun next => by
      simp only [outside]
      split
      · rw [abs_zero]
        exact boundNonneg next
      · exact untilBounded next
  rw [M.runBehavioralUntil_of_running certificate policies halt ended,
    expect_bind_tower_bounded _ _ _ payoffBounded]
  have splitEq : expect step later = expect step within + expect step outside := by
    rw [← expect_add withinIntegrable outsideIntegrable]
    apply expect_congr_on_support
    intro next _
    simp only [within, outside, later]
    split <;> ring
  change |expect step later| ≤ _
  rw [splitEq]
  calc |expect step within + expect step outside|
      ≤ |expect step within| + |expect step outside| := abs_add_le _ _
    _ ≤ κ * (depth history - 1 : ℝ) + κ := by
        refine add_le_add ?_ (exits history holds halt ended)
        rw [expect_congr_on_support (g := fun next =>
          if next ∈ step.support then within next else 0)
          (fun next member => by rw [ite_eq_left member ..])]
        apply expect_abs_le_of_bounded (mul_nonneg nonnegative (by
          have : (1 : ℝ) ≤ depth history := by exact_mod_cast positive
          linarith))
        intro next
        split
        · rename_i member
          exact withinBound next member
        · rw [abs_zero]
          exact mul_nonneg nonnegative (by
            have : (1 : ℝ) ≤ depth history := by exact_mod_cast positive
            linarith)
    _ = κ * depth history := by ring

end InformationModel

end GameTheory.Protocol
