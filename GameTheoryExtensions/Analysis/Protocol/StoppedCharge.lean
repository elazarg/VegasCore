/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Automatic stopped potentials from bounded history-dependent charges

The charge is summed over actual prefix histories. Expected future cumulative
charge under the existing stopped runner is a nonnegative integrable potential
with exact one-step drift. A bounded horizon suffices; no finite nature or finite
history carrier is required. Current stopped/terminal histories pay no further charge.
-/

noncomputable section

namespace GameTheory.Protocol.ExecutionProtocol

open GameTheory.Math.Probability

variable {Player : Type*} {E : ExecutionProtocol Player}

/-- An additive fold over the actual prefix histories, not merely endpoint states. -/
def traceCharge (charge : E.History → ℝ) : ∀ {state}, E.Trace state → ℝ
  | _, .start => 0
  | _, .extend prior _ _ _ => traceCharge charge prior + charge ⟨_, prior⟩

/-- Total charge already paid along the strict prefixes of this actual history. -/
def cumulativeCharge (charge : E.History → ℝ) (history : E.History) : ℝ :=
  traceCharge charge history.trace

theorem trace_length_le {horizon : Nat} (bounded : E.BoundedHorizon horizon)
    (history : E.History) : history.trace.length ≤ horizon := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => exact Nat.zero_le _
  | extend prior joint legal realized =>
      have shorter : prior.length < horizon := by
        by_contra long
        exact legal.1 (bounded _ prior (by omega))
      change prior.length + 1 ≤ horizon
      omega

theorem cumulative_bounds (charge : E.History → ℝ) {bound : ℝ}
    (nonnegative : ∀ history, 0 ≤ charge history)
    (atMost : ∀ history, charge history ≤ bound) (history : E.History) :
    0 ≤ cumulativeCharge charge history ∧
      cumulativeCharge charge history ≤ bound * history.trace.length := by
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => simp [cumulativeCharge, traceCharge, Trace.length]
  | @extend source target prior joint legal realized ih =>
      obtain ⟨lower, upper⟩ := ih
      have localLower := nonnegative ⟨source, prior⟩
      have localUpper := atMost ⟨source, prior⟩
      simp only [cumulativeCharge, traceCharge, Trace.length, Nat.cast_add, Nat.cast_one] at *
      constructor <;> nlinarith

theorem cumulative_mono (charge : E.History → ℝ)
    (nonnegative : ∀ history, 0 ≤ charge history) {first last : E.History}
    (priorPath : TracePrefix first.trace last.trace) :
    cumulativeCharge charge first ≤ cumulativeCharge charge last := by
  rcases first with ⟨firstState, firstTrace⟩
  rcases last with ⟨lastState, lastTrace⟩
  change TracePrefix firstTrace lastTrace at priorPath
  change traceCharge charge firstTrace ≤ traceCharge charge lastTrace
  induction priorPath with
  | refl => exact le_rfl
  | @extend source target prior earlier joint legal realized ih =>
      change _ ≤ traceCharge charge prior + charge ⟨source, prior⟩
      exact ih.trans (le_add_of_nonneg_right (nonnegative _))

theorem cumulative_integrable {horizon : Nat} (bounded : E.BoundedHorizon horizon)
    (charge : E.History → ℝ) {bound : ℝ}
    (nonnegative : ∀ history, 0 ≤ charge history)
    (atMost : ∀ history, charge history ≤ bound) (law : PMF E.History) :
    PayoffIntegrable law (cumulativeCharge charge) := by
  have boundNonnegative : 0 ≤ bound := (nonnegative E.initHistory).trans (atMost E.initHistory)
  apply payoffIntegrable_of_bounded law _ (C := bound * horizon)
  intro history
  obtain ⟨lower, upper⟩ := cumulative_bounds charge nonnegative atMost history
  rw [abs_of_nonneg lower]
  exact upper.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast trace_length_le bounded history)
    boundNonnegative)

end GameTheory.Protocol.ExecutionProtocol

namespace GameTheory.Protocol.InformationModel

open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

/-- Honest future charge until the existing stopping rule or terminal boundary.
The current prefix contributes only if execution actually continues from it. -/
def expectedCharge (certificate : E.WellFoundedHistories)
    (profile : ∀ who, M.BehavioralPolicy who) (stopped : E.History → Prop)
    (charge : E.History → ℝ) (history : E.History) : ℝ :=
  expect (M.runBehavioralUntil certificate profile stopped history) (cumulativeCharge charge) -
    cumulativeCharge charge history

theorem expectedCharge_bounds {horizon : Nat} (bounded : E.BoundedHorizon horizon)
    (certificate : E.WellFoundedHistories) (profile : ∀ who, M.BehavioralPolicy who)
    (stopped : E.History → Prop) (charge : E.History → ℝ) {bound : ℝ}
    (nonnegative : ∀ history, 0 ≤ charge history)
    (atMost : ∀ history, charge history ≤ bound) (history : E.History) :
    0 ≤ expectedCharge M certificate profile stopped charge history ∧
      expectedCharge M certificate profile stopped charge history ≤ bound * horizon := by
  let law := M.runBehavioralUntil certificate profile stopped history
  have integrable := cumulative_integrable bounded charge nonnegative atMost law
  have lower := expect_mono (μ := law)
    (f := fun _ => cumulativeCharge charge history) (g := cumulativeCharge charge)
    (fun final supported => cumulative_mono charge nonnegative
      (M.runBehavioralUntil_support_prefix certificate profile stopped history final supported))
    (payoffIntegrable_constant law _) integrable
  have upper := expect_le_const law (cumulativeCharge charge) integrable (bound * horizon) (by
    intro final _
    have boundNonnegative := (nonnegative E.initHistory).trans (atMost E.initHistory)
    exact (cumulative_bounds charge nonnegative atMost final).2.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast trace_length_le bounded final)
        boundNonnegative))
  rw [expect_constant] at lower
  have currentNonnegative := (cumulative_bounds charge nonnegative atMost history).1
  change 0 ≤ expect law _ - _ ∧ expect law _ - _ ≤ _
  constructor <;> linarith

theorem expectedCharge_integrable {horizon : Nat} (bounded : E.BoundedHorizon horizon)
    (certificate : E.WellFoundedHistories) (profile : ∀ who, M.BehavioralPolicy who)
    (stopped : E.History → Prop) (charge : E.History → ℝ) {bound : ℝ}
    (nonnegative : ∀ history, 0 ≤ charge history)
    (atMost : ∀ history, charge history ≤ bound) (law : PMF E.History) :
    PayoffIntegrable law (expectedCharge M certificate profile stopped charge) := by
  apply payoffIntegrable_of_bounded law _ (C := bound * horizon)
  intro history
  obtain ⟨lower, upper⟩ := expectedCharge_bounds M bounded certificate profile stopped charge
    nonnegative atMost history
  rwa [abs_of_nonneg lower]

theorem expectedCharge_drift {horizon : Nat} (bounded : E.BoundedHorizon horizon)
    (certificate : E.WellFoundedHistories) (profile : ∀ who, M.BehavioralPolicy who)
    (stopped : E.History → Prop) (charge : E.History → ℝ) {bound : ℝ}
    (nonnegative : ∀ history, 0 ≤ charge history)
    (atMost : ∀ history, charge history ≤ bound) (history : E.History)
    (going : ¬ stopped history) (running : ¬ E.terminal history.state) :
    charge history + expect (M.runBehavioralFrom profile 1 history)
      (expectedCharge M certificate profile stopped charge) =
        expectedCharge M certificate profile stopped charge history := by
  classical
  let total := cumulativeCharge charge
  let law := M.runBehavioralFrom profile 1 history
  let value := fun current => expect
    (M.runBehavioralUntil certificate profile stopped current) total
  have totalIntegrable := cumulative_integrable bounded charge nonnegative atMost
  have valueIntegrable (distribution : PMF E.History) : PayoffIntegrable distribution value := by
    apply payoffIntegrable_of_bounded distribution _ (C := bound * horizon)
    intro current
    apply expect_abs_le_of_bounded (mul_nonneg
      ((nonnegative E.initHistory).trans (atMost E.initHistory)) (Nat.cast_nonneg _))
    intro final
    obtain ⟨lower, upper⟩ := cumulative_bounds charge nonnegative atMost final
    rw [abs_of_nonneg lower]
    exact upper.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast trace_length_le bounded final)
      ((nonnegative E.initHistory).trans (atMost E.initHistory)))
  have tower : value history = expect law value := by
    dsimp only [value]
    rw [M.runBehavioralUntil_of_running certificate profile going running]
    exact expect_bind_tower _ _ _ (totalIntegrable _)
  have increment : ∀ next ∈ law.support, total next = total history + charge history := by
    intro next member
    dsimp only [law] at member
    rw [InformationModel.runBehavioralFrom_succ_of_not_terminal M profile 0 running,
      PMF.mem_support_bind_iff] at member
    obtain ⟨draw, _, realized⟩ := member
    rw [PMF.mem_support_bindOnSupport_iff] at realized
    obtain ⟨target, supported, final⟩ := realized
    change next ∈ (PMF.pure (history.extend draw.2 supported)).support at final
    rw [PMF.mem_support_pure_iff] at final
    subst next
    rfl
  have stepTotal : expect law total = total history + charge history :=
    (expect_congr_on_support increment).trans (expect_constant law _)
  change charge history + expect law (fun next => value next - total next) =
    value history - total history
  rw [expect_sub (valueIntegrable _) (totalIntegrable _), ← tower, stepTotal]
  ring

end GameTheory.Protocol.InformationModel
