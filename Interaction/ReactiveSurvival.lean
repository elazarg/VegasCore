/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Interaction.ReactiveStopping
import GameTheoryExtensions.Math.Probability.Survival

/-! # Conditional survival through a bounded reactive execution

The survival event can record that every attempted admission has failed so
far. A pointwise conditional floor for each scheduler round gives a whole-run
lower bound even when scheduler and player policies adapt to their recall.
The physical-round count and the conditional floor are backend obligations;
neither is inferred from the source program's logical horizon.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- The existing round evaluator equals iteration of its full-history kernel. -/
theorem runRounds_eq_iterate (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) :
    app.runRounds scheduler players count execution =
      (fun law : PMF app.Execution => law.bind (app.round scheduler players))^[count]
        (PMF.pure execution) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [app.runRounds_add scheduler players count 1 execution]
      simp only [runRounds, PMF.bind_pure]
      rw [induction, Function.iterate_succ_apply']

/-- From any state inside an event, a conditional floor at every compatible
execution bounds survival through finitely many adaptive scheduler rounds. -/
theorem runRounds_eventProbability_ge_pow (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (event : Set app.Execution) (floor : ℝ)
    (nonnegative : 0 ≤ floor)
    (survival : ∀ execution ∈ event,
      floor ≤ ((app.round scheduler players execution).toOuterMeasure event).toReal)
    (count : Nat) (execution : app.Execution) (initial : execution ∈ event) :
    floor ^ count ≤
      ((app.runRounds scheduler players count execution).toOuterMeasure event).toReal := by
  rw [app.runRounds_eq_iterate]
  simpa only [PMF.toOuterMeasure_pure_apply, initial, ite_true, ENNReal.toReal_one,
    mul_one] using
    eventProbability_iterate_ge_pow (PMF.pure execution) (app.round scheduler players)
      event floor nonnegative survival count

/-- A positive conditional floor remains positive at every finite physical
horizon. This assumes no independence between rounds. -/
theorem runRounds_eventProbability_pos (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (event : Set app.Execution) (floor : ℝ)
    (positive : 0 < floor)
    (survival : ∀ execution ∈ event,
      floor ≤ ((app.round scheduler players execution).toOuterMeasure event).toReal)
    (count : Nat) (execution : app.Execution) (initial : execution ∈ event) :
    0 < ((app.runRounds scheduler players count execution).toOuterMeasure event).toReal :=
  (pow_pos positive count).trans_le
    (app.runRounds_eventProbability_ge_pow scheduler players event floor positive.le
      survival count execution initial)

/-- The same floor bounds an execution that stops adaptively within its
physical-round budget. Stopped states remain inside the event with certainty. -/
theorem runUntil_eventProbability_ge_pow (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (event : Set app.Execution) (floor : ℝ) (nonnegative : 0 ≤ floor) (atMostOne : floor ≤ 1)
    (survival : ∀ execution ∈ event, ¬ stop execution →
      floor ≤ ((app.round scheduler players execution).toOuterMeasure event).toReal)
    (count : Nat) (execution : app.Execution) (initial : execution ∈ event) :
    floor ^ count ≤
      ((app.runUntil scheduler players stop count execution).toOuterMeasure event).toReal := by
  induction count generalizing execution with
  | zero => simp only [runUntil, PMF.toOuterMeasure_pure_apply, initial, ite_true,
      ENNReal.toReal_one, pow_zero, le_refl]
  | succ count induction =>
      by_cases stopped : stop execution
      · rw [app.runUntil_of_stop scheduler players stop _ execution stopped]
        simpa only [PMF.toOuterMeasure_pure_apply, initial, ite_true, ENNReal.toReal_one]
          using pow_le_one₀ nonnegative atMostOne
      · simp only [runUntil, stopped, ite_false, pow_succ]
        calc
          floor ^ count * floor ≤ floor ^ count *
              ((app.round scheduler players execution).toOuterMeasure event).toReal :=
            mul_le_mul_of_nonneg_left (survival execution initial stopped)
              (pow_nonneg nonnegative count)
          _ ≤ _ := eventProbability_bind_ge (app.round scheduler players execution)
            (app.runUntil scheduler players stop count) event (floor ^ count)
            (fun next member => induction next member)

/-- A positive conditional floor survives any bounded adaptive stopping rule. -/
theorem runUntil_eventProbability_pos (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (event : Set app.Execution) (floor : ℝ) (positive : 0 < floor) (atMostOne : floor ≤ 1)
    (survival : ∀ execution ∈ event, ¬ stop execution →
      floor ≤ ((app.round scheduler players execution).toOuterMeasure event).toReal)
    (count : Nat) (execution : app.Execution) (initial : execution ∈ event) :
    0 < ((app.runUntil scheduler players stop count execution).toOuterMeasure event).toReal :=
  (pow_pos positive count).trans_le
    (app.runUntil_eventProbability_ge_pow scheduler players stop event floor positive.le
      atMostOne survival count execution initial)

end Interaction.ReactiveApplication
