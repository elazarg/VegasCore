/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.StateCongruence

/-! # Finite runner laws from one-step invariants -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A terminal clause and one aggregate plan-step equation determine the
readout law of the actual finite runner once fuel covers every unfinished
event. -/
theorem runPlan_map_eq_value_of_step
    {Outcome : Type} (plan : graph.EventPlan)
    (readout : graph.Config → Outcome) (value : graph.Config → PMF Outcome)
    (terminal : ∀ config, config.cut.Terminal →
      PMF.pure (readout config) = value config)
    (step : ∀ config (notTerminal : ¬ config.cut.Terminal),
      ((plan config notTerminal).bind fun choice =>
        (config.step choice.1.1 choice.1.2 choice.2).bind value) = value config) :
    ∀ fuel config, config.remaining ≤ fuel →
      (graph.runPlan plan fuel config).map readout = value config := by
  intro fuel
  induction fuel with
  | zero =>
      intro config enough
      have remainingZero : config.remaining = 0 := by omega
      have isTerminal := (config.terminal_iff_remaining_zero).2 remainingZero
      simpa [runPlan, PMF.pure_map] using terminal config isTerminal
  | succ fuel ih =>
      intro config enough
      by_cases isTerminal : config.cut.Terminal
      · simpa [runPlan, isTerminal, PMF.pure_map] using terminal config isTerminal
      · rw [runPlan, dite_eq_right isTerminal]
        simp only [PMF.map_bind]
        calc
          (plan config isTerminal).bind (fun choice =>
              (config.step choice.1.1 choice.1.2 choice.2).bind fun next =>
                (graph.runPlan plan fuel next).map readout) =
              (plan config isTerminal).bind (fun choice =>
                (config.step choice.1.1 choice.1.2 choice.2).bind value) := by
                apply bind_congr_on_support _
                intro choice _
                apply bind_congr_on_support _
                intro next member
                apply ih next
                have decreased := config.remaining_step choice.1.1 choice.1.2
                  choice.2 next member
                omega
          _ = value config := step config isTerminal

end Vegas.EventGraph
