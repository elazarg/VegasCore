/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.TerminalObservation
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Lossless laws of the common terminal observation

The typed terminal state and entire payoff vector recover the complete pair.
The fixed reader derives the input and public-result coordinates from that same
terminal state. Recoding loses no event or payoff observable of the pair.
-/

noncomputable section

namespace Vegas.TerminalObservation

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def stateAndPayoffs (observation : TerminalObservation setup) :
    Option (State L setup.program.terminalCtx) × (Player → ℝ) :=
  (observation.terminalState, observation.netPayoffs)

@[simp] theorem stateAndPayoffs_read
    (terminal : Option (State L setup.program.terminalCtx)) (payoffs : Player → ℝ) :
    stateAndPayoffs setup (read setup terminal payoffs) = (terminal, payoffs) := rfl

theorem stateAndPayoffs_leftInverse :
    Function.LeftInverse (stateAndPayoffs setup) (Function.uncurry (read setup)) :=
  fun _ => rfl

theorem read_injective : Function.Injective (Function.uncurry (read setup)) :=
  (stateAndPayoffs_leftInverse setup).injective

theorem map_read_roundtrip
    (law : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ))) :
    (law.map (Function.uncurry (read setup))).map (stateAndPayoffs setup) = law := by
  rw [PMF.map_comp]
  exact PMF.map_id _

theorem map_read_injective :
    Function.Injective (PMF.map (Function.uncurry (read setup))) :=
  pmf_map_injective (read_injective setup)

theorem read_event_probability
    (law : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)))
    (event : Set (Option (State L setup.program.terminalCtx) × (Player → ℝ))) :
    (law.map (Function.uncurry (read setup))).toOuterMeasure
        ((stateAndPayoffs setup) ⁻¹' event) = law.toOuterMeasure event := by
  rw [← PMF.toOuterMeasure_map_apply, map_read_roundtrip]

theorem read_expectation
    (law : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)))
    (observable : Option (State L setup.program.terminalCtx) × (Player → ℝ) → ℝ) :
    expect (law.map (Function.uncurry (read setup)))
      (fun observation => observable (stateAndPayoffs setup observation)) =
        expect law observable := by
  rw [expect_map]
  rfl

theorem read_integrable_iff
    (law : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)))
    (observable : Option (State L setup.program.terminalCtx) × (Player → ℝ) → ℝ) :
    PayoffIntegrable (law.map (Function.uncurry (read setup)))
        (fun observation => observable (stateAndPayoffs setup observation)) ↔
      PayoffIntegrable law observable := by
  rw [payoffIntegrable_map_iff]
  rfl

/-- The common observation has exactly the same total-variation comparisons as
the complete typed-state/payoff pair, with no finite-carrier premise. -/
theorem withinTV_read_iff
    (first second : PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)))
    (error : ℝ) :
    PMF.WithinTV error (first.map (Function.uncurry (read setup)))
        (second.map (Function.uncurry (read setup))) ↔ PMF.WithinTV error first second := by
  constructor
  · intro close
    simpa only [map_read_roundtrip] using close.map (stateAndPayoffs setup)
  · exact fun close => close.map (Function.uncurry (read setup))

end Vegas.TerminalObservation
