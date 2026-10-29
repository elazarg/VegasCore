/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Semantics
import GameTheory.Math.Probability.Expectation

/-! # Fixed source utility after public default

Exit utility is a rule of the game, rather than a hypothesis on an arbitrary
valuation. A defaulted owner receives its declared exit value under every
continuation; the ordinary utility reads typed cells and the public default history.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L}

/-- A defaulted owner's declared utility overrides the ordinary terminal-cell valuation. -/
def Config.utility (config : Config Player L Γ)
    (ordinary : State L Γ × DefaultHistory Player → Player → ℝ)
    (exitUtility : Player → ℝ) (who : Player) : ℝ :=
  if who ∈ config.defaulted then exitUtility who else ordinary (config.state, config.defaults) who

omit [IExpr.ResultTypes L] in
/-- No subsequent typed outcome changes a defaulted owner's base utility. -/
theorem Config.utility_of_defaulted (config : Config Player L Γ)
    (ordinary : State L Γ × DefaultHistory Player → Player → ℝ)
    (exitUtility : Player → ℝ) (who : Player)
    (defaulted : who ∈ config.defaulted) :
    config.utility ordinary exitUtility who = exitUtility who := by
  simp only [Config.utility, defaulted, ite_true]

/-- Every continuation of every profile has integrable, fixed utility for an
already defaulted player. No finiteness or bound on the ordinary utility is needed. -/
theorem runFrom_utility_of_defaulted {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ)
    (ordinary : State L program.terminalCtx × DefaultHistory Player → Player → ℝ)
    (exitUtility : Player → ℝ) (who : Player) (defaulted : who ∈ config.defaulted) :
    PayoffIntegrable (runFrom program profile config)
        (fun final => final.utility ordinary exitUtility who) ∧
      expect (runFrom program profile config)
        (fun final => final.utility ordinary exitUtility who) = exitUtility who := by
  have same (final) (reached : final ∈ (runFrom program profile config).support) :
      final.utility ordinary exitUtility who = exitUtility who :=
    final.utility_of_defaulted ordinary exitUtility who
      ((runFrom_defaulted_mono program profile config final reached) defaulted)
  refine ⟨payoffIntegrable_congr_on_support (fun final reached => (same final reached).symm)
    (payoffIntegrable_constant _ _), ?_⟩
  exact (expect_congr_on_support same).trans (expect_constant _ _)

end Vegas.SourceProgram
