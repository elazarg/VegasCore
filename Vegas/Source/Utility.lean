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
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- Public default status fixes an owner's utility, irrespective of the
remaining typed values and public history. -/
def exclusionUtility {Parameter : Type} (program : SourceProgram Player L Γ O)
    (excludedPayoff : Player → ℝ)
    (utility : Parameter × PublicOutcome program → Player → ℝ) :
    Parameter × PublicOutcome program → Player → ℝ :=
  fun outcome who =>
    if who ∈ outcome.2.defaulted then excludedPayoff who else utility outcome who

/-- Public default replaces the ordinary utility by its declared exit value. -/
theorem exclusionUtility_of_defaulted {Parameter : Type}
    (program : SourceProgram Player L Γ O) (excludedPayoff : Player → ℝ)
    (utility : Parameter × PublicOutcome program → Player → ℝ)
    {outcome : Parameter × PublicOutcome program} {who : Player}
    (defaulted : who ∈ outcome.2.defaulted) :
    exclusionUtility program excludedPayoff utility outcome who = excludedPayoff who := by
  simp only [exclusionUtility, defaulted, ite_true]

/-- A player that has not defaulted retains the ordinary utility of the full public result. -/
theorem exclusionUtility_of_not_defaulted {Parameter : Type}
    (program : SourceProgram Player L Γ O) (excludedPayoff : Player → ℝ)
    (utility : Parameter × PublicOutcome program → Player → ℝ)
    {outcome : Parameter × PublicOutcome program} {who : Player}
    (active : who ∉ outcome.2.defaulted) :
    exclusionUtility program excludedPayoff utility outcome who = utility outcome who := by
  simp only [exclusionUtility, active, ite_false]

/-- Every continuation preserves the declared exit utility under the canonical
public-outcome utility, with no bound or finiteness condition on the ordinary utility. -/
theorem runFrom_exclusionUtility_of_defaulted {Parameter : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (excludedPayoff : Player → ℝ)
    (utility : Parameter × PublicOutcome program → Player → ℝ)
    (parameter : State L program.terminalCtx × DefaultHistory Player → Parameter)
    (who : Player) (defaulted : who ∈ config.defaulted) :
    PayoffIntegrable (runFrom program profile config)
        (fun final => exclusionUtility program excludedPayoff utility
          (parameter (final.state, final.defaults), publicOutcome program final) who) ∧
      expect (runFrom program profile config)
        (fun final => exclusionUtility program excludedPayoff utility
          (parameter (final.state, final.defaults), publicOutcome program final) who) =
          excludedPayoff who := by
  have same (final) (reached : final ∈ (runFrom program profile config).support) :
      exclusionUtility program excludedPayoff utility
        (parameter (final.state, final.defaults), publicOutcome program final) who =
        excludedPayoff who :=
    exclusionUtility_of_defaulted program excludedPayoff utility
      ((runFrom_defaulted_mono program profile config final reached) defaulted)
  refine ⟨payoffIntegrable_congr_on_support (fun final reached => (same final reached).symm)
    (payoffIntegrable_constant _ _), ?_⟩
  exact (expect_congr_on_support same).trans (expect_constant _ _)

end Vegas.SourceProgram
