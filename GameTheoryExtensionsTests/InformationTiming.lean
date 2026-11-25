module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Core.Equilibrium
public import GameTheory.Math.Probability.ExpectationBind
public import GameTheoryExtensions.Math.Probability.Uniform
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

/-! # The same exogenous law with different decision information

A player guesses a fair bit. Before observing it, every randomized decision
pays one half. After observing it, a legal decision kernel achieves one.
The exogenous bit law agrees for every legal policy in both presentations.
This is a decision-information boundary, not an SE preservation obstruction.
-/

noncomputable section

namespace GameTheoryExtensionsTests.InformationTiming

open GameTheory GameTheory.Math.Probability

def fair : PMF Bool := uniformLaw Bool

def reward (outcome : Bool × Bool) : ℝ := if outcome.1 = outcome.2 then 1 else 0

def hiddenDistribution (choice : PMF Bool) : PMF (Bool × Bool) :=
  choice.bind fun action => fair.map fun bit => (bit, action)

def revealedDistribution (policy : Bool → PMF Bool) : PMF (Bool × Bool) :=
  fair.bind fun bit => (policy bit).map fun action => (bit, action)

/-- The hidden decision permits arbitrary randomization, independent of the bit. -/
def hiddenForm : GameForm Unit where
  sig := { Strategy := fun _ => PMF Bool, Outcome := Bool × Bool }
  play profile := hiddenDistribution (profile ())

/-- The revealed decision permits every randomized kernel of the observed bit. -/
def revealedForm : GameForm Unit where
  sig := { Strategy := fun _ => Bool → PMF Bool, Outcome := Bool × Bool }
  play profile := revealedDistribution (profile ())

theorem hidden_bit_distribution (choice : PMF Bool) : (hiddenDistribution choice).map Prod.fst =
    fair := by
  simp only [hiddenDistribution, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_const]
  change fair.map id = fair
  exact PMF.map_id fair

theorem revealed_bit_distribution (policy : Bool → PMF Bool) :
    (revealedDistribution policy).map Prod.fst = fair := by
  simp only [revealedDistribution, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (fair.bind fun bit => (policy bit).map (Function.const Bool bit)) = fair
  simp only [PMF.map_const, PMF.bind_pure]

private theorem fixed_guess_value (action : Bool) :
    expect fair (fun bit => reward (bit, action)) = 1 / 2 := by
  rw [expect_eq_sum]
  cases action <;> norm_num [fair, reward, Fintype.sum_bool,
    toReal_uniformDistribution_apply]

/-- Even randomized hidden policies cannot improve on guessing. -/
theorem hidden_value (profile : Profile hiddenForm.sig) :
    expect (hiddenForm.play profile) reward = 1 / 2 := by
  change expect (hiddenDistribution (profile ())) reward = _
  rw [hiddenDistribution, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  simp only [expect_map, Function.comp_def, fixed_guess_value, expect_constant]

/-- Revealing the bit before the decision admits a policy with value one. -/
theorem revealed_value : expect (revealedForm.play (fun _ => PMF.pure)) reward = 1 := by
  change expect (revealedDistribution PMF.pure) reward = _
  rw [revealedDistribution, expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  simp only [PMF.pure_map, expect_pure, reward, ↓reduceIte, expect_constant]

theorem revealed_value_le_one (profile : Profile revealedForm.sig) :
    expect (revealedForm.play profile) reward ≤ 1 := by
  change expect (revealedDistribution (profile ())) reward ≤ 1
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
  intro outcome _
  unfold reward
  split <;> norm_num

end GameTheoryExtensionsTests.InformationTiming
