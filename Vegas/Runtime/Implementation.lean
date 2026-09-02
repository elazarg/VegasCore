/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy

/-!
# Same-strategy runtime adequacy

A runtime implements a game on an unchanged strategy surface when, for every
source strategy profile, decoding its finite trace law gives exactly the game's
outcome law. This is suitable only after gradual lowering has discharged every
new scheduler, observation, timing, and adversarial choice. It is not a secure
compilation criterion for a pass that introduces new target strategies.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory
open GameTheory.Math.Probability

universe uPlayer uStrategy uOutcome uTrace

/-- A profile-indexed runtime trace law with an exact semantic decoder. -/
structure Implementation {Player : Type uPlayer}
    (G : UtilityGame.{uPlayer, uStrategy, uOutcome} Player) where
  Trace : Type uTrace
  run : Profile G.form.sig → FinDist Trace
  outcome : Trace → G.form.sig.Outcome
  law_eq : ∀ profile, (run profile).map outcome = G.form.play profile

namespace Implementation

variable {Player : Type uPlayer}
variable {G : UtilityGame.{uPlayer, uStrategy, uOutcome} Player}
variable (runtime : Implementation.{uPlayer, uStrategy, uOutcome, uTrace} G)

/-- The runtime viewed as a game form over its concrete traces. -/
@[reducible]
def form : GameForm Player where
  sig := G.form.sig.mapOutcome runtime.Trace
  play := runtime.run

/-- Semantic utility pulled back to concrete runtime traces. -/
def utility (trace : runtime.Trace) (who : Player) : ℝ :=
  G.utility (runtime.outcome trace) who

/-- The utility game exposed by the concrete trace runner. -/
def game : UtilityGame Player where
  form := runtime.form
  utility := runtime.utility

/-- Exact adequacy over an unchanged strategy carrier supplies unilateral
deviation adequacy automatically: every target replacement is already a source
replacement. -/
def deviationAdequacy [DecidableEq Player] :
    DeviationAdequacy G runtime.game where
  compileStrategy := fun _ strategy => strategy
  backtranslateStrategy := fun _ strategy => strategy
  decodeOutcome := runtime.outcome
  utility_eq := rfl
  honest_law := runtime.law_eq
  compiled_considered := fun _ _ => trivial
  deviation_law := fun profile who replacement _ =>
    runtime.law_eq (Profile.update profile who replacement)

/-- Exact decoded trace laws preserve expected utility for every profile. -/
theorem expectedUtility_eq (profile : Profile G.form.sig) (who : Player) :
    expectedUtility G.utility who (G.form.play profile) =
      expectedUtility runtime.utility who (runtime.run profile) := by
  rw [← runtime.law_eq profile, expectedUtility_map]
  rfl

/-- Consequently the runtime and specification have exactly the same
Nash profiles. The proof covers unilateral deviations because `law_eq` ranges
over every profile, including every updated one. -/
theorem isNash_iff [DecidableEq Player] (profile : Profile G.form.sig) :
    IsNash G.form (euPreference G.utility) profile ↔
      IsNash runtime.form (euPreference runtime.utility) profile := by
  rw [GameTheory.isNash_iff, GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    have hspec := h who replacement
    rw [euPreference_apply] at hspec ⊢
    calc
      expectedUtility runtime.utility who
          (runtime.run (Profile.update profile who replacement)) =
          expectedUtility G.utility who
            (G.form.play (Profile.update profile who replacement)) :=
        (runtime.expectedUtility_eq _ who).symm
      _ ≤ expectedUtility G.utility who (G.form.play profile) := hspec
      _ = expectedUtility runtime.utility who (runtime.run profile) :=
        runtime.expectedUtility_eq profile who
  · intro h who replacement
    have hruntime := h who replacement
    rw [euPreference_apply] at hruntime ⊢
    calc
      expectedUtility G.utility who
          (G.form.play (Profile.update profile who replacement)) =
          expectedUtility runtime.utility who
            (runtime.run (Profile.update profile who replacement)) :=
        runtime.expectedUtility_eq _ who
      _ ≤ expectedUtility runtime.utility who (runtime.run profile) := hruntime
      _ = expectedUtility G.utility who (G.form.play profile) :=
        (runtime.expectedUtility_eq profile who).symm

end Implementation

end Vegas.Runtime
