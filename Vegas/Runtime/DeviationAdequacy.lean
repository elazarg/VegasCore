/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Utility

/-!
# Unilateral-deviation adequacy

Exact honest-run outcome equality is not enough when compilation introduces new
strategies.  `DeviationAdequacy` adds the narrow back-translation obligation
needed for Nash preservation: every unilateral target replacement at a
compiled profile must have a source replacement with the same decoded outcome
law.

This is one deliberately small strategic certificate, not a claim to solve
secure compilation in general.  It does not cover coalitions, target context
composition, scheduler hyperproperties, timing, or liveness.  A lowering pass
that introduces one of those surfaces needs a stronger pass-specific theorem.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory
open GameTheory.Math.Probability

universe uPlayer uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

/-- A target game is adequate for source unilateral deviations at compiled
profiles. -/
structure DeviationAdequacy
    {Player : Type uPlayer} [DecidableEq Player]
    (source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player)
    (target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player) where
  compileStrategy :
    (who : Player) → source.form.sig.Strategy who →
      target.form.sig.Strategy who
  backtranslateStrategy :
    (who : Player) → target.form.sig.Strategy who →
      source.form.sig.Strategy who
  decodeOutcome : target.form.sig.Outcome → source.form.sig.Outcome
  utility_eq :
    target.utility =
      fun outcome who => source.utility (decodeOutcome outcome) who
  honest_law :
    ∀ profile,
      (target.form.play
        (fun who => compileStrategy who (profile who))).map decodeOutcome =
          source.form.play profile
  deviation_law :
    ∀ profile who replacement,
      (target.form.play
        (Profile.update
          (fun player => compileStrategy player (profile player))
          who replacement)).map decodeOutcome =
        source.form.play
          (Profile.update profile who
            (backtranslateStrategy who replacement))

namespace DeviationAdequacy

variable {Player : Type uPlayer}
variable [DecidableEq Player]
variable {source : UtilityGame.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
variable {target : UtilityGame.{uPlayer, uTargetStrategy, uTargetOutcome} Player}
variable (adequacy : DeviationAdequacy source target)

/-- Compile every coordinate of a source profile. -/
def compileProfile (profile : Profile source.form.sig) :
    Profile target.form.sig :=
  fun who => adequacy.compileStrategy who (profile who)

@[simp] theorem compileProfile_apply
    (profile : Profile source.form.sig) (who : Player) :
    adequacy.compileProfile profile who =
      adequacy.compileStrategy who (profile who) :=
  rfl

theorem compileProfile_update
    (profile : Profile source.form.sig) (who : Player)
    (replacement : source.form.sig.Strategy who) :
    Profile.update (adequacy.compileProfile profile) who
        (adequacy.compileStrategy who replacement) =
      adequacy.compileProfile (Profile.update profile who replacement) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp
  · simp [Profile.update_of_ne, hplayer]

/-- Honest compiled profiles have exactly the source expected utility. -/
theorem expectedUtility_compileProfile
    (profile : Profile source.form.sig) (who : Player) :
    expectedUtility target.utility who
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  calc
    expectedUtility target.utility who
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility
        (fun outcome who => source.utility (adequacy.decodeOutcome outcome) who)
        who (target.form.play (adequacy.compileProfile profile)) := by
          rw [adequacy.utility_eq]
    _ = expectedUtility source.utility who
        ((target.form.play (adequacy.compileProfile profile)).map
          adequacy.decodeOutcome) := by
          rw [expectedUtility_map]
    _ = expectedUtility source.utility who (source.form.play profile) := by
          change
            expectedUtility source.utility who
                ((target.form.play
                  (fun player => adequacy.compileStrategy player (profile player))).map
                    adequacy.decodeOutcome) =
              expectedUtility source.utility who (source.form.play profile)
          rw [adequacy.honest_law]

/-- Every unilateral target deviation at a compiled profile has the expected
utility of its source back-translation. -/
theorem expectedUtility_deviation
    (profile : Profile source.form.sig) (who : Player)
    (replacement : target.form.sig.Strategy who) :
    expectedUtility target.utility who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) =
      expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy who replacement))) := by
  calc
    expectedUtility target.utility who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) =
      expectedUtility
        (fun outcome who => source.utility (adequacy.decodeOutcome outcome) who)
        who
        (target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)) := by
            rw [adequacy.utility_eq]
    _ = expectedUtility source.utility who
        ((target.form.play
          (Profile.update (adequacy.compileProfile profile) who replacement)).map
            adequacy.decodeOutcome) := by
            rw [expectedUtility_map]
    _ = expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy who replacement))) := by
            change
              expectedUtility source.utility who
                  ((target.form.play
                    (Profile.update
                      (fun player => adequacy.compileStrategy player (profile player))
                      who replacement)).map adequacy.decodeOutcome) =
                expectedUtility source.utility who
                  (source.form.play
                    (Profile.update profile who
                      (adequacy.backtranslateStrategy who replacement)))
            rw [adequacy.deviation_law]

/-- The certificate is exactly strong enough to preserve and reflect Nash
at compiled profiles. -/
theorem isNash_compileProfile_iff
    (profile : Profile source.form.sig) :
    IsNash target.form (euPreference target.utility)
        (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile := by
  rw [GameTheory.isNash_iff, GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    have htarget := h who (adequacy.compileStrategy who replacement)
    rw [euPreference_apply] at htarget ⊢
    rw [adequacy.compileProfile_update] at htarget
    rw [adequacy.expectedUtility_compileProfile,
      adequacy.expectedUtility_compileProfile] at htarget
    exact htarget
  · intro h who replacement
    have hsource := h who (adequacy.backtranslateStrategy who replacement)
    rw [euPreference_apply] at hsource ⊢
    rw [adequacy.expectedUtility_deviation,
      adequacy.expectedUtility_compileProfile]
    exact hsource

end DeviationAdequacy

end Vegas.Runtime
