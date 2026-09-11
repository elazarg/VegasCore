/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Core.Utility

/-!
# Adequacy with fixed trusted runtime roles

A classical runtime may add protocol participants that are not strategic source
players: a sampling oracle, an atomic batch mediator, or a fair scheduler.  Such
a participant is modeled as an ordinary target-game player whose strategy is
fixed by `compileProfile`.  Equilibrium quantification is then restricted to
the injectively embedded source players.

This is the precise classical reading of "sampling is a player with a known
strategy."  It neither proves that the trusted participant follows that
strategy nor protects against target-only observations, coalitions, aborts, or
timing attacks.  A secure compiler must replace or strengthen these premises.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory
open GameTheory.Math.Probability

universe uSourcePlayer uTargetPlayer
universe uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

/-- Exact unilateral-deviation adequacy for real source players when the target
game also contains fixed trusted roles. -/
structure TrustedRoleAdequacy
    {SourcePlayer : Type uSourcePlayer} [DecidableEq SourcePlayer]
    {TargetPlayer : Type uTargetPlayer} [DecidableEq TargetPlayer]
    (source : UtilityGame.{uSourcePlayer, uSourceStrategy, uSourceOutcome}
      SourcePlayer)
    (target : UtilityGame.{uTargetPlayer, uTargetStrategy, uTargetOutcome}
      TargetPlayer) where
  /-- Runtime identity of each strategic source player. -/
  embed : SourcePlayer → TargetPlayer
  embed_injective : Function.Injective embed
  /-- Runtime strategy generated for a source-player strategy. -/
  compileStrategy :
    (who : SourcePlayer) → source.form.sig.Strategy who →
      target.form.sig.Strategy (embed who)
  /-- Complete target profile. Coordinates outside `embed` are the known
  oracle, batcher, and scheduler strategies. -/
  compileProfile : Profile source.form.sig → Profile target.form.sig
  compileProfile_real :
    ∀ profile who,
      compileProfile profile (embed who) = compileStrategy who (profile who)
  /-- Trusted-role coordinates do not vary with the source strategy profile. -/
  trusted_fixed :
    ∀ left right role,
      (¬ ∃ who, embed who = role) →
        compileProfile left role = compileProfile right role
  /-- Back-translation of an arbitrary real-player runtime deviation. -/
  backtranslateStrategy :
    (profile : Profile source.form.sig) →
      (who : SourcePlayer) →
        target.form.sig.Strategy (embed who) →
          source.form.sig.Strategy who
  backtranslate_compile :
    ∀ profile who replacement,
      backtranslateStrategy profile who (compileStrategy who replacement) =
        replacement
  decodeOutcome : target.form.sig.Outcome → source.form.sig.Outcome
  utility_eq :
    ∀ outcome who,
      target.utility outcome (embed who) =
        source.utility (decodeOutcome outcome) who
  honest_law :
    ∀ profile,
      (target.form.play (compileProfile profile)).map decodeOutcome =
        source.form.play profile
  deviation_law :
    ∀ profile who replacement,
      (target.form.play
        (Profile.update (compileProfile profile) (embed who)
          replacement)).map decodeOutcome =
        source.form.play
          (Profile.update profile who
            (backtranslateStrategy profile who replacement))

namespace TrustedRoleAdequacy

variable {SourcePlayer : Type uSourcePlayer} [DecidableEq SourcePlayer]
variable {TargetPlayer : Type uTargetPlayer} [DecidableEq TargetPlayer]
variable
  {source : UtilityGame.{uSourcePlayer, uSourceStrategy, uSourceOutcome}
    SourcePlayer}
variable
  {target : UtilityGame.{uTargetPlayer, uTargetStrategy, uTargetOutcome}
    TargetPlayer}
variable (adequacy : TrustedRoleAdequacy source target)

/-- Nash against deviations by embedded source players only. Trusted runtime
roles remain at their fixed compiled strategies and are not equilibrium
claimants. -/
def IsNashForReal (profile : Profile target.form.sig) : Prop :=
  ∀ who replacement,
    euPreference target.utility (adequacy.embed who)
      (target.form.play profile)
      (target.form.play
        (Profile.update profile (adequacy.embed who) replacement))

/-- Pulling a target outcome law back through the semantic decoder preserves
the expected utility of every embedded real player. -/
theorem expectedUtility_eq_decoded
    (law : FinDist target.form.sig.Outcome) (who : SourcePlayer) :
    expectedUtility target.utility (adequacy.embed who) law =
      expectedUtility source.utility who
        (law.map adequacy.decodeOutcome) := by
  unfold expectedUtility
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro outcome _supported
  exact adequacy.utility_eq outcome who

/-- Honest execution with all trusted roles fixed has exactly the source
expected utility for every real player. -/
theorem expectedUtility_compileProfile
    (profile : Profile source.form.sig) (who : SourcePlayer) :
    expectedUtility target.utility (adequacy.embed who)
        (target.form.play (adequacy.compileProfile profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  rw [adequacy.expectedUtility_eq_decoded, adequacy.honest_law]

/-- Every real-player target deviation has exactly the expected utility of its
source back-translation while trusted roles remain fixed. -/
theorem expectedUtility_deviation
    (profile : Profile source.form.sig) (who : SourcePlayer)
    (replacement : target.form.sig.Strategy (adequacy.embed who)) :
    expectedUtility target.utility (adequacy.embed who)
        (target.form.play
          (Profile.update (adequacy.compileProfile profile)
            (adequacy.embed who) replacement)) =
      expectedUtility source.utility who
        (source.form.play
          (Profile.update profile who
            (adequacy.backtranslateStrategy profile who replacement))) := by
  rw [adequacy.expectedUtility_eq_decoded, adequacy.deviation_law]

/-- The trusted-role certificate preserves and reflects Nash for precisely the
strategic players inherited from the source game. -/
theorem isNashForReal_compileProfile_iff
    (profile : Profile source.form.sig) :
    adequacy.IsNashForReal (adequacy.compileProfile profile) ↔
      IsNash source.form (euPreference source.utility) profile := by
  rw [GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    have htarget := h who (adequacy.compileStrategy who replacement)
    rw [euPreference_apply] at htarget ⊢
    rw [adequacy.expectedUtility_deviation,
      adequacy.backtranslate_compile,
      adequacy.expectedUtility_compileProfile] at htarget
    exact htarget
  · intro h who replacement
    have hsource :=
      h who (adequacy.backtranslateStrategy profile who replacement)
    rw [euPreference_apply] at hsource ⊢
    rw [adequacy.expectedUtility_deviation,
      adequacy.expectedUtility_compileProfile]
    exact hsource

end TrustedRoleAdequacy

end Vegas.Runtime
