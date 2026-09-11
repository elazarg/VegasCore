/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.TrustedRoles

/-!
# Externalizing stochastic play to a known mediator

Every game form can be presented as a game with one additional runtime role.
The real players retain their source strategies.  The mediator's strategy is a
complete contingent function from real-player profiles to outcome laws, and
the compiled mediator strategy is exactly `source.form.play`.

This construction proves the classical content of outsourcing sampling and
protocol administration to a player with a known strategy.  A concrete oracle
or batch runtime must still refine this mediator strategy, and a secure
compiler must account for deviations or observations that the construction
intentionally treats as trusted.
-/

noncomputable section

namespace Vegas.Runtime.KnownMediator

open GameTheory
open GameTheory.Math.Probability

universe uPlayer uStrategy uOutcome

/-- Runtime roles consist of the strategic source players and one trusted
mediator. -/
inductive Role (Player : Type uPlayer) : Type uPlayer where
  | real (who : Player)
  | mediator
deriving DecidableEq

variable {Player : Type uPlayer} [DecidableEq Player]
variable (source : UtilityGame.{uPlayer, uStrategy, uOutcome} Player)

/-- Target strategies for real players are unchanged.  The mediator supplies a
complete outcome-law policy contingent on the whole real-player profile. -/
@[reducible] def signature :
    GameSignature.{uPlayer, max uPlayer uStrategy uOutcome, uOutcome}
      (Role Player) where
  Strategy
    | .real who =>
        ULift.{max uPlayer uStrategy uOutcome}
          (source.form.sig.Strategy who)
    | .mediator => Profile source.form.sig → FinDist source.form.sig.Outcome
  Outcome := source.form.sig.Outcome

/-- Extract the source-player coordinates of a mediator-game profile. -/
def realProfile (profile : Profile (signature source)) :
    Profile source.form.sig :=
  fun who => (profile (.real who)).down

/-- The target form asks the mediator strategy for the law associated with the
current real-player profile. -/
@[reducible] def form : GameForm (Role Player) where
  sig := signature source
  play := fun profile => profile .mediator (realProfile source profile)

/-- Real roles retain source utility. The trusted mediator has zero utility;
its behavior is fixed by assumption rather than equilibrium incentives. -/
def utility (outcome : source.form.sig.Outcome) : Role Player → ℝ
  | .real who => source.utility outcome who
  | .mediator => 0

/-- Utility game of the externalized known-mediator presentation. -/
@[reducible] def game : UtilityGame (Role Player) where
  form := form source
  utility := utility source

/-- Compile a source profile by retaining every real strategy and fixing the
mediator to the source form's complete stochastic play function. -/
def compileProfile (profile : Profile source.form.sig) :
    Profile (signature source) :=
  fun role =>
    match role with
    | .real who => ULift.up (profile who)
    | .mediator => source.form.play

omit [DecidableEq Player] in
@[simp] theorem compileProfile_real
    (profile : Profile source.form.sig) (who : Player) :
    compileProfile source profile (.real who) = ULift.up (profile who) :=
  rfl

omit [DecidableEq Player] in
@[simp] theorem compileProfile_mediator
    (profile : Profile source.form.sig) :
    compileProfile source profile .mediator = source.form.play :=
  rfl

omit [DecidableEq Player] in
@[simp] theorem realProfile_compileProfile
    (profile : Profile source.form.sig) :
    realProfile source (compileProfile source profile) = profile := by
  rfl

/-- Exact trusted-role adequacy of the known-mediator externalization. -/
def adequacy : TrustedRoleAdequacy source (game source) where
  embed := Role.real
  embed_injective := by
    intro first second heq
    cases heq
    rfl
  compileStrategy := fun _who strategy => ULift.up strategy
  compileProfile := compileProfile source
  compileProfile_real := fun _profile _who => rfl
  trusted_fixed := by
    intro left right role htrusted
    cases role with
    | real who => exact False.elim (htrusted ⟨who, rfl⟩)
    | mediator => rfl
  backtranslateStrategy := fun _profile _who strategy => strategy.down
  backtranslate_compile := fun _profile _who _replacement => rfl
  decodeOutcome := id
  utility_eq := fun _outcome _who => rfl
  honest_law := by
    intro profile
    simp [game, form, compileProfile]
  deviation_law := by
    intro profile who replacement
    change
      ((Profile.update (compileProfile source profile) (.real who)
          replacement) .mediator
        (realProfile source
          (Profile.update (compileProfile source profile) (.real who)
            replacement))).map id =
        source.form.play (Profile.update profile who replacement.down)
    have hmediator :
        Profile.update (compileProfile source profile) (.real who) replacement
            .mediator = source.form.play := by
      rw [Profile.update_of_ne]
      · rfl
      · intro heq
        cases heq
    have hreal :
        realProfile source
            (Profile.update (compileProfile source profile) (.real who)
              replacement) =
          Profile.update profile who replacement.down := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [realProfile]
      · simp [realProfile, Profile.update_of_ne, hplayer]
    rw [hmediator, hreal, FinDist.map_id]

/-- The classical mediator presentation has exactly the source Nash profiles
when deviations are quantified over real players and the mediator remains
fixed. -/
theorem isNashForReal_iff (profile : Profile source.form.sig) :
    (adequacy source).IsNashForReal (compileProfile source profile) ↔
      IsNash source.form (euPreference source.utility) profile :=
  (adequacy source).isNashForReal_compileProfile_iff profile

end Vegas.Runtime.KnownMediator
