/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Core.Mixed

/-! # Ignoring independent public randomization

Every player can condition a mixed action on one exogenous public signal.
At profiles which ignore the signal, averaging any unilateral contingent
alternative gives an ordinary mixed alternative with exactly the same law.
Nash transfer is preference-parametric; no sequential-consistency claim is made.
-/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

variable {Player Signal : Type*} [Fintype Player] [DecidableEq Player]
  (source : GameForm Player) (signal : PMF Signal)

/-- Nature draws one public signal before simultaneous randomized play. -/
def publicRandomization : GameForm Player where
  sig := ⟨(fun who => Signal → PMF (source.sig.Strategy who)), source.sig.Outcome⟩
  play profile := signal.bind fun observed => source.mixed.play (fun who => profile who observed)

/-- A source mixed profile ignores the public signal at every coordinate. -/
def ignorePublicSignal (profile : Profile source.sig.mixed) :
    Profile (source.publicRandomization signal).sig := fun who _ => profile who

omit [DecidableEq Player] in
theorem play_ignorePublicSignal (profile : Profile source.sig.mixed) :
    (source.publicRandomization signal).play (source.ignorePublicSignal signal profile) =
      source.mixed.play profile := by
  change signal.bind (fun _ => source.mixed.play profile) = _
  exact PMF.bind_const signal _

/-- The signal-dependent alternative is legal at every observation. Its
unconditional mixed action realizes the entire unilateral deviation law. -/
theorem play_update_ignorePublicSignal (profile : Profile source.sig.mixed) (who : Player)
    (alternative : Signal → PMF (source.sig.Strategy who)) :
    (source.publicRandomization signal).play
        (Profile.update (source.ignorePublicSignal signal profile) who alternative) =
      source.mixed.play (Profile.update profile who (signal.bind alternative)) := by
  have coordinate (observed : Signal) :
      (fun other => Profile.update (source.ignorePublicSignal signal profile) who alternative
        other observed) = Profile.update profile who (alternative observed) := by
    funext other
    by_cases same : other = who
    · subst other
      simp only [Profile.update_same]
    · simp only [Profile.update_of_ne _ _ same, ignorePublicSignal]
  change signal.bind (fun observed => source.mixed.play
    (fun other => Profile.update (source.ignorePublicSignal signal profile) who alternative
      other observed)) = source.mixed.play (Profile.update profile who (signal.bind alternative))
  simp_rw [coordinate]
  calc
    _ = signal.bind (fun observed => (alternative observed).bind fun action =>
        source.mixed.play (Profile.update profile who (PMF.pure action))) := by
      congr 1
      funext observed
      exact source.mixed_play_update profile who (alternative observed)
    _ = (signal.bind alternative).bind (fun action =>
        source.mixed.play (Profile.update profile who (PMF.pure action))) :=
      (PMF.bind_bind _ _ _).symm
    _ = _ := (source.mixed_play_update profile who (signal.bind alternative)).symm

/-- Every source mixed Nash equilibrium survives independent public information
when the prescribed strategies ignore it. All contingent target alternatives
are covered, and honest outcome laws agree exactly. -/
theorem isNash_ignorePublicSignal_iff (preference : WeakPreference Player source.sig.Outcome)
    (profile : Profile source.sig.mixed) :
    IsNash (source.publicRandomization signal) preference
        (source.ignorePublicSignal signal profile) ↔ IsNash source.mixed preference profile := by
  simp only [isNash_iff, source.play_ignorePublicSignal signal,
    source.play_update_ignorePublicSignal signal]
  constructor
  · intro optimal who alternative
    have compared := optimal who (fun _ => alternative)
    simpa only [PMF.bind_const] using compared
  · intro optimal who alternative
    exact optimal who (signal.bind alternative)

end GameTheory.GameForm
