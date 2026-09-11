/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.MixtureSimulation

/-! # Strategic transfer for a source-level quit

This file isolates the mechanism-design step used when a runtime has an
additional action that is intended to mean “quit”.  The runtime action is not
identified with a source strategy by its name.  Instead, the caller supplies a
law showing that every source strategy in the deviation mixture is the source
quit.  Under that checked law, any strict source improvement over quit remains
a strict target improvement at the compiled profile.
-/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn

open GameTheory.Math.Probability

universe uι us uo us' uo' uv

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player}
variable {target : GameForm.{uι, us', uo'} Player}
variable {Observation : Type uv}
variable {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)

/-- A runtime quit whose deviation law is supported entirely on the source quit
cannot occur in a compiled Nash equilibrium when a source strategy is strictly
better than that quit at the corresponding source profile.

The premise `hquit` is the precise hiding/equivalence obligation.  It
must be proved by the runtime model; this theorem does not identify arbitrary
malformed, replay, or reaction commands with quitting by fiat. -/
theorem compiled_quit_profile_not_isNash
    (value : Observation → Player → ℝ)
    (profile : Profile source.sig) (who : Player)
    (quit : source.sig.Strategy who)
    (preferred : source.sig.Strategy who)
    (quitTarget : target.sig.Strategy who)
    (hconsidered : Considered who quitTarget)
    (hquit : ∀ alternatives : FinDist (source.sig.Strategy who),
      (target.play (Profile.update (simulation.compileProfile profile) who quitTarget)).map
          targetObserve =
        (alternatives.bind fun alternative =>
          (source.play (Profile.update profile who alternative)).map sourceObserve) →
      ∀ alternative ∈ alternatives.support, alternative = quit)
    (hstrict :
      (source.play (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who) <
        (source.play (Profile.update profile who preferred)).expect
          (fun outcome => value (sourceObserve outcome) who)) :
    ¬ IsNash target
      (euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (simulation.compileProfile profile) who quitTarget) := by
  intro hnash
  obtain ⟨alternatives, hlaw⟩ :=
    simulation.deviation_mixture profile who quitTarget hconsidered
  have halternatives := hquit alternatives hlaw
  have htargetNash :=
    (isNash_iff (F := target) (weaklyPrefers :=
      euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (simulation.compileProfile profile) who quitTarget)).1 hnash
  have hquitLaw := congrArg
      (fun law => law.expect (fun observation => value observation who)) hlaw
  simp only [FinDist.expect_map, FinDist.expect_bind] at hquitLaw
  have hquitSupport : alternatives.expect (fun alternative =>
      (source.play (Profile.update profile who alternative)).expect
        (fun outcome => value (sourceObserve outcome) who)) =
      (source.play (Profile.update profile who quit)).expect
        (fun outcome => value (sourceObserve outcome) who) := by
    rw [← FinDist.expect_const alternatives
      ((source.play (Profile.update profile who quit)).expect
        (fun outcome => value (sourceObserve outcome) who))]
    apply FinDist.expect_congr
    intro alternative halternative
    rw [halternatives alternative halternative]
  have hquitTarget :
      (target.play (Profile.update (simulation.compileProfile profile) who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) =
        (source.play (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who) := by
    exact hquitLaw.trans hquitSupport
  have hpreferredTarget :
      (target.play (Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who preferred))).expect
          (fun outcome => value (targetObserve outcome) who) =
        (source.play (Profile.update profile who preferred)).expect
          (fun outcome => value (sourceObserve outcome) who) := by
    rw [simulation.compileProfile_update profile who preferred]
    exact simulation.expect_compile (Profile.update profile who preferred)
      (fun observation => value observation who)
  have htargetStrict :
      (target.play (Profile.update (simulation.compileProfile profile) who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) <
        (target.play (Profile.update (simulation.compileProfile profile) who
          (simulation.compileStrategy who preferred))).expect
          (fun outcome => value (targetObserve outcome) who) := by
    rw [hquitTarget, hpreferredTarget]
    exact hstrict
  have htargetWeak := htargetNash who (simulation.compileStrategy who preferred)
  rw [Profile.update_idem] at htargetWeak
  rw [euPreference_apply] at htargetWeak
  have htargetWeak' :
      (target.play (Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who preferred))).expect
          (fun outcome => value (targetObserve outcome) who) ≤
        (target.play (Profile.update (simulation.compileProfile profile) who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) := by
    simpa only [expectedUtility] using htargetWeak
  exact (not_lt_of_ge htargetWeak') htargetStrict

/-- The same transfer stated with the standard strict-dominance predicate.
Strict dominance is quantified over all source profiles, so its instance at
the supplied profile discharges the pointwise premise of
`compiled_quit_profile_not_isNash`. -/
theorem compiled_quit_profile_not_isNash_of_strictlyDominates
    (value : Observation → Player → ℝ)
    (profile : Profile source.sig) (who : Player)
    (quit : source.sig.Strategy who)
    (preferred : source.sig.Strategy who)
    (quitTarget : target.sig.Strategy who)
    (hconsidered : Considered who quitTarget)
    (hquit : ∀ alternatives : FinDist (source.sig.Strategy who),
      (target.play (Profile.update (simulation.compileProfile profile) who quitTarget)).map
          targetObserve =
        (alternatives.bind fun alternative =>
          (source.play (Profile.update profile who alternative)).map sourceObserve) →
      ∀ alternative ∈ alternatives.support, alternative = quit)
    (hdom : StrictlyDominates source
      (euPreference (fun outcome player => value (sourceObserve outcome) player)) who
      preferred quit) :
    ¬ IsNash target
      (euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (simulation.compileProfile profile) who quitTarget) := by
  apply simulation.compiled_quit_profile_not_isNash value profile who quit preferred quitTarget
    hconsidered hquit
  exact (euPreference_strict_iff _ _ _ _).1
    (hdom profile (fun _ => Set.mem_univ _))

end GameTheory.GameForm.MixtureSimulationOn

/-- info: 'GameTheory.GameForm.MixtureSimulationOn.compiled_quit_profile_not_isNash'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.MixtureSimulationOn.compiled_quit_profile_not_isNash

/-- info: 'GameTheory.GameForm.MixtureSimulationOn.compiled_quit_profile_not_isNash_of_strictlyDominates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.GameForm.MixtureSimulationOn.compiled_quit_profile_not_isNash_of_strictlyDominates
