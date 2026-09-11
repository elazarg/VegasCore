/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.Approximate

/-! # Game-form simulation by finite mixtures of unilateral deviations -/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uι us uo us' uo' uv

/-- Exact common-observation laws, with each target deviation represented by
a finite mixture of legal unilateral source deviations. -/
structure MixtureSimulationOn {Player : Type uι} [DecidableEq Player]
    (source : GameForm.{uι, us, uo} Player) (target : GameForm.{uι, us', uo'} Player)
    {Observation : Type uv} (sourceObserve : source.sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop) where
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  honest_law : ∀ profile,
    (target.play (fun who => compileStrategy who (profile who))).map targetObserve =
      (source.play profile).map sourceObserve
  compiled_considered : ∀ who strategy, Considered who (compileStrategy who strategy)
  deviation_mixture : ∀ profile who replacement, Considered who replacement →
    ∃ alternatives : FinDist (source.sig.Strategy who),
      (target.play (Profile.update (fun player => compileStrategy player (profile player))
        who replacement)).map targetObserve =
      alternatives.bind fun alternative =>
        (source.play (Profile.update profile who alternative)).map sourceObserve

namespace MixtureSimulationOn

variable {Player : Type uι} [DecidableEq Player]
variable {source : GameForm.{uι, us, uo} Player} {target : GameForm.{uι, us', uo'} Player}
variable {Observation : Type uv} {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)

def compileProfile (profile : Profile source.sig) : Profile target.sig :=
  fun who => simulation.compileStrategy who (profile who)

@[simp] theorem compileProfile_apply (profile : Profile source.sig) (who : Player) :
    simulation.compileProfile profile who = simulation.compileStrategy who (profile who) := rfl

theorem compileProfile_update (profile : Profile source.sig) (who : Player)
    (replacement : source.sig.Strategy who) :
    Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who replacement) =
      simulation.compileProfile (Profile.update profile who replacement) := by
  funext actor
  by_cases h : actor = who
  · subst actor; simp
  · simp [Profile.update_of_ne, h]

theorem expect_compile (profile : Profile source.sig) (value : Observation → ℝ) :
    (target.play (simulation.compileProfile profile)).expect
        (fun outcome => value (targetObserve outcome)) =
      (source.play profile).expect (fun outcome => value (sourceObserve outcome)) := by
  change
    (target.play (fun who => simulation.compileStrategy who (profile who))).expect
        (fun outcome => value (targetObserve outcome)) =
      (source.play profile).expect (fun outcome => value (sourceObserve outcome))
  have hlaw := congrArg (fun law => law.expect value) (simulation.honest_law profile)
  simpa only [FinDist.expect_map] using hlaw

theorem guarantee (profile : Profile source.sig) (who : Player)
    (value : Observation → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : source.sig.Strategy who,
      bound ≤ (source.play (Profile.update profile who alternative)).expect
        (value ∘ sourceObserve))
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement) :
    bound ≤ (target.play
      (Profile.update (simulation.compileProfile profile) who replacement)).expect
        (value ∘ targetObserve) := by
  obtain ⟨alternatives, hlaw⟩ :=
    simulation.deviation_mixture profile who replacement hconsidered
  have hexpect := congrArg (fun law => law.expect value) hlaw
  simp only [FinDist.expect_map, FinDist.expect_bind] at hexpect
  change bound ≤
    (target.play (Profile.update
      (fun player => simulation.compileStrategy player (profile player)) who replacement)).expect
      (fun outcome => value (targetObserve outcome))
  rw [hexpect]
  calc
    bound = alternatives.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => by
      simpa only [Function.comp_def] using hbound alternative

theorem considered_deviations_iff_isεNash (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig) :
    (∀ who replacement, Considered who replacement →
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
          (fun outcome => value (targetObserve outcome) who) ≤
        (target.play (simulation.compileProfile profile)).expect
          (fun outcome => value (targetObserve outcome) who) + ε) ↔
      IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  rw [GameTheory.isεNash_iff]
  constructor
  · intro h who alternative
    have hdev := h who (simulation.compileStrategy who alternative)
      (simulation.compiled_considered who alternative)
    rw [simulation.compileProfile_update] at hdev
    change
      (target.play (simulation.compileProfile (Profile.update profile who alternative))).expect
          (fun outcome => value (targetObserve outcome) who) ≤
        (target.play (simulation.compileProfile profile)).expect
          (fun outcome => value (targetObserve outcome) who) + ε at hdev
    rw [
      simulation.expect_compile (Profile.update profile who alternative)
        (fun observation => value observation who),
      simulation.expect_compile profile (fun observation => value observation who)] at hdev
    exact hdev
  · intro h who replacement hconsidered
    obtain ⟨alternatives, hlaw⟩ :=
      simulation.deviation_mixture profile who replacement hconsidered
    have hdev := congrArg (fun law => law.expect (fun observation => value observation who)) hlaw
    simp only [FinDist.expect_map, FinDist.expect_bind] at hdev
    change
      (target.play (Profile.update
        (fun player => simulation.compileStrategy player (profile player)) who replacement)).expect
          (fun outcome => value (targetObserve outcome) who) ≤
        (target.play (simulation.compileProfile profile)).expect
          (fun outcome => value (targetObserve outcome) who) + ε
    rw [hdev, simulation.expect_compile profile (fun observation => value observation who)]
    calc
      alternatives.expect (fun alternative =>
          (source.play (Profile.update profile who alternative)).expect
            (fun outcome => value (sourceObserve outcome) who)) ≤
          alternatives.expect (fun _ =>
            (source.play profile).expect
              (fun outcome => value (sourceObserve outcome) who) + ε) :=
        FinDist.expect_mono fun alternative _ => h who alternative
      _ = (source.play profile).expect
          (fun outcome => value (sourceObserve outcome) who) + ε :=
        FinDist.expect_const _ _

theorem isεNash_compileProfile_iff (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile source.sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
        (simulation.compileProfile profile) ↔
      IsεNash source (fun outcome who => value (sourceObserve outcome) who) ε profile := by
  rw [← simulation.considered_deviations_iff_isεNash value ε profile]
  rw [GameTheory.isεNash_iff]
  constructor
  · intro h who replacement _
    exact h who replacement
  · intro h who replacement
    exact h who replacement (hall who replacement)

theorem isNash_compileProfile_iff (value : Observation → Player → ℝ)
    (profile : Profile source.sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsNash target (euPreference fun outcome who => value (targetObserve outcome) who)
        (simulation.compileProfile profile) ↔
      IsNash source (euPreference fun outcome who => value (sourceObserve outcome) who)
        profile := by
  simpa only [GameTheory.isNash_iff_isεNash_zero] using
    simulation.isεNash_compileProfile_iff value 0 profile hall

end MixtureSimulationOn
end GameTheory.GameForm

/-- info: 'GameTheory.GameForm.MixtureSimulationOn.guarantee' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.MixtureSimulationOn.guarantee

/-- info: 'GameTheory.GameForm.MixtureSimulationOn.isεNash_compileProfile_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.MixtureSimulationOn.isεNash_compileProfile_iff

/-- info: 'GameTheory.GameForm.MixtureSimulationOn.isNash_compileProfile_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.MixtureSimulationOn.isNash_compileProfile_iff
