/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.MixtureSimulation
import GameTheoryExtensions.Math.SelectiveStopping

/-! # Strategic transfer by utility bounds

Some target deviations admit a source deviation with at least as much utility,
although their outcome laws differ. This suffices for preservation and
reflection of Nash and approximate Nash at compiled profiles. The utilities
are parameters of this certificate. It does not transport guarantees for
other utilities or other players affected by the deviator.
-/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uMiddle uSourceOutcome uTargetOutcome uMiddleOutcome

variable {Player : Type uPlayer} [DecidableEq Player]

/-- A strategy translation preserves honest expected utilities and bounds every
unilateral target deviation by one legal source deviation. The witness may
depend on the fixed opponents and the utilities being analyzed. -/
structure UtilitySimulation
    (source : GameForm.{uPlayer, uSource, uSourceOutcome} Player)
    (target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player)
    (sourceUtility : source.sig.Outcome → Player → ℝ)
    (targetUtility : target.sig.Outcome → Player → ℝ) where
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  honest_utility : ∀ profile who,
    (target.play (fun player => compileStrategy player (profile player))).expect
        (fun outcome => targetUtility outcome who) =
      (source.play profile).expect (fun outcome => sourceUtility outcome who)
  deviation_bound : ∀ profile who replacement,
    ∃ alternative : source.sig.Strategy who,
      (target.play (Profile.update (fun player => compileStrategy player (profile player))
        who replacement)).expect (fun outcome => targetUtility outcome who) ≤
      (source.play (Profile.update profile who alternative)).expect
        (fun outcome => sourceUtility outcome who)

variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {sourceUtility : source.sig.Outcome → Player → ℝ}
variable {targetUtility : target.sig.Outcome → Player → ℝ}

/-- Utility equality for compiled source profiles and deviation bounds at one
fixed profile suffice for same-error Nash equivalence at that profile. Unlike
`UtilitySimulation`, this theorem does not require a reusable deviation bound
at source profiles that are not under consideration. -/
theorem isεNash_compileProfile_iff_of_utility_bounds
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (profile : Profile source.sig)
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        (target.play (Profile.update (fun player => compileStrategy player (profile player))
          who replacement)).expect (fun outcome => targetUtility outcome who) ≤
        (source.play (Profile.update profile who alternative)).expect
          (fun outcome => sourceUtility outcome who))
    (ε : ℝ) :
    IsεNash target targetUtility ε
        (fun player => compileStrategy player (profile player)) ↔
      IsεNash source sourceUtility ε profile := by
  rw [isεNash_iff, isεNash_iff]
  constructor
  · intro h who alternative
    have hcompiled := h who (compileStrategy who alternative)
    have hupdate :
        Profile.update (fun player => compileStrategy player (profile player)) who
            (compileStrategy who alternative) =
          fun player => compileStrategy player
            ((Profile.update profile who alternative) player) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp
      · simp [Profile.update_of_ne, hplayer]
    rw [hupdate] at hcompiled
    change (target.play (fun player => compileStrategy player
        ((Profile.update profile who alternative) player))).expect
        (fun outcome => targetUtility outcome who) ≤
      (target.play (fun player => compileStrategy player (profile player))).expect
        (fun outcome => targetUtility outcome who) + ε at hcompiled
    rw [honestUtility, honestUtility] at hcompiled
    exact hcompiled
  · intro h who replacement
    obtain ⟨alternative, hbound⟩ := deviationBound who replacement
    exact hbound.trans (by
      rw [expectedUtility, honestUtility]
      exact h who alternative)

namespace UtilitySimulation

variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {sourceUtility : source.sig.Outcome → Player → ℝ}
variable {targetUtility : target.sig.Outcome → Player → ℝ}

def compileProfile (simulation : UtilitySimulation source target sourceUtility targetUtility)
    (profile : Profile source.sig) : Profile target.sig :=
  fun who => simulation.compileStrategy who (profile who)

theorem compileProfile_update
    (simulation : UtilitySimulation source target sourceUtility targetUtility)
    (profile : Profile source.sig) (who : Player) (alternative : source.sig.Strategy who) :
    Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who alternative) =
      simulation.compileProfile (Profile.update profile who alternative) := by
  funext player
  by_cases h : player = who
  · subst player; simp [compileProfile]
  · simp [compileProfile, Profile.update_of_ne, h]

/-- The same additive error is preserved and reflected at every compiled
profile. No claim concerns target equilibria outside the compiler image. -/
theorem isεNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility)
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (simulation.compileProfile profile) ↔
      IsεNash source sourceUtility ε profile := by
  exact isεNash_compileProfile_iff_of_utility_bounds simulation.compileStrategy
    simulation.honest_utility profile (simulation.deviation_bound profile) ε

theorem isNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility)
    (profile : Profile source.sig) :
    IsNash target (euPreference targetUtility) (simulation.compileProfile profile) ↔
      IsNash source (euPreference sourceUtility) profile := by
  simpa only [isNash_iff_isεNash_zero] using simulation.isεNash_compileProfile_iff 0 profile

/-- Utility comparisons compose through independently verified target layers. -/
def trans {middle : GameForm.{uPlayer, uMiddle, uMiddleOutcome} Player}
    {middleUtility : middle.sig.Outcome → Player → ℝ}
    (left : UtilitySimulation source middle sourceUtility middleUtility)
    (right : UtilitySimulation middle target middleUtility targetUtility) :
    UtilitySimulation source target sourceUtility targetUtility where
  compileStrategy who strategy := right.compileStrategy who (left.compileStrategy who strategy)
  honest_utility profile who :=
    (right.honest_utility (left.compileProfile profile) who).trans
      (left.honest_utility profile who)
  deviation_bound profile who replacement := by
    obtain ⟨middleAlternative, hright⟩ :=
      right.deviation_bound (left.compileProfile profile) who replacement
    obtain ⟨sourceAlternative, hleft⟩ := left.deviation_bound profile who middleAlternative
    exact ⟨sourceAlternative, hright.trans hleft⟩

end UtilitySimulation

/-- Exact finite-mixture simulation supplies utility simulation for every
chosen utility on the common observation. A finite mixture has a component
whose utility is at least its mean; no closure assumption on strategies is needed. -/
def MixtureSimulationOn.toUtilitySimulation
    {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
    {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
    {Observation : Type*} {sourceObserve : source.sig.Outcome → Observation}
    {targetObserve : target.sig.Outcome → Observation}
    {Considered : (who : Player) → target.sig.Strategy who → Prop}
    (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)
    (utility : Observation → Player → ℝ) (hall : ∀ who strategy, Considered who strategy) :
    UtilitySimulation source target
      (fun outcome who => utility (sourceObserve outcome) who)
      (fun outcome who => utility (targetObserve outcome) who) where
  compileStrategy := simulation.compileStrategy
  honest_utility profile who := simulation.expect_compile profile (fun obs => utility obs who)
  deviation_bound profile who replacement := by
    obtain ⟨alternatives, hlaw⟩ :=
      simulation.deviation_mixture profile who replacement (hall who replacement)
    have hexpect := congrArg (fun law => law.expect (fun obs => utility obs who)) hlaw
    simp only [FinDist.expect_map, FinDist.expect_bind] at hexpect
    obtain ⟨alternative, _, hbound⟩ := FinDist.exists_expect_le_support alternatives
      (fun alternative => (source.play (Profile.update profile who alternative)).expect
        (fun outcome => utility (sourceObserve outcome) who))
    exact ⟨alternative, hexpect.le.trans hbound⟩

end GameTheory.GameForm

/-- info: 'GameTheory.GameForm.UtilitySimulation.isεNash_compileProfile_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.UtilitySimulation.isεNash_compileProfile_iff

/-- info: 'GameTheory.GameForm.UtilitySimulation.trans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.UtilitySimulation.trans
