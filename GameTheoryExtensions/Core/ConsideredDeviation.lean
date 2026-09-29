/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.MixtureSimulation
import GameTheory.Core.Response

/-! # Unilateral bounds for considered deviations

A mixture simulation may cover only a restricted class of target deviations.
Each covered deviation with integrable utility is still matched by one
supported source deviation with at least its expected utility. This is the
unilateral step of `GameTheory.GameForm.MixtureSimulationOn.toUtilitySimulation`
without requiring every target deviation to be covered, and it gives best
responses against the covered class.
-/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uSourceOutcome uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {Observation : Type*} {sourceObserve : source.sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)

/-- A covered target deviation with integrable utility is matched by one source
deviation whose expected utility is at least as large. -/
theorem exists_source_deviation_ge (utility : Observation → Player → ℝ)
    (profile : Profile source.sig) (who : Player) (replacement : target.sig.Strategy who)
    (considered : Considered who replacement)
    (integrable : UtilityIntegrable (fun outcome player => utility (targetObserve outcome) player)
      who (target.play (Profile.update (simulation.compileProfile profile) who replacement))) :
    ∃ alternative : source.sig.Strategy who,
      expectedUtility (fun outcome player => utility (targetObserve outcome) player) who
          (target.play (Profile.update (simulation.compileProfile profile) who replacement)) ≤
        expectedUtility (fun outcome player => utility (sourceObserve outcome) player) who
          (source.play (Profile.update profile who alternative)) := by
  classical
  let value : Observation → ℝ := fun observation => utility observation who
  let kernel : source.sig.Strategy who → PMF Observation := fun alternative =>
    (source.play (Profile.update profile who alternative)).map sourceObserve
  obtain ⟨alternatives, hlaw⟩ := simulation.deviation_mixture profile who replacement considered
  have htobs : PayoffIntegrable
      ((target.play (Profile.update (simulation.compileProfile profile) who replacement)).map
        targetObserve) value := (payoffIntegrable_map_iff targetObserve _ value).mpr integrable
  have hbind : PayoffIntegrable (alternatives.bind kernel) value := by
    rw [← hlaw]
    exact htobs
  let g : source.sig.Strategy who → ℝ := fun a =>
    if a ∈ alternatives.support then expect (kernel a) value else 0
  have hagree : ∀ a, ∀ _ : a ∈ alternatives.support, g a = expect (kernel a) value := by
    intro a ha
    simp only [g, ha, ↓reduceIte]
  have hg := payoffIntegrable_bind_conditionalValue_on_support alternatives kernel value hbind g
    hagree
  obtain ⟨alternative, ha, hmean⟩ := exists_expect_le_support alternatives g hg
  refine ⟨alternative, ?_⟩
  calc
    expectedUtility (fun outcome player => utility (targetObserve outcome) player) who
        (target.play (Profile.update (simulation.compileProfile profile) who replacement)) =
      expect (alternatives.bind kernel) value :=
        (expect_map targetObserve _ value).symm.trans (expect_congr_law hlaw value)
    _ = expect alternatives g :=
      expect_bind_tower_on_support alternatives kernel value hbind g hagree
    _ ≤ g alternative := hmean
    _ = expect (kernel alternative) value := hagree alternative ha
    _ = expectedUtility (fun outcome player => utility (sourceObserve outcome) player) who
        (source.play (Profile.update profile who alternative)) :=
      expect_map sourceObserve _ value

/-- A source best response compiles to a best response against every covered
target deviation whose utility is integrable. -/
theorem compileStrategy_ge_considered (utility : Observation → Player → ℝ)
    (profile : Profile source.sig) (who : Player)
    (best : IsBestResponse source
      (euPreference fun outcome player => utility (sourceObserve outcome) player) who profile
      (profile who))
    (replacement : target.sig.Strategy who) (considered : Considered who replacement)
    (integrable : UtilityIntegrable (fun outcome player => utility (targetObserve outcome) player)
      who (target.play (Profile.update (simulation.compileProfile profile) who replacement)))
    (sourceIntegrable : ∀ alternative : source.sig.Strategy who,
      UtilityIntegrable (fun outcome player => utility (sourceObserve outcome) player) who
        (source.play (Profile.update profile who alternative))) :
    euPreference (fun outcome player => utility (targetObserve outcome) player) who
      (target.play (simulation.compileProfile profile))
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)) := by
  obtain ⟨alternative, bound⟩ :=
    simulation.exists_source_deviation_ge utility profile who replacement considered integrable
  have baseline := sourceIntegrable (profile who)
  rw [Profile.update_eq_self] at baseline
  have hbest := best alternative
  rw [Profile.update_eq_self] at hbest
  have hsource := (euPreference_iff _ _ _ _ baseline (sourceIntegrable alternative)).mp hbest
  refine (euPreference_iff _ _ _ _ ((simulation.integrable_compile_iff profile
    (fun observation => utility observation who)).mpr baseline) integrable).mpr ?_
  have honest := simulation.expect_compile profile (fun observation => utility observation who)
  exact bound.trans (hsource.trans_eq honest.symm)

end GameTheory.GameForm.MixtureSimulationOn
