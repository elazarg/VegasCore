/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastQuietOccupation
import Vegas.Examples.CommitSeedBroadcastFirstLateSeedBelief

/-! # Original bad-seed posterior at a full native quiet input -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
private theorem quiet_joint_input_mass (players : Player → app.Policy)
    (waited : ∀ observer, players observer ((initialCallback observer).recall observer)
      ((initialCallback observer).observe app observer) = PMF.pure ⟨none⟩)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (length : past.length = 1) (clock : view.application.2.native.clock = 2) :
    let joint := nativeSeedLaw.bind fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)
    expect joint (fun outcome =>
      if app.observe owner outcome.1 = some (past, view) then (1 : ℝ) else 0) =
      (1 / (horizon : ℝ)) * expect nativeSeedLaw
        (quietFirstLateMass players owner (some (past, view))) := by
  classical
  intro joint
  rw [show joint = nativeSeedLaw.bind (fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)) from rfl,
    expect_bind_tower_bounded _ _ _ (C := 1) (by
      intro outcome
      split_ifs <;> norm_num)]
  simp only [expect_map, Function.comp_def]
  have pointwise (seed : Seeds) :
      expect (app.occupationControlLaw (family seed) players initial horizon)
        (fun state => if app.observe owner state = some (past, view) then (1 : ℝ) else 0) =
      (1 / (horizon : ℝ)) * quietFirstLateMass players owner (some (past, view)) seed := by
    have actual := quiet_fixed_input_mass seed players waited owner past view length clock
    rw [toReal_map_apply] at actual
    trans quietFirstLateMass players owner (some (past, view)) seed / horizon
    · convert actual using 1
      congr 1
      funext state
      by_cases equal : app.observe owner state = some (past, view)
      · rw [ite_eq_left equal, ite_eq_left equal.symm]
      · rw [ite_eq_right equal, ite_eq_right (Ne.symm equal)]
    · ring
  calc
    _ = expect nativeSeedLaw (fun seed => (1 / (horizon : ℝ)) *
        quietFirstLateMass players owner (some (past, view)) seed) :=
      expect_congr_on_support fun seed _supported => pointwise seed
    _ = _ := expect_const_mul

open Classical in
private theorem quiet_joint_bad_mass (players : Player → app.Policy)
    (waited : ∀ observer, players observer ((initialCallback observer).recall observer)
      ((initialCallback observer).observe app observer) = PMF.pure ⟨none⟩)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (length : past.length = 1) (clock : view.application.2.native.clock = 2) :
    let joint := nativeSeedLaw.bind fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)
    expect joint (fun outcome => if app.observe owner outcome.1 = some (past, view) then
      if outcome.2.2 owner = false then (1 : ℝ) else 0 else 0) =
      (1 / (horizon : ℝ)) * expect nativeSeedLaw (fun seed => if seed.2 owner = false then
        quietFirstLateMass players owner (some (past, view)) seed else 0) := by
  classical
  intro joint
  rw [show joint = nativeSeedLaw.bind (fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)) from rfl,
    expect_bind_tower_bounded _ _ _ (C := 1) (by
      intro outcome
      split_ifs <;> norm_num)]
  simp only [expect_map, Function.comp_def]
  have pointwise (seed : Seeds) :
      expect (app.occupationControlLaw (family seed) players initial horizon)
        (fun state => if app.observe owner state = some (past, view) then
          if seed.2 owner = false then (1 : ℝ) else 0 else 0) =
      (1 / (horizon : ℝ)) * (if seed.2 owner = false then
        quietFirstLateMass players owner (some (past, view)) seed else 0) := by
    by_cases bad : seed.2 owner = false
    · simp only [ite_eq_left bad]
      have actual := quiet_fixed_input_mass seed players waited owner past view length clock
      rw [toReal_map_apply] at actual
      trans quietFirstLateMass players owner (some (past, view)) seed / horizon
      · convert actual using 1
        congr 1
        funext state
        by_cases equal : app.observe owner state = some (past, view)
        · rw [ite_eq_left equal, ite_eq_left equal.symm]
        · rw [ite_eq_right equal, ite_eq_right (Ne.symm equal)]
      · ring
    · simp only [ite_eq_right bad, ite_self, expect_constant, mul_zero]
  calc
    _ = expect nativeSeedLaw (fun seed => (1 / (horizon : ℝ)) *
        (if seed.2 owner = false then
          quietFirstLateMass players owner (some (past, view)) seed else 0)) :=
      expect_congr_on_support fun seed _supported => pointwise seed
    _ = _ := expect_const_mul

/-- This bound conditions the original initialized seed occupation on the
complete native input. The three initial WAITs are an actual reference profile,
not a claim about the fully mixed assessment approximants. -/
theorem quiet_original_seed_posterior_le (players : Player → app.Policy)
    (waited : ∀ observer, players observer ((initialCallback observer).recall observer)
      ((initialCallback observer).observe app observer) = PMF.pure ⟨none⟩)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (length : past.length = 1) (clock : view.application.2.native.clock = 2) :
    let joint := nativeSeedLaw.bind fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)
    ∀ _positive : some (past, view) ∈
      (joint.map (fun outcome => app.observe owner outcome.1)).support,
    expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1) (some (past, view)))
      (fun outcome => if outcome.2.2 owner = false then (1 : ℝ) else 0) ≤
        (271 / 1000 : ℝ) := by
  classical
  intro joint positive
  let observation := fun outcome : app.ProtocolState × Seeds => app.observe owner outcome.1
  let input : NativeInput := some (past, view)
  let denominator := (∑' outcome, (observation ⁻¹' {input}).indicator joint outcome).toReal
  have denominatorPositive : 0 < denominator :=
    fiberMass_toReal_pos joint observation input positive
  have denominatorEq :
      expect joint (fun outcome => if observation outcome = input then (1 : ℝ) else 0) =
        denominator := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, PMF.toOuterMeasure_apply] using
      expect_indicator joint (observation ⁻¹' {input})
  have numeratorEq :
      (observation ⁻¹' {input}).indicator
        (fun outcome : app.ProtocolState × Seeds =>
          if outcome.2.2 owner = false then (1 : ℝ) else 0) =
      (fun outcome => if observation outcome = input then
        if outcome.2.2 owner = false then (1 : ℝ) else 0 else 0) := by
    funext outcome
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  rw [expect_fiberPosterior joint observation _ input positive, numeratorEq]
  apply (div_le_iff₀ denominatorPositive).mpr
  rw [← denominatorEq]
  have numerator := quiet_joint_bad_mass players waited owner past view length clock
  have total := quiet_joint_input_mass players waited owner past view length clock
  change expect joint (fun outcome => if app.observe owner outcome.1 = some (past, view) then
    if outcome.2.2 owner = false then (1 : ℝ) else 0 else 0) ≤
    (271 / 1000 : ℝ) * expect joint (fun outcome =>
      if app.observe owner outcome.1 = some (past, view) then (1 : ℝ) else 0)
  rw [numerator, total]
  have bound := quiet_firstLate_bad_mass_le players waited owner (some (past, view))
  have scaled := mul_le_mul_of_nonneg_left bound (by positivity : 0 ≤ 1 / (horizon : ℝ))
  nlinarith

end Vegas.Examples.CommitSeedBroadcast
