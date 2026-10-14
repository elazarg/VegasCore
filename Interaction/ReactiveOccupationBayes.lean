/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveControlOccupation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Actual Bayes control laws from finite command occupation -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) [NeZero horizon] (scheduler : app.Scheduler)
  [Fintype (menu.protocol initial horizon scheduler).History]

local notation "model" => menu.information initial horizon scheduler
local notation "protocol" => menu.protocol initial horizon scheduler

omit [Fintype Principal] [NeZero horizon]
    [Fintype (menu.protocol initial horizon scheduler).History] in
private theorem site_info_ne_none (who : Principal) (site : (model).InformationSite who) :
    site.1 ≠ none := by
  obtain ⟨_, _, response, legal⟩ := site.2
  have raw := (menu.rawChoice initial horizon scheduler who site.1 ⟨some response, legal⟩).2
  change (some response).isSome = site.1.isSome at raw
  intro absent
  rw [absent] at raw
  cases raw

open Classical in
/-- Gating by a genuine owner's complete information selects precisely its
actual information histories, across all environmental command counts. -/
theorem occupation_gated_expect
    (profile : ∀ who, (model).BehavioralPolicy who)
    (who : Principal) (site : (model).InformationSite who)
    (value : app.ProtocolState → ℝ) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (bounded : ∀ state, |value state| ≤ bound) :
    expect (app.occupationControlLaw scheduler
        (menu.decodeProfile initial horizon scheduler profile) initial horizon)
      (fun state => if app.observe who state = site.1 then value state else 0) =
      (∑ history : (model).InformationHistory who site.1,
        ((model).historyReachWeight profile history.1).toReal *
          value history.1.state) / horizon := by
  classical
  let gated := fun state => if app.observe who state = site.1 then value state else 0
  have gateBounded : ∀ state, |gated state| ≤ bound := by
    intro state
    dsimp only [gated]
    split_ifs
    · exact bounded state
    · simpa only [abs_zero] using nonnegative
  have present := menu.site_info_ne_none initial horizon scheduler who site
  have idle : ∀ remaining execution, gated (some ⟨remaining, none, execution⟩) = 0 := by
    intro remaining execution
    simp only [gated, ReactiveApplication.observe, reduceCtorEq, ↓reduceIte,
      Ne.symm present]
  have unstarted : gated none = 0 := by
    simp only [gated, ReactiveApplication.observe, Ne.symm present, ↓reduceIte]
  have occupied := menu.expect_occupationControlLaw_eq_reach initial horizon scheduler profile
    gated nonnegative gateBounded idle unstarted
  change expect (app.occupationControlLaw scheduler
    (menu.decodeProfile initial horizon scheduler profile) initial horizon) gated = _
  rw [occupied]
  congr 1
  calc
    _ = ∑ history : (protocol).History,
        if (model).infoOf who history.trace = site.1 then
          ((model).historyReachWeight profile history).toReal * value history.state else 0 := by
      apply Finset.sum_congr rfl
      intro history _
      have observed := menu.info initial horizon scheduler who history.trace
      change (model).infoOf who history.trace = app.observe who history.state at observed
      dsimp only [gated]
      rw [← observed]
      split_ifs <;> simp only [mul_zero]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

omit [NeZero horizon] in
open Classical in
private theorem informationMass_toReal_sum
    (profile : ∀ who, (model).BehavioralPolicy who)
    (who : Principal) (site : (model).InformationSite who) :
    ((model).informationMass profile who site).toReal =
      ∑ history : (model).InformationHistory who site.1,
        ((model).historyReachWeight profile history.1).toReal := by
  change (∑' history : (model).InformationHistory who site.1,
    (model).historyReachWeight profile history.1).toReal = _
  exact (ENNReal.tsum_toReal_eq (fun history : (model).InformationHistory who site.1 =>
    PMF.apply_ne_top ((model).runBehavioral profile history.1.trace.length) history.1)).trans
      (tsum_fintype _)

omit [Fintype (menu.protocol initial horizon scheduler).History] in
open Classical in
/-- The full owner-observation mass is exactly the standard information mass
normalized by the number of genuine command indices. -/
theorem occupation_information_mass
    [Finite (menu.protocol initial horizon scheduler).History]
    (profile : ∀ who, (model).BehavioralPolicy who)
    (who : Principal) (site : (model).InformationSite who) :
    (((app.occupationControlLaw scheduler
      (menu.decodeProfile initial horizon scheduler profile) initial horizon).map
        (app.observe who)) site.1).toReal =
      ((model).informationMass profile who site).toReal / horizon := by
  classical
  let := Fintype.ofFinite (menu.protocol initial horizon scheduler).History
  rw [toReal_map_apply]
  have occupied := menu.occupation_gated_expect initial horizon scheduler profile who site
    (fun _ => (1 : ℝ)) (by norm_num : 0 ≤ (1 : ℝ)) (fun _ => by norm_num)
  have massReal := menu.informationMass_toReal_sum initial horizon scheduler profile who site
  calc
    _ = expect (app.occupationControlLaw scheduler
        (menu.decodeProfile initial horizon scheduler profile) initial horizon)
        (fun state => if app.observe who state = site.1 then (1 : ℝ) else 0) := by
      apply expect_congr_on_support
      intro state _
      by_cases same : app.observe who state = site.1
      · rw [ite_eq_left same, ite_eq_left same.symm]
      · rw [ite_eq_right same, ite_eq_right (Ne.symm same)]
    _ = _ := by simpa only [mul_one, ← massReal] using occupied

omit [Fintype (menu.protocol initial horizon scheduler).History] in
open Classical in
/-- The standard actual Bayes control mean equals conditioning the genuine
uniform command-boundary law on the same complete owner observation. -/
theorem occupation_posterior_expect
    [Finite (menu.protocol initial horizon scheduler).History]
    (profile : ∀ who, (model).BehavioralPolicy who)
    (who : Principal) (site : (model).InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (positive : 0 < (model).informationMass profile who site)
    (value : app.ProtocolState → ℝ) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (bounded : ∀ state, |value state| ≤ bound) :
    expect (fiberPosterior
        (app.occupationControlLaw scheduler
          (menu.decodeProfile initial horizon scheduler profile) initial horizon)
        (app.observe who) site.1) value =
      expect ((model).bayesBelief profile who site antichain positive)
        (fun history => value history.1.state) := by
  classical
  let := Fintype.ofFinite (menu.protocol initial horizon scheduler).History
  let law := app.occupationControlLaw scheduler
    (menu.decodeProfile initial horizon scheduler profile) initial horizon
  let mass := (model).informationMass profile who site
  have massPositive : 0 < mass.toReal := ENNReal.toReal_pos (ne_of_gt positive)
    (ne_of_lt (lt_of_le_of_lt ((model).informationMass_le_one profile who site antichain)
      ENNReal.one_lt_top))
  have horizonPositive : 0 < (horizon : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have marginal := menu.occupation_information_mass initial horizon scheduler profile who site
  change ((law.map (app.observe who)) site.1).toReal = mass.toReal / horizon at marginal
  have marginalPositive : 0 < ((law.map (app.observe who)) site.1).toReal := by
    rw [marginal]
    exact div_pos massPositive horizonPositive
  have support : site.1 ∈ (law.map (app.observe who)).support := by
    exact (PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp marginalPositive).1
  have denominator : (∑' state,
      ((app.observe who) ⁻¹' {site.1}).indicator law state) =
        (law.map (app.observe who)) site.1 := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro state
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    by_cases same : app.observe who state = site.1
    · rw [ite_eq_left same, ite_eq_left same.symm]
    · rw [ite_eq_right same, ite_eq_right (Ne.symm same)]
  have numerator := menu.occupation_gated_expect initial horizon scheduler profile who site value
    nonnegative bounded
  have posterior : expect (fiberPosterior law (app.observe who) site.1) value =
      (∑ history : (model).InformationHistory who site.1,
        ((model).historyReachWeight profile history.1).toReal * value history.1.state) /
          mass.toReal := by
    rw [expect_fiberPosterior law (app.observe who) value site.1 support, denominator, marginal]
    have gated : (((app.observe who) ⁻¹' {site.1}).indicator value) =
        fun state => if app.observe who state = site.1 then value state else 0 := by
      funext state
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    rw [gated, numerator]
    exact div_div_div_cancel_right₀ (ne_of_gt horizonPositive) _ _
  rw [posterior, expect_eq_sum]
  simp only [InformationModel.bayesBelief_apply, ENNReal.toReal_div]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

end Interaction.ReactiveApplication.ResponseMenu
