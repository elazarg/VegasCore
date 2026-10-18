/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOccupationRepair
import Interaction.ReactiveSchedulerSeedBayes
import GameTheoryExtensions.Analysis.Protocol.ConsistentLikelihood

/-! # Original regular-prefix probability in sequentially consistent native beliefs -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability Filter

def originalSeedPosterior (state : app.ProtocolState) : PMF Seeds :=
  match state with
  | none => nativeSeedLaw
  | some current => implementation.posterior current.execution.environmentRecall

open Classical in
def regularFirstLateValue (state : app.ProtocolState) : ℝ :=
  expect (originalSeedPosterior state)
    (fun seed => if regularFirstLateControl seed state then (1 : ℝ) else 0)

theorem regularFirstLateValue_mem_Icc (state : app.ProtocolState) :
    regularFirstLateValue state ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  refine ⟨expect_nonneg _ _ (fun seed _ => ?_), expect_le_const _ _
    (payoffIntegrable_ite_one_zero _ _) 1 (fun seed _ => ?_)⟩ <;>
    split_ifs <;> norm_num

open Classical in
private theorem original_regular_posterior_lower
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    let players := rawMenu.decodeProfile initial horizon scheduler profile
    let joint := nativeSeedLaw.bind fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)
    ∀ _positive : some (past, view) ∈
      (joint.map (fun outcome => app.observe owner outcome.1)).support,
    (1 / 48 : ℝ) ≤
      expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1)
        (some (past, view)))
        (fun outcome => if regularFirstLateControl outcome.2 outcome.1 then (1 : ℝ) else 0) := by
  classical
  intro players joint positive
  let observation := fun outcome : app.ProtocolState × Seeds => app.observe owner outcome.1
  let input := some (past, view)
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
          if regularFirstLateControl outcome.2 outcome.1 then (1 : ℝ) else 0) =
      (fun outcome => if observation outcome = input then
        if regularFirstLateControl outcome.2 outcome.1 then (1 : ℝ) else 0 else 0) := by
    funext outcome
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  rw [expect_fiberPosterior joint observation _ input positive, numeratorEq]
  apply (le_div_iff₀ denominatorPositive).mpr
  rw [← denominatorEq]
  have bound := firstLate_regular_occupation_domination profile owner past view original clock empty
  have totalEq : expect joint (fun outcome =>
      if observation outcome = input then (1 : ℝ) else 0) =
      expect nativeSeedLaw (fun seed =>
        expect (app.occupationControlLaw (family seed) players initial horizon)
          (fun state => if app.observe owner state = some (past, view) then (1 : ℝ) else 0)) := by
    rw [show joint = nativeSeedLaw.bind (fun seed =>
        (app.occupationControlLaw (family seed) players initial horizon).map
          fun state => (state, seed)) from rfl,
      expect_bind_tower_bounded _ _ _ (C := 1) (by
        intro outcome
        split_ifs <;> norm_num)]
    simp only [expect_map, Function.comp_def, observation, input]
  have regularEq : expect joint (fun outcome => if observation outcome = input then
      if regularFirstLateControl outcome.2 outcome.1 then (1 : ℝ) else 0 else 0) =
      expect nativeSeedLaw (fun seed =>
        expect (app.occupationControlLaw (family seed) players initial horizon)
          (fun state => if app.observe owner state = some (past, view) then
            if regularFirstLateControl seed state then (1 : ℝ) else 0 else 0)) := by
    rw [show joint = nativeSeedLaw.bind (fun seed =>
        (app.occupationControlLaw (family seed) players initial horizon).map
          fun state => (state, seed)) from rfl,
      expect_bind_tower_bounded _ _ _ (C := 1) (by
        intro outcome
        split_ifs <;> norm_num)]
    simp only [expect_map, Function.comp_def, observation, input]
  rw [totalEq, regularEq]
  linarith

theorem firstLate_bayes_regular_lower
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view))
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = [])
    (positive : 0 < rawModel.informationMass profile owner site) :
    (1 / 48 : ℝ) ≤ expect (rawModel.bayesBelief profile owner site
      (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
      (fun history => regularFirstLateValue history.1.state) := by
  classical
  let players := rawMenu.decodeProfile initial horizon scheduler profile
  let joint := nativeSeedLaw.bind fun seed =>
    (app.occupationControlLaw (family seed) players initial horizon).map
      fun state => (state, seed)
  let occupation := app.occupationControlLaw scheduler players initial horizon
  have realized : joint = occupation.bind fun state =>
      (originalSeedPosterior state).map (Prod.mk state) := by
    convert app.schedulerMixture_occupation_joint nativeSeedLaw family players initial horizon
      using 1
    congr 1
    funext state
    cases state <;> rfl
  have present := rawMenu.occupation_observation_support initial horizon scheduler profile
    owner site positive
  change site.1 ∈ (occupation.map (app.observe owner)).support at present
  obtain ⟨state, stateSupport, same⟩ := PMF.support_map .. ▸ present
  obtain ⟨seed, seedSupport⟩ := (originalSeedPosterior state).support_nonempty
  have pairSupport : (state, seed) ∈ joint.support := by
    rw [realized, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, stateSupport,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, seedSupport, rfl⟩⟩
  have fiberPresent : some (past, view) ∈
      (joint.map (fun outcome => app.observe owner outcome.1)).support := by
    rw [PMF.support_map]
    exact ⟨(state, seed), pairSupport, same.trans observed⟩
  have lower := original_regular_posterior_lower profile owner past view original clock empty
    fiberPresent
  have : app.FiniteNature initial (app.schedulerMixture nativeSeedLaw family).scheduler := by
    change app.FiniteNature initial scheduler
    exact finiteNature
  have bridge : fiberPosterior joint (fun outcome => app.observe owner outcome.1) site.1 =
      (((rawModel.bayesBelief profile owner site
        (rawMenu.decisionInformationAntichain initial horizon scheduler owner site)
          positive).map (fun history => history.1.state)).bind fun state =>
            (originalSeedPosterior state).map (Prod.mk state)) := by
    convert rawMenu.bayesBelief_seededOccupation (app := app) nativeSeedLaw family initial horizon
      profile owner site positive using 1
    · rfl
    · congr 1
      funext current
      cases current <;> rfl
  have renamed : expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1)
      (some (past, view)))
      (fun outcome => if regularFirstLateControl outcome.2 outcome.1 then (1 : ℝ) else 0) =
      expect (rawModel.bayesBelief profile owner site
        (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
        (fun history => regularFirstLateValue history.1.state) := by
    rw [← observed, bridge, expect_bind_tower_bounded _ _ _ (C := 1) (by
      intro outcome
      split_ifs <;> norm_num)]
    simp only [expect_map, Function.comp_def, regularFirstLateValue]
  exact lower.trans_eq renamed

/-- The posterior refers to the original immutable scheduler draw. Its mean is
continuous in the finite native belief, including at zero-reach limiting sites. -/
theorem assessed_firstLate_regular_lower
    (assessment : rawModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (rawMenu.decisionInformationAntichain initial horizon scheduler))
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view))
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    (1 / 48 : ℝ) ≤ expect (assessment.belief owner site)
      (fun history => regularFirstLateValue history.1.state) := by
  classical
  let := Fintype.ofFinite rawProtocol.History
  obtain ⟨sequence, approximate, converges⟩ := consistent
  have bound (n : Nat) : (1 / 48 : ℝ) ≤ expect ((sequence n).belief owner site)
      (fun history => regularFirstLateValue history.1.state) := by
    have positive := rawModel.informationMass_pos_of_fullSupport (sequence n).strategy
      (approximate n).1 owner site
    have law : (sequence n).belief owner site = rawModel.bayesBelief (sequence n).strategy
        owner site (rawMenu.decisionInformationAntichain initial horizon scheduler owner site)
          positive := PMF.ext ((approximate n).2 owner site positive)
    rw [law]
    exact firstLate_bayes_regular_lower (sequence n).strategy owner site past view observed
      original clock empty positive
  have tends : Tendsto (fun n => expect ((sequence n).belief owner site)
      (fun history => regularFirstLateValue history.1.state)) atTop
      (nhds (expect (assessment.belief owner site)
        (fun history => regularFirstLateValue history.1.state))) := by
    simp only [expect, tsum_fintype]
    exact tendsto_finsetSum _ fun history _ =>
      ((converges.belief owner site).toReal history).mul_const _
  exact ge_of_tendsto tends (Eventually.of_forall bound)

end Vegas.Examples.CommitSeedBroadcast
