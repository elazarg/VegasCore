/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastQuietSeedBelief
import Vegas.Examples.CommitSeedBroadcastInitialQuietReplay
import GameTheoryExtensions.Analysis.Protocol.ConsistentLikelihood

/-! # Actual reference-history bound before cancelling the original quiet density -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Ordinary native Bayes at the actual quiet reference has the original seed
bound. Both the physical information fiber and the original seed tag are retained. -/
theorem quiet_native_bayes_bad_le (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (waited : ∀ observer,
      rawMenu.decodeProfile initial horizon scheduler profile observer
        ((initialCallback observer).recall observer)
        ((initialCallback observer).observe app observer) = PMF.pure ⟨none⟩)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view)) (length : past.length = 1)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2)
    (positive : 0 < rawModel.informationMass profile owner site) :
    expect (rawModel.bayesBelief profile owner site
      (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
      (fun history => firstLateBadValue history.1.state) ≤ (271 / 1000 : ℝ) := by
  let players := rawMenu.decodeProfile initial horizon scheduler profile
  let joint := nativeSeedLaw.bind fun seed =>
    (app.occupationControlLaw (family seed) players initial horizon).map
      fun state => (state, seed)
  let occupation := app.occupationControlLaw scheduler players initial horizon
  let draws : app.ProtocolState → PMF Seeds := fun state => match state with
    | none => nativeSeedLaw
    | some current => implementation.posterior current.execution.environmentRecall
  have realized : joint = occupation.bind fun state => (draws state).map (Prod.mk state) := by
    convert app.schedulerMixture_occupation_joint nativeSeedLaw family players initial horizon
      using 1
    congr 1
    funext state
    cases state <;> rfl
  have present := rawMenu.occupation_observation_support initial horizon scheduler profile
    owner site positive
  change site.1 ∈ (occupation.map (app.observe owner)).support at present
  obtain ⟨state, stateSupport, same⟩ := PMF.support_map .. ▸ present
  obtain ⟨seed, seedSupport⟩ := (draws state).support_nonempty
  have pairSupport : (state, seed) ∈ joint.support := by
    rw [realized, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, stateSupport,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, seedSupport, rfl⟩⟩
  have fiberPresent : some (past, view) ∈
      (joint.map (fun outcome => app.observe owner outcome.1)).support := by
    rw [PMF.support_map]
    exact ⟨(state, seed), pairSupport, same.trans observed⟩
  have bound := quiet_original_seed_posterior_le players waited owner past view length clock
    fiberPresent
  have bridge := firstLate_original_seed_bayes profile owner site past view observed
    original clock positive
  change expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1) site.1)
      (fun outcome => if outcome.2.2 owner = false then (1 : ℝ) else 0) = _ at bridge
  have rename := congrArg (fun input : NativeInput =>
    expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1) input)
      (fun outcome => if outcome.2.2 owner = false then (1 : ℝ) else 0)) observed
  exact bridge.symm.trans_le (rename.trans_le bound)

/-- The divide-free bound also holds at reference inputs with zero mass.
This is the form needed to cancel a possibly vanishing initial WAIT density. -/
theorem quiet_native_bad_reach_le
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (waited : ∀ observer,
      rawMenu.decodeProfile initial horizon scheduler profile observer
        ((initialCallback observer).recall observer)
        ((initialCallback observer).observe app observer) = PMF.pure ⟨none⟩)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view)) (length : past.length = 1)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) :
    (∑ history : rawModel.InformationHistory owner site.1,
      (rawModel.historyReachWeight profile history.1).toReal *
        firstLateBadValue history.1.state) ≤
      (271 / 1000 : ℝ) * ∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight profile history.1).toReal := by
  classical
  have massEq : (rawModel.informationMass profile owner site).toReal =
      ∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight profile history.1).toReal := by
    change (∑' history : rawModel.InformationHistory owner site.1,
      rawModel.historyReachWeight profile history.1).toReal = _
    exact (ENNReal.tsum_toReal_eq (fun history : rawModel.InformationHistory owner site.1 =>
      PMF.apply_ne_top (rawModel.runBehavioral profile history.1.trace.length) history.1)).trans
        (tsum_fintype _)
  by_cases positive : 0 < rawModel.informationMass profile owner site
  · have bound := quiet_native_bayes_bad_le profile waited owner site past view observed length
      original clock positive
    have denominatorPositive : 0 < (rawModel.informationMass profile owner site).toReal :=
      ENNReal.toReal_pos positive.ne' (ne_of_lt (lt_of_le_of_lt
        (rawModel.informationMass_le_one profile owner site
          (rawMenu.decisionInformationAntichain initial horizon scheduler owner site))
        ENNReal.one_lt_top))
    have normalized : expect (rawModel.bayesBelief profile owner site
        (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
        (fun history => firstLateBadValue history.1.state) =
        (∑ history : rawModel.InformationHistory owner site.1,
          (rawModel.historyReachWeight profile history.1).toReal *
            firstLateBadValue history.1.state) /
              (rawModel.informationMass profile owner site).toReal := by
      simp only [expect, tsum_fintype, rawModel.bayesBelief_apply, ENNReal.toReal_div]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro history _member
      ring
    rw [normalized] at bound
    rw [← massEq]
    exact (div_le_iff₀ denominatorPositive).mp bound
  · have zero : rawModel.informationMass profile owner site = 0 :=
      le_antisymm (le_of_not_gt positive) bot_le
    have each (history : rawModel.InformationHistory owner site.1) :
        (rawModel.historyReachWeight profile history.1).toReal = 0 := by
      have absent : rawModel.historyReachWeight profile history.1 = 0 := by
        apply le_antisymm _ bot_le
        calc
          _ ≤ rawModel.informationMass profile owner site := ENNReal.le_tsum history
          _ = 0 := zero
      rw [absent, ENNReal.toReal_zero]
    simp only [each, zero_mul, Finset.sum_const_zero, mul_zero, le_refl]

end Vegas.Examples.CommitSeedBroadcast
