/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit
import Vegas.Examples.CommitSeedBroadcastFirstLateProvenance
import Interaction.ReactiveSchedulerSeedBayes
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveFiniteAssessment

/-! # Original service seeds in the actual full native Bayes information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem fixed_occupation_raw_trace (seed : Seeds) (players : Player → app.Policy)
    (state : app.ProtocolState)
    (supported : state ∈
      (app.occupationControlLaw (family seed) players initial horizon).support) :
    ∃ current, state = some current ∧
      Nonempty ((app.protocol initial horizon (family seed)).Trace (some current)) := by
  rw [ReactiveApplication.occupationControlLaw, PMF.support_bind] at supported
  obtain ⟨time, _uniform, commanded⟩ := Set.mem_iUnion₂.mp supported
  change state ∈ (app.commandControlLaw (family seed) players initial
    (horizon - time.val - 1) time.val).support at commanded
  rw [ReactiveApplication.commandControlLaw, initial, PMF.pure_bind,
    PMF.support_bind] at commanded
  obtain ⟨before, beforeReached, chosen⟩ := Set.mem_iUnion₂.mp commanded
  obtain ⟨command, selected, activeSupport⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ chosen)
  obtain ⟨active, moved, stateEq⟩ := PMF.support_map .. ▸ activeSupport
  have rounds : before ∈
      (app.roundsFrom initial (family seed) players time.val).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind] using beforeReached
  obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seed) players time.val
    (Nat.le_of_lt time.isLt) before rounds
  have remaining : horizon - time.val = (horizon - time.val - 1) + 1 := by
    have inside := time.isLt
    omega
  rw [remaining] at beforeTrace
  obtain ⟨activeTrace⟩ := app.raw_trace_environment initial horizon (family seed)
    (horizon - time.val - 1) before active command beforeTrace selected moved
  exact ⟨_, stateEq.symm, ⟨activeTrace⟩⟩

/-- The complete native history determines the original bad-service mark at a
clock-two decision, even though the owner does not observe that mark. -/
def firstLateBadValue : app.ProtocolState → ℝ
  | none => 0
  | some current => if 12 ≤ current.execution.environmentRecall.length then 1 else 0

private theorem firstLateBadValue_bounded (state : app.ProtocolState) :
    |firstLateBadValue state| ≤ 1 := by
  cases state with
  | none => norm_num [firstLateBadValue]
  | some current =>
      change |if 12 ≤ current.execution.environmentRecall.length then (1 : ℝ) else 0| ≤ 1
      split <;> norm_num

/-- Conditioning the initialized seed-tagged occupation on the owner's complete
native information gives exactly the ordinary native Bayes bad-history mass.
The full original seed posterior is retained; no new prior is introduced. -/
theorem firstLate_original_seed_bayes
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view))
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2)
    (positive : 0 < rawModel.informationMass profile owner site) :
    let players := rawMenu.decodeProfile initial horizon scheduler profile
    let joint := nativeSeedLaw.bind fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)
    expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1) site.1)
        (fun outcome => if outcome.2.2 owner = false then (1 : ℝ) else 0) =
      expect (rawModel.bayesBelief profile owner site
        (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
          (fun history => firstLateBadValue history.1.state) := by
  intro players joint
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
  have fiberPresent : site.1 ∈
      (joint.map (fun outcome => app.observe owner outcome.1)).support := by
    rw [PMF.support_map]
    exact ⟨(state, seed), pairSupport, same⟩
  have marked : expect
      (fiberPosterior joint (fun outcome => app.observe owner outcome.1) site.1)
      (fun outcome => if outcome.2.2 owner = false then (1 : ℝ) else 0) =
      expect (fiberPosterior joint (fun outcome => app.observe owner outcome.1) site.1)
        (fun outcome => firstLateBadValue outcome.1) := by
    apply expect_congr_on_support
    intro outcome supported
    obtain ⟨observedHere, actual⟩ := mem_support_fiberPosterior fiberPresent supported
    obtain ⟨seed, _prior, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
    obtain ⟨state, stateSupport, equal⟩ := PMF.support_map .. ▸ produced
    subst outcome
    obtain ⟨current, stateEq, ⟨trace⟩⟩ :=
      fixed_occupation_raw_trace seed players state stateSupport
    subst state
    have active : current.actor = some owner := by
      by_contra absent
      simp only [ReactiveApplication.observe, absent, ite_false] at observedHere
      rw [observed] at observedHere
      cases observedHere
    have sameInfo : current.execution.observe app owner = view := by
      simp only [ReactiveApplication.observe, active, ite_true] at observedHere
      rw [observed] at observedHere
      exact congrArg Prod.snd (Option.some.inj observedHere)
    have originalHere : current.execution.application.attempt = originalAttempt :=
      (congrArg (fun actual : app.PlayerView => actual.application.2.attempt) sameInfo).trans
        original
    have clockHere : current.execution.application.current.native.clock = 2 :=
      (congrArg (fun actual : app.PlayerView => actual.application.2.native.clock) sameInfo).trans
        clock
    have bad := original_first_late_bad_iff seed current trace owner active originalHere clockHere
    by_cases failed : seed.2 owner = false
    · rw [ite_eq_left failed, firstLateBadValue, ite_eq_left (bad.mp failed)]
    · rw [ite_eq_right failed, firstLateBadValue, ite_eq_right (mt bad.mpr failed)]
  rw [marked]
  have : app.FiniteNature initial (app.schedulerMixture nativeSeedLaw family).scheduler := by
    change app.FiniteNature initial scheduler
    exact finiteNature
  have bayes : fiberPosterior joint (fun outcome => app.observe owner outcome.1) site.1 =
      ((rawModel.bayesBelief profile owner site
        (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive).map
        (fun history => history.1.state)).bind fun state => (draws state).map (Prod.mk state) := by
    convert rawMenu.bayesBelief_seededOccupation (app := app)
      nativeSeedLaw family initial horizon profile owner site positive using 1
    · rfl
    · congr 1
      funext state
      cases state <;> rfl
  rw [bayes]
  rw [expect_bind_tower_bounded _ _
    (fun outcome : app.ProtocolState × Seeds => firstLateBadValue outcome.1)
    (fun outcome => firstLateBadValue_bounded outcome.1)]
  simp only [expect_map, Function.comp_def, expect_constant]

end Vegas.Examples.CommitSeedBroadcast
