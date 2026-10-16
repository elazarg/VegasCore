/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPrivatePlan
import Interaction.ReactiveProfileMixture
import GameTheoryExtensions.Math.Probability.ConditionalProductMixture

/-! # Private plans for the actual finite played timing pools -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- A nontrivial current pool has not appeared at any earlier own response.
Free pools identify their actual agent; keyed pools retain complete recall
length. The remaining shared pool has one part. -/
theorem phaseTimingPool_fresh_or_subsingleton (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (present : some (past, view) ∈ (N).playedInformation who) :
    let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    Subsingleton (Parts (pool current)) ∨
      ∀ (before : List (app).PlayerEntry) (entry : (app).PlayerEntry),
        before ++ [entry] <+: past →
        ∀ earlier : some (before, entry.beforeView) ∈ (N).playedInformation who,
          pool (⟨who, ⟨some (before, entry.beforeView), earlier⟩⟩ : Agent) ≠ pool current := by
  intro current
  by_cases excluded : isFree current
  · right
    intro before entry recorded earlier equal
    have currentPool := freeKeyedPool_of_free (free := isFree) (keyed := isKeyed)
      (key := poolKey) (agent := current) excluded
    have same := eq_of_freeKeyedPool_eq_inl
      (free := isFree) (keyed := isKeyed) (key := poolKey) (equal.trans currentPool)
    have infoEq := congrArg (fun agent : Agent =>
      (Subtype.val (Sigma.snd agent) : (app).Info)) same
    exact phaseTimingKey_fresh runtime leaks who past before view entry recorded
      (congrArg (phaseTimingKey runtime leaks who) infoEq)
  · by_cases unprotected : isKeyed current
    · right
      intro before entry recorded earlier equal
      let previous : Agent := ⟨who, ⟨some (before, entry.beforeView), earlier⟩⟩
      have currentPool : pool current =
          Sum.inr (some ⟨poolKey current, ⟨current, unprotected, excluded⟩, rfl⟩) := by
        rw [phaseTimingPool, freeKeyedPool_of_not_free excluded,
          keyedPool_of_keyed (show ownedKeyed isFree isKeyed current from ⟨unprotected, excluded⟩)]
      by_cases wasFree : isFree previous
      · have priorPool := freeKeyedPool_of_free (free := isFree) (keyed := isKeyed)
          (key := poolKey) (agent := previous) wasFree
        change pool previous = pool current at equal
        rw [phaseTimingPool, priorPool] at equal
        change Sum.inl ⟨previous, wasFree⟩ = pool current at equal
        rw [currentPool] at equal
        cases equal
      · by_cases wasKeyed : isKeyed previous
        · have priorPool : pool previous =
              Sum.inr (some ⟨poolKey previous, ⟨previous, wasKeyed, wasFree⟩, rfl⟩) := by
            rw [phaseTimingPool, freeKeyedPool_of_not_free wasFree,
              keyedPool_of_keyed (show ownedKeyed isFree isKeyed previous from ⟨wasKeyed, wasFree⟩)]
          change pool previous = pool current at equal
          rw [priorPool, currentPool] at equal
          have keys := congrArg Subtype.val (Option.some.inj (Sum.inr.inj equal))
          exact phaseTimingKey_fresh runtime leaks who past before view entry recorded keys
        · have unowned : ¬ ownedKeyed isFree isKeyed previous := fun owned => wasKeyed owned.1
          change pool previous = pool current at equal
          rw [phaseTimingPool, freeKeyedPool_of_not_free wasFree,
            keyedPool_of_not_keyed unowned] at equal
          change Sum.inr none = pool current at equal
          rw [currentPool] at equal
          cases equal
    · left
      have unowned : ¬ ownedKeyed isFree isKeyed current := fun owned => unprotected owned.1
      change Subsingleton (FreeKeyedPart isFree isKeyed poolKey (LateOption bounds.candidateCount)
        (freeKeyedPool isFree isKeyed poolKey current))
      rw [freeKeyedPool_of_not_free excluded, keyedPool_of_not_keyed unowned]
      change Subsingleton Unit
      infer_instance

variable (fallback : (who : Player) →
    (ReactiveApplication.ResponseMenu.information (PhaseCount.onePacketMenu runtime leaks bounds)
      initial horizon scheduler).Policy who)
  (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
  (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)

open Classical in
/-- One finite assignment chooses the part of every actual played pool. The
existing agent assembly and runtime decoder supply the complete member policy. -/
def phaseTimingPlanPolicy (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player) : (app).Policy :=
  (menu).decodeProfile initial horizon scheduler
    ((N).agentBehavior (N).playedInformation fallback
      (fun agent => (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) agent (plan (pool agent)))) who

open Classical in
private theorem member_apply (plan : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who past view =
      (if present : some (past, view) ∈ (N).playedInformation who then
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) ⟨who, ⟨some (past, view), present⟩⟩
          (plan (pool ⟨who, ⟨some (past, view), present⟩⟩))
      else PMF.pure (fallback who (some (past, view)))).map
        (fun choice => choice.1.getD ⟨none⟩) := by
  simp only [phaseTimingPlanPolicy, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    PMF.map_comp, Function.comp_def, InformationModel.agentBehavior]
  by_cases present : some (past, view) ∈ (N).playedInformation who
  · simp only [dite_eq_left present]
    rfl
  · simp only [dite_eq_right present]
    rfl

open Classical in
/-- The actual current played pool is unread in the complete prior response
word; an unkeyed singleton part is ignored even if its pool occurs repeatedly. -/
theorem phaseTimingPlanPolicy_unread (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (present : some (past, view) ∈ (N).playedInformation who) :
    let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    ∀ (before : List (app).PlayerEntry) (entry : (app).PlayerEntry),
      before ++ [entry] <+: past → ∀ (plan : (p : Pool) → Parts p)
      (part : Parts (pool current)),
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) (Function.update plan (pool current) part) who before
            entry.beforeView =
          (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who before entry.beforeView := by
  intro current before entry recorded plan part
  obtain singleton | fresh := phaseTimingPool_fresh_or_subsingleton setup mode runtime leaks
    bounds initial horizon scheduler bound who past view present
  · have samePart : part = plan (pool current) := @Subsingleton.elim _ singleton _ _
    rw [samePart, Function.update_eq_self]
  · rw [member_apply, member_apply]
    by_cases earlier : some (before, entry.beforeView) ∈ (N).playedInformation who
    · rw [dite_eq_left earlier, dite_eq_left earlier,
        Function.update_of_ne (fresh before entry recorded earlier)]
    · rw [dite_eq_right earlier, dite_eq_right earlier]

open Classical in
/-- At every actual played owner input, the selected private pool part retains
its ORIGINAL common weight law independently of the entire remaining plan. -/
theorem phaseTimingPlanPolicy_posterior (weights : (p : Pool) → PMF (Parts p))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (present : some (past, view) ∈ (N).playedInformation who) :
    let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    ∃ remainder : PMF ((p : {p // p ≠ pool current}) → Parts p.val),
      (((app).policyMixture (independentProduct weights) (fun plan =>
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who)).posterior
        past).map (Equiv.piSplitAt (pool current) Parts) =
      (weights (pool current)).bind (fun part => remainder.map (Prod.mk part)) := by
  intro current
  exact (app).policyMixture_posterior_coordinate weights (fun plan =>
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who)
    (pool current) past (phaseTimingPlanPolicy_unread setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded who past view present)

open Classical in
/-- The original common pool weights realize the ENTIRE actual assembled
finite phase strategy. Neither unread coordinates nor a target response-law
equality is supplied as a premise. -/
theorem phaseTimingPlanPolicy_realization (weights : (p : Pool) → PMF (Parts p))
    (who : Player) :
    ((app).policyMixture (independentProduct weights) (fun plan =>
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who)).policy =
      (menu).decodeProfile initial horizon scheduler
        ((N).agentBehavior (N).playedInformation fallback
          (fun agent => (weights (pool agent)).bind
            ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) agent))) who := by
  funext past view
  rw [ReactiveApplication.policyMixture_policy]
  by_cases present : some (past, view) ∈ (N).playedInformation who
  · let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    obtain ⟨remainder, product⟩ := phaseTimingPlanPolicy_posterior setup mode runtime leaks
      bounds initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded weights who past view present
    have marginal : (((app).policyMixture (independentProduct weights)
        (fun plan =>
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who)).posterior past).map
          (fun plan => plan (pool current)) =
        weights (pool current) := by
      have evaluated := congrArg (PMF.map Prod.fst) product
      simp only [PMF.map_comp, PMF.map_bind] at evaluated
      change _ = (weights (pool current)).bind
        (fun part => remainder.map (Function.const _ part)) at evaluated
      simp only [Function.comp_def, Equiv.piSplitAt_apply] at evaluated
      simpa only [PMF.map_const, PMF.bind_pure] using evaluated
    have atCurrent (plan : (p : Pool) → Parts p) :
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who past view =
        ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) current (plan (pool current))).map
          (fun choice => choice.1.getD ⟨none⟩) := by
      rw [member_apply, dite_eq_left present]
    simp_rw [atCurrent]
    have evaluatedBind := congrArg (fun law => law.bind (fun part =>
      ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded) current part).map (fun choice => choice.1.getD ⟨none⟩))) marginal
    rw [PMF.bind_map] at evaluatedBind
    change _ = _ at evaluatedBind
    refine evaluatedBind.trans ?_
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
      InformationModel.agentBehavior, dite_eq_left present, PMF.map_bind]
    rfl
  · have unchanged (plan : (p : Pool) → Parts p) :
        (phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded) plan who past view =
        PMF.pure ((fallback who (some (past, view))).1.getD ⟨none⟩) := by
      rw [member_apply, dite_eq_right present, PMF.pure_map]
    simp_rw [unchanged]
    rw [PMF.bind_const]
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, InformationModel.agentBehavior,
      dite_eq_right present, PMF.pure_map]
    rfl

open Classical in
/-- The SAME actual assembled assessment is realized by the original private
pool plans. The joint law retains every owner's plan and the entire physical
execution, rather than only a response or final-state marginal. -/
theorem phaseTimingAssessment_runRounds_joint
    (weights : (p : Pool) → PMF (Parts p)) (assessment : (N).BehavioralAssessment)
    (assembled : assessment.strategy = (N).agentBehavior (N).playedInformation fallback
      (fun agent => (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent)))
    (count : Nat) (execution : (app).Execution) :
    let members := fun owner plan => phaseTimingPlanPolicy setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan owner
    let posterior := fun current : (app).Execution => independentProduct (fun owner =>
      ((app).policyMixture (independentProduct weights) (members owner)).posterior
        (current.recall owner))
    (posterior execution).bind (fun plans =>
      ((app).runRounds scheduler (fun owner => members owner (plans owner)) count execution).map
        (fun final => (final, plans))) =
      ((app).runRounds scheduler
        ((menu).decodeProfile initial horizon scheduler assessment.strategy) count execution).bind
          (fun final => (posterior final).map (Prod.mk final)) := by
  intro members posterior
  have realized : (fun owner => ((app).policyMixture (independentProduct weights)
      (members owner)).policy) =
      (menu).decodeProfile initial horizon scheduler assessment.strategy := by
    rw [assembled]
    funext owner
    exact phaseTimingPlanPolicy_realization setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded weights owner
  have joint := (app).runRounds_policyMixtures_posterior_joint scheduler
    (fun _ => independentProduct weights) members count execution
  rwa [realized] at joint

open Classical in
/-- Conditioning the ORIGINAL private-plan run on an actual complete owner
input leaves its current pool part independent of the entire execution,
all other owners' plans, and every other part of its own plan. -/
theorem phaseTimingAssessment_observation_posterior
    (weights : (p : Pool) → PMF (Parts p)) (assessment : (N).BehavioralAssessment)
    (assembled : assessment.strategy = (N).agentBehavior (N).playedInformation fallback
      (fun agent => (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent)))
    (count : Nat) (execution : (app).Execution) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who) :
    let current : Agent := ⟨who, ⟨some (past, view), played⟩⟩
    let members := fun owner plan => phaseTimingPlanPolicy setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan owner
    let posteriors := fun actual : (app).Execution => independentProduct (fun owner =>
      ((app).policyMixture (independentProduct weights) (members owner)).posterior
        (actual.recall owner))
    let law := (app).runRounds scheduler
      ((menu).decodeProfile initial horizon scheduler assessment.strategy) count execution
    let joint := (posteriors execution).bind (fun plans =>
      ((app).runRounds scheduler (fun owner => members owner (plans owner)) count execution).map
        (fun final => (final, plans)))
    let observe := fun actual : (app).Execution => (actual.recall who, actual.observe (app) who)
    (past, view) ∈ (law.map observe).support →
    ∃ remainder : PMF (((p : {p // p ≠ pool current}) → Parts p.val) ×
        ((app).Execution × ((owner : {owner // owner ≠ who}) → (p : Pool) → Parts p))),
      (fiberPosterior joint (fun pair => observe pair.1) (past, view)).map
        (fun pair => (pair.2 who (pool current),
          ((fun p : {p // p ≠ pool current} => pair.2 who p.val),
            (pair.1, fun owner : {owner // owner ≠ who} => pair.2 owner.val)))) =
        (weights (pool current)).bind (fun part => remainder.map (Prod.mk part)) := by
  intro current members posteriors law joint observe observed
  let factors := fun (actual : (app).Execution) (owner : Player) =>
    ((app).policyMixture (independentProduct weights) (members owner)).posterior
      (actual.recall owner)
  let common := ((app).policyMixture (independentProduct weights) (members who)).posterior past
  have originalJoint := phaseTimingAssessment_runRounds_joint setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded weights assessment assembled count execution
  change joint = law.bind (fun final => (posteriors final).map (Prod.mk final)) at originalJoint
  have fixed : ∀ actual ∈ (fiberPosterior law observe (past, view)).support,
      factors actual who = common := by
    intro actual supported
    have equal := (mem_support_fiberPosterior observed supported).1
    have recallEq := congrArg Prod.fst equal
    change actual.recall who = past at recallEq
    simp only [factors, common, recallEq]
  have ownerProduct := fiberPosterior_tagged_product_splitAt law posteriors observe (past, view)
    observed factors (fun _ _ => rfl) who common fixed
  rw [← originalJoint] at ownerProduct
  obtain ⟨restLaw, currentProduct⟩ := phaseTimingPlanPolicy_posterior setup mode runtime leaks
    bounds initial horizon scheduler bound fallback wellFormed source noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded weights who past view played
  let others := (fiberPosterior law observe (past, view)).bind fun actual =>
    (independentProduct (fun owner : {owner // owner ≠ who} => factors actual owner.val)).map
      (Prod.mk actual)
  change _ = common.bind (fun plan => others.map (Prod.mk plan)) at ownerProduct
  let read := fun pair : ((p : Pool) → Parts p) ×
      ((app).Execution × ((owner : {owner // owner ≠ who}) → (p : Pool) → Parts p)) =>
    (pair.1 (pool current), ((fun p : {p // p ≠ pool current} => pair.1 p.val), pair.2))
  have projected := congrArg (PMF.map read) ownerProduct
  simp only [PMF.map_comp, PMF.map_bind] at projected
  refine ⟨restLaw.bind (fun rest => others.map (Prod.mk rest)), projected.trans ?_⟩
  have combined := congrArg (fun distribution => distribution.bind (fun pair =>
    others.map (fun other => (pair.1, (pair.2, other))))) currentProduct
  simpa only [PMF.bind_map, PMF.bind_bind, PMF.map_bind, PMF.map_comp, Function.comp_def,
    Equiv.piSplitAt_apply, read, common] using combined

end Vegas
