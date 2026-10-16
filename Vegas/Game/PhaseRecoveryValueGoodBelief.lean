/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueGoodConditional
import Vegas.Game.PhaseRecoveryValueBelief
import Vegas.Game.PhaseTimingRawBindingLimit

/-! # Actual common Bayes approximation by retained original-memory weights -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [goodBeliefHistories : Fintype
    ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [goodBeliefInputEquality : ∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "nativeInitial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw))
local notation "M" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) nativeInitial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueGoodBeliefPoolFintype : Fintype Pool := Fintype.ofFinite _

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)))
    scheduler]

omit goodBeliefHistories goodBeliefInputEquality in
open Classical in
private theorem markerMass_cast
    (old : PMF (phaseApplication runtime leaks).State) (oldLaw : old = nativeInitial)
    (focal : Player)
    (profile : ∀ who, ((menu).information old horizon scheduler).BehavioralPolicy who)
    (site : ((menu).information old horizon scheduler).InformationSite focal)
    [Fintype (((menu).information old horizon scheduler).InformationHistory focal site.1)]
    (noise : ℝ) :
    (∑ history : ((menu).information old horizon scheduler).InformationHistory focal site.1,
      ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
          scheduler noise owner (oldLaw ▸ profile) (oldLaw ▸ history.1) index) =
      phaseOpponentRawBindingMass setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise focal (oldLaw ▸ profile) (oldLaw ▸ site) := by
  subst old
  simp only [phaseOpponentRawBindingMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro owner _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr (by ext history; simp)
  intro history _
  rfl

omit goodBeliefHistories goodBeliefInputEquality nature in
private theorem informationMass_cast
    (old : PMF (phaseApplication runtime leaks).State) (oldLaw : old = nativeInitial)
    (focal : Player)
    (profile : ∀ who, ((menu).information old horizon scheduler).BehavioralPolicy who)
    (site : ((menu).information old horizon scheduler).InformationSite focal) :
    ((menu).information old horizon scheduler).informationMass profile focal site =
      (M).informationMass (oldLaw ▸ profile) focal (oldLaw ▸ site) := by
  subst old
  rfl

omit goodBeliefHistories goodBeliefInputEquality nature in
open Classical in
private theorem fixed_focal_mixture {Memory : Player → Type}
    (priors : ∀ who, PMF (Memory who)) (members : ∀ who, Memory who → (app).Policy)
    (allCovered : ∀ who memory past view response,
      response ∈ (members who memory past view).support →
      response ∈ (menu).actions who past view) (focal : Player) :
    let raw := fun who => ((app).policyMixture (priors who) (members who)).policy
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who (raw who)
    let family := fun who memory => if who = focal then raw focal else members who memory
    let behavior := fun who => (menu).restrictPolicy initial horizon scheduler who
      ((app).policyMixture (priors who) (family who)).policy
    (∀ past view response, response ∈ (raw focal past view).support →
      response ∈ (menu).actions focal past view) ∧ behavior = first := by
  intro raw first family behavior
  refine ⟨?_, ?_⟩
  · intro past view response supported
    change response ∈ (((app).policyMixture (priors focal) (members focal)).policy
      past view).support at supported
    rw [ReactiveApplication.policyMixture_policy] at supported
    obtain ⟨memory, _, present⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    exact allCovered focal memory past view response present
  · funext who
    apply congrArg ((menu).restrictPolicy initial horizon scheduler who)
    funext past view
    by_cases same : who = focal
    · subst who
      rw [ReactiveApplication.policyMixture_policy]
      simp only [family, ↓reduceIte, PMF.bind_const]
    · simp only [family, ite_eq_right same]
      rfl

open Classical in
private theorem original_good_conditional
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (focal : Player) (site : (N).InformationSite focal)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let raw := fun who => ((app).policyMixture (priors who) (members who)).policy
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who (raw who)
    let lawEq : initial = nativeInitial := by
      simpa only [Function.comp_def] using
        PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial runtimePlan)
    let nativeFirst : ∀ who, (M).BehavioralPolicy who := lawEq ▸ first
    let nativeSite : (M).InformationSite focal := lawEq ▸ site
    let share := phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon
      scheduler noise focal nativeFirst nativeSite
    0 < ((N).informationMass first focal site).toReal → share < 1 →
    ∃ chance : (N).InformationHistory focal site.1 → ℝ,
      let good := fun history : (N).InformationHistory focal site.1 =>
        phaseTimingPlanPolicy_value_retainedWeight setup mode runtime leaks bounds runtimePlan
          initial horizon scheduler bound fallback wellFormed assessment finite weights noise
            noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded focal (raw focal)
              history.1 (chance history)
      (∀ history, 0 ≤ good history ∧
        good history ≤ ((N).historyReachWeight first history.1).toReal) ∧
        0 < ∑ history, good history ∧
        ∑ history, |((N).historyReachWeight first history.1).toReal /
          ((N).informationMass first focal site).toReal -
          good history / ∑ next, good next| ≤ 2 * share := by
  intro priors members raw first lawEq nativeFirst nativeSite share massPositive small
  let family := fun who memory => if who = focal then raw focal else members who memory
  let behavior := fun who => (menu).restrictPolicy initial horizon scheduler who
    ((app).policyMixture (priors who) (family who)).policy
  obtain ⟨covered, behaviorEq⟩ := fixed_focal_mixture setup mode runtime leaks bounds runtimePlan
    horizon scheduler priors members (fun who memory past view response present =>
      phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed _ noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded memory.1 who past view response present) focal
  have massEq : ((N).informationMass first focal site).toReal =
      ∑ history : (N).InformationHistory focal site.1,
        ((N).historyReachWeight first history.1).toReal :=
    (N).informationMass_toReal_eq_sum (who := focal) (site := site) first
  have cap := phaseTimingPlanPolicy_value_good_conditional setup mode runtime leaks bounds
    runtimePlan initial lawEq horizon scheduler bound maximal fallback wellFormed assessment mixed
      finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        focal (raw focal) covered site unflagged
  change let weight := fun history : (N).InformationHistory focal site.1 =>
      ((N).historyReachWeight behavior history.1).toReal
    let nativeBehavior : ∀ who, (M).BehavioralPolicy who := lawEq ▸ behavior
    let marks := fun history : (N).InformationHistory focal site.1 =>
      ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
          scheduler noise owner nativeBehavior (lawEq ▸ history.1) index
    _ at cap
  rw [behaviorEq] at cap
  have marksEq : (∑ history : (N).InformationHistory focal site.1,
      ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
          scheduler noise owner nativeFirst (lawEq ▸ history.1) index) =
      phaseOpponentRawBindingMass setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise focal nativeFirst nativeSite := by
    exact markerMass_cast setup mode runtime leaks bounds runtimePlan horizon scheduler initial
      lawEq focal first site noise
  have shareEq : share = (∑ history : (N).InformationHistory focal site.1,
      ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
          scheduler noise owner nativeFirst (lawEq ▸ history.1) index) /
      ∑ history : (N).InformationHistory focal site.1,
        ((N).historyReachWeight first history.1).toReal := by
    change phaseOpponentRawBindingMass setup mode runtime leaks bounds runtimePlan horizon
      scheduler noise focal nativeFirst nativeSite /
        ((M).informationMass nativeFirst focal nativeSite).toReal = _
    rw [← informationMass_cast setup mode runtime leaks bounds runtimePlan horizon scheduler
      initial lawEq focal first site, massEq, ← marksEq]
  have positiveSum : 0 < ∑ history : (N).InformationHistory focal site.1,
      ((N).historyReachWeight first history.1).toReal := by
    rw [← massEq]
    exact massPositive
  obtain ⟨chance, _, boundedGood, positiveGood, close⟩ := cap positiveSum
    ((div_lt_one positiveSum).mp (shareEq ▸ small))
  refine ⟨chance, boundedGood, positiveGood, ?_⟩
  simpa only [massEq, shareEq, mul_div_assoc] using close

open Classical in
/-- The SAME actual clear-input Bayes belief is close to the explicitly retained
ORIGINAL-memory weight. Only foreign binding-SEND RAW mass is removed. -/
theorem phaseTimingPlanPolicy_value_good_belief
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (actual : (N).BehavioralAssessment)
    (assembled : ∀ who (site : (N).InformationSite who),
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
      actual.strategy who site.1 = ((N).agentBehavior (N).playedInformation fallback
        (fun agent => (weights (pool agent)).bind
          (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
              slotBounded agent))) who site.1)
    (actualMixed : actual.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent (N) actual
      ((menu).decisionInformationAntichain initial horizon scheduler))
    (focal : Player) (site : (N).InformationSite focal)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let raw := fun who => ((app).policyMixture (priors who) (members who)).policy
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who (raw who)
    let lawEq : initial = nativeInitial := by
      simpa only [Function.comp_def] using
        PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial runtimePlan)
    let nativeFirst : ∀ who, (M).BehavioralPolicy who := lawEq ▸ first
    let nativeSite : (M).InformationSite focal := lawEq ▸ site
    let share := phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon
      scheduler noise focal nativeFirst nativeSite
    share < 1 →
    ∃ chance : (N).InformationHistory focal site.1 → ℝ,
      let good := fun history : (N).InformationHistory focal site.1 =>
        phaseTimingPlanPolicy_value_retainedWeight setup mode runtime leaks bounds runtimePlan
          initial horizon scheduler bound fallback wellFormed assessment finite weights noise
            noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded focal (raw focal)
              history.1 (chance history)
      (∀ history, 0 ≤ good history ∧
        good history ≤ ((N).historyReachWeight first history.1).toReal) ∧
        0 < ∑ history, good history ∧
        ∑ history, |(actual.belief focal site history).toReal -
          good history / ∑ next, good next| ≤ 2 * share := by
  intro priors members raw first lawEq nativeFirst nativeSite share small
  have bayesRule := phaseTimingPlanPolicy_value_bayes_of_clear setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
        actualMixed bayes focal site unflagged
  have massPositive : 0 < ((N).informationMass first focal site).toReal :=
    ENNReal.toReal_pos bayesRule.2.1.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      ((N).informationMass_le_one first focal site
        ((menu).decisionInformationAntichain initial horizon scheduler focal site)))
  obtain ⟨chance, boundedGood, positiveGood, close⟩ :=
    original_good_conditional setup mode runtime leaks bounds runtimePlan horizon scheduler bound
      maximal fallback wellFormed assessment mixed finite weights noise noiseNonnegative
        noiseBounded
        slotWeight slotNonnegative slotBounded focal site unflagged massPositive small
  refine ⟨chance, boundedGood, positiveGood, ?_⟩
  have beliefEq (history : (N).InformationHistory focal site.1) :
      (actual.belief focal site history).toReal =
        ((N).historyReachWeight first history.1).toReal /
          ((N).informationMass first focal site).toReal := by
    rw [bayesRule.2.2 history, ENNReal.toReal_div]
  simpa only [beliefEq] using close

end Vegas
