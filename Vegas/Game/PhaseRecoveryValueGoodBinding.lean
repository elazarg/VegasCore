/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueGoodBelief
import Vegas.Game.PhaseCommonRawBindingLimit

/-! # Native binding-input Bayes error under the unchanged common profile -/

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
  [goodBindingHistories : Fintype
    ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [goodBindingInputEquality : ∀ who, DecidableEq
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

local instance phaseRecoveryValueGoodBindingPoolFintype : Fintype Pool := Fintype.ofFinite _

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)))
    scheduler]

omit goodBindingHistories goodBindingInputEquality in
open Classical in
private theorem clear_share_cast
    (old : PMF (phaseApplication runtime leaks).State) (oldLaw : old = nativeInitial)
    (first second : ∀ who, ((menu).information old horizon scheduler).BehavioralPolicy who)
    (agree : ∀ who (site : ((menu).information old horizon scheduler).InformationSite who),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 → first who site.1 = second who site.1)
    (mixed : ∀ who (site : ((menu).information old horizon scheduler).InformationSite who) choice,
      choice ∈ (second who site.1).support)
    (noise : ℝ) (focal : Player)
    (site : ((menu).information old horizon scheduler).InformationSite focal)
    (original : (app).Control)
    (trace : ((menu).protocol old horizon scheduler).Trace (some original))
    (atSite : ((menu).information old horizon scheduler).infoOf focal trace = site.1)
    (active : original.actor = some focal) (event : (serviceGraph setup mode).EventId)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon scheduler noise
      focal (oldLaw ▸ first) (oldLaw ▸ site) =
    phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon scheduler noise
      focal (oldLaw ▸ second) (oldLaw ▸ site) := by
  subst old
  exact (phase_clear_fiber_raw_share_eq setup mode runtime leaks bounds runtimePlan horizon
    scheduler
    first second agree mixed noise focal site original trace atSite active event clear request).2

open Classical in
/-- The SAME actual clear-input Bayes belief is close to the explicitly retained
ORIGINAL-memory weight. Only foreign binding-SEND RAW mass is removed. -/
theorem phaseTimingPlanPolicy_value_good_binding
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
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1)
    (original : (app).Control) (trace : (E).Trace (some original))
    (atSite : (N).infoOf focal trace = site.1) (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
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
    let nativeActual : ∀ who, (M).BehavioralPolicy who := lawEq ▸ actual.strategy
    let nativeSite : (M).InformationSite focal := lawEq ▸ site
    let share := phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon
      scheduler noise focal nativeActual nativeSite
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
  intro priors members raw first lawEq nativeActual nativeSite share small
  have agree := phaseTimingPlanPolicy_value_clear_profile_agreement setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
  have equality := clear_share_cast setup mode runtime leaks bounds runtimePlan horizon scheduler
    initial lawEq first actual.strategy agree actualMixed noise focal site original trace atSite
      active event clear request
  have cap := phaseTimingPlanPolicy_value_good_belief setup mode runtime leaks bounds runtimePlan
    horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
        actualMixed
        bayes focal site unflagged
  change (phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon
    scheduler noise focal (lawEq ▸ first) nativeSite < 1 → _) at cap
  rw [equality] at cap
  exact cap small

end Vegas
