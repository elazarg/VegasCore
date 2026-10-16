/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueStopped
import Interaction.ReactiveStoppedProfileMixture

/-! # Original global private tags in the actual stopped physical law -/

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
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
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
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The literal assembled stopped history law retains the SAME original
global source-policy and per-owner full timing-plan tags. At a later entry
their genuine own-recall posteriors remain, without refreshing either prior. -/
theorem phaseTimingPlanPolicy_value_stopped_memory_joint
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (extra : ((menu).protocol initial horizon scheduler).History → Prop)
    (start : ((menu).protocol initial horizon scheduler).History) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (pool agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded agent))
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => False
        | some current => current.execution.application.current.excluded ≠ ∅
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    (posteriors start).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) stopped start).map
          (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate profile stopped start).bind
        (fun final => (posteriors final).map (Prod.mk final)) := by
  intro priors members profile stopped posteriors
  have covered : ∀ who memory past view action, action ∈ (members who memory past view).support →
      action ∈ (menu).actions who past view := by
    intro who memory past view action supported
    exact phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
            past view action supported
  have joint := (menu).runUntil_policyMixtures_joint initial horizon scheduler certificate priors
    members covered stopped start
  have law := phaseTimingPlanPolicy_value_stopped_law setup mode runtime leaks bounds runtimePlan
    horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded certificate extra start
  exact joint.trans (congrArg (fun law => law.bind
    (fun final => (posteriors final).map (Prod.mk final))) law)

open Classical in
/-- From the original protocol initialization the tags are the ORIGINAL
global priors, sampled once before the original physical input draw. The
complete stopped history retains that draw and every original correlation. -/
theorem phaseTimingPlanPolicy_value_initial_memory_joint
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (extra : ((menu).protocol initial horizon scheduler).History → Prop) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (pool agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded agent))
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => False
        | some current => current.execution.application.current.excluded ≠ ∅
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    (independentProduct priors).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) stopped
          ((menu).protocol initial horizon scheduler).initHistory).map
            (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate profile stopped
        ((menu).protocol initial horizon scheduler).initHistory).bind
          (fun final => (posteriors final).map (Prod.mk final)) := by
  intro priors members profile stopped posteriors
  have joint := phaseTimingPlanPolicy_value_stopped_memory_joint setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded certificate extra
        ((menu).protocol initial horizon scheduler).initHistory
  exact joint

end Vegas
