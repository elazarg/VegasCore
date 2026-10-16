/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingMarkedBindingFiber
import Vegas.Game.PhaseOpponentRawBindingMass

/-! # All-opponent raw-send bounds for actual timing mixtures -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)


variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))) scheduler]

local instance (focal : Player) (site : (N).InformationSite focal) :
    Fintype ((N).InformationHistory focal site.1) := Fintype.ofFinite _

include maximal nature in
open Classical in
private theorem phase_timing_raw_position_fiber_mass_le
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
            slotPositive.le
            slotBounded agent))
    (covered : bounds.CoversOutputValues) (owner focal : Player) (different : focal ≠ owner)
    (site : (N).InformationSite focal) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (genuine : ∀ history : (N).InformationHistory focal site.1,
      ∃ control : (phaseApplication runtime leaks).Control,
        history.1.state = some control ∧ control.actor = some focal ∧
          control.execution.application.current.excluded = ∅ ∧
          control.execution.application.SeedRequest focal
            ⟨control.execution.application.attempt, event⟩) (index : Nat) :
    (∑ history : (N).InformationHistory focal site.1,
      phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
        owner strategy history.1 index) ≤
      (Nat.card (E).History : ℝ) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1)) *
            ((N).informationMass strategy focal site).toReal := by
  let before := fun history : (N).InformationHistory focal site.1 =>
    ((N).ownPlay owner history.1.trace).take index
  let marked := fun history : (N).InformationHistory focal site.1 =>
    phaseOwnRecordAt setup mode runtime leaks bounds plan horizon scheduler owner history.1 index
  let after := fun history : (N).InformationHistory focal site.1 =>
    (((N).ownPlay owner history.1.trace).drop index).tail
  let histories := Finset.univ.filter fun history : (N).InformationHistory focal site.1 =>
    phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
      (marked history)
  obtain ⟨repair, bound⟩ := phase_timing_raw_binding_fiber_mass_le setup mode runtime leaks bounds
    plan maximal
    horizon scheduler bound finite wellFormed target approximation n capacity floor positive
      floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights
        strategy assembled covered owner focal
        different site event payload output histories (fun history _ => genuine history)
          before after marked (fun history member =>
            phase_position_records setup mode runtime leaks bounds plan horizon scheduler owner
              history.1 index (Finset.mem_filter.mp member).2)
          (fun _ member => (Finset.mem_filter.mp member).2)
  have targetLe : InformationModel.finiteHistoryReach (M := N) strategy focal site
      (histories.image repair) ≤ ((N).informationMass strategy focal site).toReal := by
    rw [InformationModel.informationMass_toReal_eq_sum]
    unfold InformationModel.finiteHistoryReach
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => ENNReal.toReal_nonneg)
  have scaled := bound.trans (mul_le_mul_of_nonneg_left targetLe (by positivity))
  dsimp only [histories] at scaled
  rw [Finset.sum_filter] at scaled
  simpa only [phaseRawBindingPositionWeight, before, after, marked] using scaled

include maximal nature in
theorem phase_timing_opponent_raw_binding_mass_le
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
            slotPositive.le
            slotBounded agent))
    (covered : bounds.CoversOutputValues) (focal : Player) (site : (N).InformationSite focal)
    (original : (phaseApplication runtime leaks).Control)
    (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf focal originalTrace = site.1) (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    phaseOpponentRawBindingMass setup mode runtime leaks bounds plan horizon scheduler noise focal
        strategy site ≤
      ((Fintype.card Player : ℝ) * (2 * horizon + 1) * Nat.card (E).History) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1)) *
            ((N).informationMass strategy focal site).toReal := by
  classical
  have genuine := phase_binding_fiber_genuine setup mode runtime leaks bounds plan horizon scheduler
    focal site original originalTrace atSite active event clear request
  let common := (Nat.card (E).History : ℝ) *
    (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
      (2 * horizon + 1)) *
        ((N).informationMass strategy focal site).toReal
  unfold phaseOpponentRawBindingMass
  calc (∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        ∑ history : (N).InformationHistory focal site.1,
          phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
            owner strategy history.1 index)
      ≤ ∑ _owner ∈ Finset.univ.erase focal, ∑ _index ∈ Finset.range (2 * horizon + 1),
          common := by
        apply Finset.sum_le_sum
        intro owner member
        apply Finset.sum_le_sum
        intro index _inside
        exact phase_timing_raw_position_fiber_mass_le setup mode runtime leaks bounds plan maximal
          horizon scheduler bound finite wellFormed target approximation n capacity floor positive
            floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights
              strategy assembled covered owner
              focal
              (Ne.symm (Finset.mem_erase.mp member).1) site event payload output genuine index
    _ = ((Finset.univ.erase focal).card : ℝ) * ((2 * horizon + 1) * common) := by simp
    _ ≤ (Fintype.card Player : ℝ) * ((2 * horizon + 1) * common) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp only [common]; positivity)
      exact_mod_cast Finset.card_le_univ (Finset.univ.erase focal)
    _ = _ := by dsimp only [common]; ring

include maximal nature in
/-- All opponent positions have a uniform normalized RAW-send bound under
the actual arbitrary-weight timing strategy, including information fibers with
zero mass. Source failures and all non-RAW tiers remain ordinary probability. -/
theorem phase_timing_opponent_raw_binding_share_le
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
            slotPositive.le
            slotBounded agent))
    (covered : bounds.CoversOutputValues) (focal : Player) (site : (N).InformationSite focal)
    (original : (phaseApplication runtime leaks).Control)
    (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf focal originalTrace = site.1) (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    0 ≤ phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler noise
        focal strategy site ∧
      phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler noise
        focal strategy site ≤
      ((Fintype.card Player : ℝ) * (2 * horizon + 1) * Nat.card (E).History) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1)) := by
  constructor
  · unfold phaseOpponentRawBindingShare phaseOpponentRawBindingMass
    apply div_nonneg _ ENNReal.toReal_nonneg
    apply Finset.sum_nonneg
    intro owner _member
    apply Finset.sum_nonneg
    intro index _inside
    apply Finset.sum_nonneg
    intro history _member
    exact phaseRawBindingPositionWeight_nonneg setup mode runtime leaks bounds plan horizon
      scheduler noise noiseNonnegative owner strategy history.1 index
  · by_cases zeroMass : ((N).informationMass strategy focal site).toReal = 0
    · simp only [phaseOpponentRawBindingShare, zeroMass, div_zero]
      positivity
    · have massPositive : 0 < ((N).informationMass strategy focal site).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm zeroMass)
      unfold phaseOpponentRawBindingShare
      rw [div_le_iff₀ massPositive]
      exact phase_timing_opponent_raw_binding_mass_le setup mode runtime leaks bounds plan maximal
        horizon scheduler bound finite wellFormed target approximation n capacity floor positive
          floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights
            strategy assembled covered focal site original originalTrace atSite active event
              payload output clear request

end Vegas
