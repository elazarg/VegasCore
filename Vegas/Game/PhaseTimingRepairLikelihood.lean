/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingRepairResponseFactor
import Vegas.Game.PhaseTimingOpeningFactor
import Vegas.Game.PhaseMarkedRepairMass

/-! # Whole chronological likelihood for actual timing mixtures -/

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

include maximal

/-- Actual arbitrary-weight timing mixtures bound the entire chronological
own-response product. The source omission floor covers every WAIT; genuine
opening and inert records have identical factors. -/
theorem PhaseRepairOwnPlay.timing_reach_ratio
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
    (slotsPositive : 0 < bounds.candidateCount)
    (who : Player)
    (firstRecords secondRecords : List ((N).InfoState who × (E).Action who)) (sends waits : Nat)
    (paired : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstRecords secondRecords sends waits) :
    (N).ownPlayReachProbability (strategy who) firstRecords ≤
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^ (sends + waits) *
        (N).ownPlayReachProbability (strategy who) secondRecords := by
  let coefficient := (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)
  have nonnegative : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have oneSlot : (1 : ℝ) ≤ bounds.candidateCount := by
    exact_mod_cast (show 1 ≤ bounds.candidateCount by omega)
  have waitBound : 1 / ((1 - noise) * slotWeight * floor) ≤ coefficient :=
    div_le_div_of_nonneg_right oneSlot (by positivity)
  induction paired with
  | nil => simp [InformationModel.ownPlayReachProbability]
  | @sending firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
    have head := phaseBindingSendingPair.timing_record_ratio setup mode runtime leaks bounds plan
      maximal horizon scheduler bound wellFormed (approximation.sequence n) (approximation.mixed n)
        floor positive floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded
          weights strategy assembled who firstRecord secondRecord pair
    rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability]
    have product := mul_le_mul head ih ((N).ownPlayReachProbability_nonneg _ _)
      (mul_nonneg nonnegative ENNReal.toReal_nonneg)
    exact product.trans_eq (by
      rw [show sends + 1 + waits = (sends + waits) + 1 by omega, pow_succ]
      ring)
  | @waiting firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
    have head := phaseBindingWaitingPair.timing_record_ratio setup mode runtime leaks bounds plan
      maximal horizon scheduler bound wellFormed (approximation.sequence n) floor positive floored
        noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights strategy
          assembled finite target approximation n rfl capacity who firstRecord secondRecord pair
    have scaled := mul_le_mul_of_nonneg_right waitBound
      (show 0 ≤ (((strategy who secondRecord.1).map Subtype.val) (some secondRecord.2)).toReal
        from ENNReal.toReal_nonneg)
    have headBound := head.trans scaled
    rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability]
    have product := mul_le_mul headBound ih ((N).ownPlayReachProbability_nonneg _ _)
      (mul_nonneg nonnegative ENNReal.toReal_nonneg)
    exact product.trans_eq (by
      rw [show sends + (waits + 1) = (sends + waits) + 1 by omega, pow_succ]
      ring)
  | @opening firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
    have head := phaseOpeningResponsePair.timing_record_eq setup mode runtime leaks bounds plan
      maximal horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
        noiseSmall.le slotWeight slotPositive.le slotBounded weights strategy assembled who
          firstRecord secondRecord pair
    rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability, head]
    exact (mul_le_mul_of_nonneg_left ih ENNReal.toReal_nonneg).trans_eq (by ring)
  | @inert firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
    have head := phaseInertResponsePair.record_eq setup mode runtime leaks bounds plan horizon
      scheduler strategy who firstRecord secondRecord pair
    rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability, head]
    exact (mul_le_mul_of_nonneg_left ih ENNReal.toReal_nonneg).trans_eq (by ring)

/-- One marked raw send contributes its extra noise factor under the same
actual strategy. The total send-and-WAIT exponent is bounded by the original
physical horizon, retaining every callback and possible retry. -/
theorem phase_timing_raw_playerReach_prefix_of_floor
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
    (who : Player) (first second : (E).History)
    (firstBefore firstAfter secondBefore secondAfter : List ((N).InfoState who × (E).Action who))
    (firstMarked secondMarked : (N).InfoState who × (E).Action who)
    (firstRecords : (N).ownPlay who first.trace = firstBefore ++ firstMarked :: firstAfter)
    (secondRecords : (N).ownPlay who second.trace = secondBefore ++ secondMarked :: secondAfter)
    (sendsBefore waitsBefore sendsAfter waitsAfter : Nat)
    (beforePair : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstBefore secondBefore sendsBefore waitsBefore)
    (markedPair : phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler
      who firstMarked secondMarked)
    (afterPair : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstAfter secondAfter sendsAfter waitsAfter) :
    phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon scheduler noise who
        (strategy who) firstBefore firstMarked firstAfter ≤
      noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1) * (N).playerReachProbability strategy who second.trace := by
  have count := (phase_raw_playerReach_prefix_of_floor setup mode runtime leaks bounds plan horizon
    scheduler finite wellFormed target approximation maximal n capacity floor positive floored noise
      noiseNonnegative noiseSmall slotWeight slotPositive slotBounded who first second firstBefore
        firstAfter secondBefore secondAfter firstMarked secondMarked firstRecords secondRecords
          sendsBefore waitsBefore sendsAfter waitsAfter beforePair markedPair afterPair).1
  have markedResult := phaseRawBindingSendingPair.timing_raw_ratio setup mode runtime leaks bounds
    plan maximal horizon scheduler bound wellFormed (approximation.sequence n)
      (approximation.mixed n)
      floor positive floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded
        weights strategy assembled who firstMarked secondMarked markedPair
  have slotsPositive : 0 < bounds.candidateCount := by
    by_contra absent
    have empty : bounds.candidateCount = 0 := by omega
    simp only [empty, Nat.cast_zero, zero_div] at markedResult
    linarith [markedResult.1]
  have beforeBound := beforePair.timing_reach_ratio setup mode runtime leaks bounds plan maximal
    horizon scheduler bound finite wellFormed target approximation n capacity floor positive floored
      noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights strategy
        assembled slotsPositive who _ _ _ _
  have afterBound := afterPair.timing_reach_ratio setup mode runtime leaks bounds plan maximal
    horizon scheduler bound finite wellFormed target approximation n capacity floor positive floored
      noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights strategy
        assembled slotsPositive who _ _ _ _
  let coefficient := (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)
  have beforeTarget := (N).ownPlayReachProbability_nonneg (strategy who) secondBefore
  have firstUpper : 0 ≤ coefficient ^ (sendsBefore + waitsBefore) *
      (N).ownPlayReachProbability (strategy who) secondBefore := by positivity
  have markedUpper : 0 ≤ noise * coefficient *
      (((strategy who secondMarked.1).map Subtype.val) (some secondMarked.2)).toReal := by
    positivity
  have markedSource : 0 ≤ phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler
      noise who firstMarked := mul_nonneg noiseNonnegative ENNReal.toReal_nonneg
  have firstProduct := mul_le_mul beforeBound markedResult.2 markedSource firstUpper
  have product := mul_le_mul firstProduct afterBound
    ((N).ownPlayReachProbability_nonneg _ _) (mul_nonneg firstUpper markedUpper)
  have counted : phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon scheduler
      noise who (strategy who) firstBefore firstMarked firstAfter ≤
        noise * coefficient ^ ((sendsBefore + sendsAfter + 1) + (waitsBefore + waitsAfter)) *
          (N).playerReachProbability strategy who second.trace := by
    rw [(N).playerReachProbability_eq_ownPlayReachProbability, secondRecords,
      ownPlayReachProbability_append, InformationModel.ownPlayReachProbability]
    dsimp only [phaseRawMixtureOwnPlayWeight]
    apply product.trans_eq
    rw [show (sendsBefore + sendsAfter + 1) + (waitsBefore + waitsAfter) =
      (sendsBefore + waitsBefore) + (sendsAfter + waitsAfter) + 1 by omega,
        pow_succ, pow_add]
    ring
  have powers := pow_le_pow_right₀ markedResult.1 count
  have targetNonnegative : 0 ≤ (N).playerReachProbability strategy who second.trace := by
    rw [(N).playerReachProbability_eq_ownPlayReachProbability]
    exact (N).ownPlayReachProbability_nonneg _ _
  exact counted.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left powers noiseNonnegative) targetNonnegative)


/-- The operationally derived counterfactual equality lifts the actual timing
marked-own-product bound to the full original history reach. -/
theorem phase_timing_raw_historyReach_prefix_of_floor
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
    (who : Player) (first second : (E).History)
    (firstBefore firstAfter secondBefore secondAfter : List ((N).InfoState who × (E).Action who))
    (firstMarked secondMarked : (N).InfoState who × (E).Action who)
    (firstRecords : (N).ownPlay who first.trace = firstBefore ++ firstMarked :: firstAfter)
    (secondRecords : (N).ownPlay who second.trace = secondBefore ++ secondMarked :: secondAfter)
    (sendsBefore waitsBefore sendsAfter waitsAfter : Nat)
    (beforePair : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstBefore secondBefore sendsBefore waitsBefore)
    (markedPair : phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler
      who firstMarked secondMarked)
    (afterPair : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstAfter secondAfter sendsAfter waitsAfter)
    (counterfactual : (N).counterfactualReachProbability strategy who first.trace =
      (N).counterfactualReachProbability strategy who second.trace) :
    phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler noise who
        strategy first firstBefore firstMarked firstAfter ≤
      (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
        (2 * horizon + 1)) * ((N).historyReachWeight strategy second).toReal := by
  have bound := phase_timing_raw_playerReach_prefix_of_floor setup mode runtime leaks bounds plan
    maximal horizon scheduler bound finite wellFormed target approximation n capacity floor positive
      floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded weights strategy
        assembled who first second firstBefore firstAfter secondBefore secondAfter firstMarked
          secondMarked firstRecords secondRecords sendsBefore waitsBefore sendsAfter waitsAfter
            beforePair markedPair afterPair
  have scaled := mul_le_mul_of_nonneg_right bound
    ((N).counterfactualReachProbability_nonneg strategy who first.trace)
  dsimp only [phaseMarkedHistoryWeight]
  rw [counterfactual, mul_assoc] at scaled
  rw [← (N).historyReachProbability_eq_player_mul_counterfactual strategy who second.trace]
    at scaled
  simpa only [counterfactual] using scaled

end Vegas
