/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRawBindingContribution

/-! # One marked raw-mixture send in actual own-action prefixes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- One selected raw-tier contribution at the specified actual own record.
All earlier and later factors use the full same native behavioral strategy. -/
def phaseRawMixtureOwnPlayWeight (noise : ℝ) (who : Player) (policy : (N).BehavioralPolicy who)
    (before : List ((N).InfoState who × (E).Action who))
    (marked : (N).InfoState who × (E).Action who)
    (after : List ((N).InfoState who × (E).Action who)) : ℝ :=
  (N).ownPlayReachProbability policy before *
    phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler noise who marked *
      (N).ownPlayReachProbability policy after

private theorem ownPlayReachProbability_append (who : Player) (policy : (N).BehavioralPolicy who)
    (first second : List ((N).InfoState who × (E).Action who)) :
    (N).ownPlayReachProbability policy (first ++ second) =
      (N).ownPlayReachProbability policy first * (N).ownPlayReachProbability policy second := by
  induction first with
  | nil => simp [InformationModel.ownPlayReachProbability]
  | cons first rest ih =>
      simp only [List.cons_append, InformationModel.ownPlayReachProbability, ih]
      ring

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

/-- Distributing the actual marked local mixture produces exactly the raw
contribution and the remaining source/slot contribution. Accepted source
failures are in the latter; they are not declared negligible. -/
theorem phase_marked_ownPlay_decomposition (n : Nat)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (before after : List ((N).InfoState who × (E).Action who))
    (marked : (N).InfoState who × (E).Action who) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseBounded
        slotWeight slotNonnegative slotBounded
    let conditional := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler who marked.1)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler who marked.1)
    (N).ownPlayReachProbability (strategy who) (before ++ marked :: after) =
      phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon scheduler noise who
        (strategy who) before marked after +
      (N).ownPlayReachProbability (strategy who) before *
        ((1 - noise) * ((conditional.map Subtype.val) (some marked.2)).toReal) *
          (N).ownPlayReachProbability (strategy who) after := by
  intro strategy conditional
  rw [ownPlayReachProbability_append, InformationModel.ownPlayReachProbability]
  have split := phaseSourcePerturbedStrategy_raw_decomposition setup mode runtime leaks bounds plan
    horizon scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded who marked
  rw [split]
  dsimp only [phaseRawMixtureOwnPlayWeight]
  ring

include maximal

/-- Exactly one raw-mixture binding send contributes the extra noise factor.
The chronological segments and the marked callback are witnessed by actual
initialized histories; no likelihood inequality is a hypothesis. -/
theorem phase_raw_playerReach_prefix_of_floor
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
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
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded
    (sendsBefore + sendsAfter + 1) + (waitsBefore + waitsAfter) ≤ 2 * horizon + 1 ∧
    phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon scheduler noise who
        (strategy who) firstBefore firstMarked firstAfter ≤
      noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (sendsBefore + sendsAfter + 1) *
        (1 + noise / ((1 - noise) * floor)) ^ (waitsBefore + waitsAfter) *
          (N).playerReachProbability strategy who second.trace ∧
    phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon scheduler noise who
        (strategy who) firstBefore firstMarked firstAfter ≤
      noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1) *
        (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1) *
          (N).playerReachProbability strategy who second.trace := by
  intro strategy
  have ordinary := markedPair.toSendingPair setup mode runtime leaks bounds plan horizon scheduler
    who firstMarked secondMarked
  have combined := beforePair.append setup mode runtime leaks bounds plan horizon scheduler
    (PhaseRepairOwnPlay.sending ordinary afterPair)
  have paired : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      ((N).ownPlay who first.trace) ((N).ownPlay who second.trace)
        (sendsBefore + (sendsAfter + 1)) (waitsBefore + waitsAfter) := by
    rw [firstRecords, secondRecords]
    exact combined
  have count := (phase_playerReach_repair_prefix_of_floor setup mode runtime leaks bounds plan
    horizon scheduler finite wellFormed target approximation maximal n capacity floor positive
      floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded who first second
        _ _ paired).1
  have countBound : (sendsBefore + sendsAfter + 1) + (waitsBefore + waitsAfter) ≤
      2 * horizon + 1 := by omega
  have beforeBound := beforePair.reach_ratio setup mode runtime leaks bounds plan horizon scheduler
    finite wellFormed target approximation maximal n capacity floor positive floored noise
      noiseNonnegative noiseSmall slotWeight slotPositive slotBounded who _ _ _ _
  have afterBound := afterPair.reach_ratio setup mode runtime leaks bounds plan horizon scheduler
    finite wellFormed target approximation maximal n capacity floor positive floored noise
      noiseNonnegative noiseSmall slotWeight slotPositive slotBounded who _ _ _ _
  have markedResult := markedPair.raw_ratio setup mode runtime leaks bounds plan horizon scheduler
    wellFormed maximal (approximation.sequence n) (approximation.mixed n) floor positive floored
      noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded who _ _
  have markedBound := markedResult.2
  have beforeTarget := (N).ownPlayReachProbability_nonneg (strategy who) secondBefore
  have afterSource := (N).ownPlayReachProbability_nonneg (strategy who) firstAfter
  have markedSource : 0 ≤ phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler
      noise who firstMarked := mul_nonneg noiseNonnegative ENNReal.toReal_nonneg
  have firstUpper : 0 ≤
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^ sendsBefore *
        (1 + noise / ((1 - noise) * floor)) ^ waitsBefore *
          (N).ownPlayReachProbability (strategy who) secondBefore := by positivity
  have markedUpper : 0 ≤ noise *
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
        (((strategy who secondMarked.1).map Subtype.val) (some secondMarked.2)).toReal := by
    positivity
  have firstProduct := mul_le_mul beforeBound markedBound markedSource firstUpper
  have product := mul_le_mul firstProduct afterBound afterSource (mul_nonneg firstUpper markedUpper)
  have counted : phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon
      scheduler noise who (strategy who) firstBefore firstMarked firstAfter ≤
      noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (sendsBefore + sendsAfter + 1) *
        (1 + noise / ((1 - noise) * floor)) ^ (waitsBefore + waitsAfter) *
          (N).playerReachProbability strategy who second.trace := by
    rw [(N).playerReachProbability_eq_ownPlayReachProbability, secondRecords,
      ownPlayReachProbability_append, InformationModel.ownPlayReachProbability]
    dsimp only [phaseRawMixtureOwnPlayWeight]
    apply product.trans_eq
    rw [pow_add, pow_add, pow_succ]
    ring
  refine ⟨countBound, counted, ?_⟩
  have sendPower := pow_le_pow_right₀ markedResult.1
    (show sendsBefore + sendsAfter + 1 ≤ 2 * horizon + 1 by omega)
  have waitingOneLe : 1 ≤ 1 + noise / ((1 - noise) * floor) := by
    have quotient : 0 ≤ noise / ((1 - noise) * floor) := by positivity
    linarith
  have waitPower := pow_le_pow_right₀ waitingOneLe
    (show waitsBefore + waitsAfter ≤ 2 * horizon + 1 by omega)
  have coefficient := mul_le_mul sendPower waitPower
    (by positivity : 0 ≤ (1 + noise / ((1 - noise) * floor)) ^ (waitsBefore + waitsAfter))
    (by positivity : 0 ≤ ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
      (2 * horizon + 1))
  have targetNonnegative : 0 ≤ (N).playerReachProbability strategy who second.trace := by
    rw [(N).playerReachProbability_eq_ownPlayReachProbability]
    exact (N).ownPlayReachProbability_nonneg _ _
  have scaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left coefficient noiseNonnegative) targetNonnegative
  exact counted.trans (by convert scaled using 1 <;> ring)

end Vegas
