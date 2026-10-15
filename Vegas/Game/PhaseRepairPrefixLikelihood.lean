/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairResponseFactor

/-! # Chronological finite-horizon response likelihood under directed repair -/

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

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

/-- Actual callback witnesses bound the whole chronological own-action product,
including arbitrary segments used around a marked raw-mixture send. -/
theorem PhaseRepairOwnPlay.reach_ratio
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player)
    (firstRecords secondRecords : List ((N).InfoState who × (E).Action who)) (sends waits : Nat)
    (paired : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstRecords secondRecords sends waits) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded
    (N).ownPlayReachProbability (strategy who) firstRecords ≤
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^ sends *
        (1 + noise / ((1 - noise) * floor)) ^ waits *
          (N).ownPlayReachProbability (strategy who) secondRecords := by
  intro strategy
  let sendRatio := (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)
  let waitRatio := 1 + noise / ((1 - noise) * floor)
  have sendNonnegative : 0 ≤ sendRatio := by dsimp [sendRatio]; positivity
  have waitNonnegative : 0 ≤ waitRatio := by dsimp [waitRatio]; positivity
  have products : ∀ {firstRecords secondRecords sends waits},
      PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who firstRecords
        secondRecords sends waits →
      (N).ownPlayReachProbability (strategy who) firstRecords ≤
        sendRatio ^ sends * waitRatio ^ waits *
          (N).ownPlayReachProbability (strategy who) secondRecords := by
    intro firstRecords secondRecords sends waits matched
    induction matched with
    | nil => simp [InformationModel.ownPlayReachProbability]
    | @sending firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
      have head := phaseBindingSendingPair.record_ratio setup mode runtime leaks bounds plan
        horizon scheduler wellFormed maximal (approximation.sequence n) (approximation.mixed n)
          floor positive floored noise noiseNonnegative noiseSmall slotWeight slotPositive
            slotBounded who firstRecord secondRecord pair
      rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability]
      have product := mul_le_mul head ih
        ((N).ownPlayReachProbability_nonneg _ _) (mul_nonneg sendNonnegative ENNReal.toReal_nonneg)
      simpa only [pow_succ] using product.trans_eq (by ring)
    | @waiting firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
      have head := phaseBindingWaitingPair.record_ratio setup mode runtime leaks bounds plan horizon
        scheduler finite wellFormed target approximation maximal n capacity floor positive floored
          noise noiseNonnegative noiseSmall slotWeight slotPositive.le slotBounded who firstRecord
            secondRecord pair
      rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability]
      have product := mul_le_mul head ih
        ((N).ownPlayReachProbability_nonneg _ _) (mul_nonneg waitNonnegative ENNReal.toReal_nonneg)
      simpa only [pow_succ] using product.trans_eq (by ring)
    | @opening firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
      have head := phaseOpeningResponsePair.record_eq setup mode runtime leaks bounds plan horizon
        scheduler wellFormed maximal (approximation.sequence n) noise noiseNonnegative noiseSmall.le
          slotWeight slotPositive.le slotBounded who firstRecord secondRecord pair
      rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability,
        head]
      have product := mul_le_mul_of_nonneg_left ih
        (show 0 ≤ (((strategy who secondRecord.1).map Subtype.val) (some secondRecord.2)).toReal
          from ENNReal.toReal_nonneg)
      exact product.trans_eq (by ring)
    | @inert firstRecord secondRecord restFirst restSecond sends waits pair _tail ih =>
      have head := phaseInertResponsePair.record_eq setup mode runtime leaks bounds plan horizon
        scheduler strategy who firstRecord secondRecord pair
      rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability,
        head]
      have product := mul_le_mul_of_nonneg_left ih
        (show 0 ≤ (((strategy who secondRecord.1).map Subtype.val) (some secondRecord.2)).toReal
          from ENNReal.toReal_nonneg)
      exact product.trans_eq (by ring)
  exact products paired

/-- Every own-response factor comes from its actual callback category. Send
and binding-wait counts remain separate; exact opening and inert laws cancel. -/
theorem phase_playerReach_repair_prefix_of_floor
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : (E).History) (sends waits : Nat)
    (paired : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      ((N).ownPlay who first.trace) ((N).ownPlay who second.trace) sends waits) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded
    sends + waits ≤ 2 * horizon + 1 ∧
    (N).playerReachProbability strategy who first.trace ≤
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^ sends *
        (1 + noise / ((1 - noise) * floor)) ^ waits *
          (N).playerReachProbability strategy who second.trace := by
  intro strategy
  have counts : ∀ {firstRecords secondRecords sendCount waitCount},
      PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who firstRecords
        secondRecords sendCount waitCount → sendCount + waitCount ≤ firstRecords.length := by
    intro firstRecords secondRecords sendCount waitCount matched
    induction matched <;> simp_all only [List.length_cons, List.length_nil] <;> omega
  have count := counts paired
  have ownLength : ∀ {state} (trace : (E).Trace state),
      ((N).ownPlay who trace).length ≤ trace.length := by
    intro state trace
    induction trace with
    | start => simp [InfoSignals.ownPlay, Trace.length]
    | extend prior joint legal reached ih =>
      rw [InfoSignals.ownPlay_extend]
      cases joint who <;> simp_all only [Trace.length, List.length_cons] <;> omega
  have bounded := (app).trace_bound initial horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
      first.trace)
  rw [ReactiveApplication.ResponseMenu.toRawTrace_length] at bounded
  refine ⟨by have := ownLength first.trace; omega, ?_⟩
  rw [(N).playerReachProbability_eq_ownPlayReachProbability,
    (N).playerReachProbability_eq_ownPlayReachProbability]
  exact paired.reach_ratio setup mode runtime leaks bounds plan horizon scheduler finite wellFormed
    target approximation maximal n capacity floor positive floored noise noiseNonnegative noiseSmall
      slotWeight slotPositive slotBounded who _ _ sends waits

/-- The single common source floor is derived over all genuine auxiliary
sites, so every category uses the same assessment and quantitative witness. -/
theorem phase_playerReach_repair_prefix [setup.FiniteInitialLaw]
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧
      ∀ (who : Player) (first second : (E).History) (sends waits : Nat),
        PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
          ((N).ownPlay who first.trace) ((N).ownPlay who second.trace) sends waits →
        let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial
          horizon scheduler wellFormed (approximation.sequence n) noise noiseNonnegative
            noiseSmall.le slotWeight slotPositive.le slotBounded
        sends + waits ≤ 2 * horizon + 1 ∧
        (N).playerReachProbability strategy who first.trace ≤
          ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^ sends *
            (1 + noise / ((1 - noise) * floor)) ^ waits *
              (N).playerReachProbability strategy who second.trace := by
  obtain ⟨floor, positive, bounded, floored⟩ :=
    setup.exists_commitRecovery_choice_floor finite (approximation.sequence n)
      (approximation.mixed n)
  exact ⟨floor, positive, bounded, phase_playerReach_repair_prefix_of_floor setup mode runtime
    leaks bounds plan horizon scheduler finite wellFormed target approximation maximal n capacity
      floor positive floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded⟩

end Vegas
