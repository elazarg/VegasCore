/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingWaitingRatio
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Repeated binding waits in actual native own-action prefixes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

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

/-- A pair of literal waiting records is witnessed by actual initialized clear
unsent callbacks at the same original binding event. No probability comparison
or equality of hidden source views is part of this chronological relation. -/
def phaseBindingWaitingPair (who : Player)
    (firstRecord secondRecord : (N).InfoState who × (E).Action who) : Prop :=
  ∃ (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (_binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (first second : (app).Control)
    (_firstTrace : (E).Trace (some first)) (_secondTrace : (E).Trace (some second)),
    first.actor = some who ∧ second.actor = some who ∧
    first.execution.application.SeedRequest who ⟨first.execution.application.attempt, event⟩ ∧
    second.execution.application.SeedRequest who ⟨second.execution.application.attempt, event⟩ ∧
    (∀ message ∈ (app).outputs (first.execution.recall who), PhaseCount.event? message.payload ≠
      some ⟨first.execution.application.attempt, event⟩) ∧
    (∀ message ∈ (app).outputs (second.execution.recall who), PhaseCount.event? message.payload ≠
      some ⟨second.execution.application.attempt, event⟩) ∧
    (∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) ∧
    first.execution.application.current.excluded = ∅ ∧
    second.execution.application.current.excluded = ∅ ∧
    firstRecord = (some (first.execution.recall who, first.execution.observe app who), ⟨none⟩) ∧
    secondRecord = (some (second.execution.recall who, second.execution.observe app who), ⟨none⟩)

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

private theorem waiting_record_ratio (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseBindingWaitingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotNonnegative slotBounded
    (((strategy who first.1).map Subtype.val) (some first.2)).toReal ≤
      (1 + noise / ((1 - noise) * floor)) *
        (((strategy who second.1).map Subtype.val) (some second.2)).toReal := by
  obtain ⟨event, payload, binding, firstControl, secondControl, firstTrace, secondTrace,
    firstActor, secondActor, firstRequest, secondRequest, firstUnsent, secondUnsent, values,
      firstClear, secondClear, rfl, rfl⟩ := paired
  let firstChoice : (N).Choice who (some (firstControl.execution.recall who,
      firstControl.execution.observe app who)) :=
    ⟨some ⟨none⟩, ⟨⟨none⟩, PhaseCount.silence_onePacket runtime leaks bounds who _ _, rfl⟩⟩
  let secondChoice : (N).Choice who (some (secondControl.execution.recall who,
      secondControl.execution.observe app who)) :=
    ⟨some ⟨none⟩, ⟨⟨none⟩, PhaseCount.silence_onePacket runtime leaks bounds who _ _, rfl⟩⟩
  intro strategy
  have compared := (phaseSourcePerturbedStrategy_waiting_ratio setup mode runtime leaks bounds
    plan horizon scheduler finite wellFormed target approximation maximal n capacity who event
      payload binding firstControl secondControl firstTrace secondTrace firstActor secondActor
        firstRequest secondRequest firstUnsent secondUnsent values firstClear secondClear floor
          floorPositive floored noise noiseNonnegative noiseSmall slotWeight slotNonnegative
            slotBounded firstChoice secondChoice rfl rfl).2.2
  have firstAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective firstChoice
  have secondAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective secondChoice
  rw [firstAtom, secondAtom]
  exact compared

omit maximal in
private theorem ownPlayReachProbability_filter (who : Player) (policy : (N).BehavioralPolicy who)
    (selected : (N).InfoState who × (E).Action who → Bool)
    (records : List ((N).InfoState who × (E).Action who)) :
    (N).ownPlayReachProbability policy records =
      (N).ownPlayReachProbability policy (records.filter selected) *
        (N).ownPlayReachProbability policy (records.filter fun record => !selected record) := by
  induction records with
  | nil => simp [InformationModel.ownPlayReachProbability]
  | cons record records ih =>
    cases chosen : selected record <;>
      simp only [List.filter_cons, chosen, Bool.false_eq_true, Bool.not_false, Bool.not_true,
        ↓reduceIte, InformationModel.ownPlayReachProbability, ih] <;> ring

/-- Every selected waiting factor is derived at its actual callback. The
remaining own actions are retained exactly, including opening waits and sends.
The quantitative source floor can be shared with the chosen noise schedule. -/
theorem phase_playerReach_waiting_prefix_of_floor
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ ((approximation.sequence n).strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    ∀ (who : Player) (first second : (E).History)
        (selected : (N).InfoState who × (E).Action who → Bool),
        List.Forall₂ (phaseBindingWaitingPair setup mode runtime leaks bounds plan horizon
          scheduler who) ((N).ownPlay who first.trace |>.filter selected)
            ((N).ownPlay who second.trace |>.filter selected) →
        let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial
          horizon scheduler wellFormed (approximation.sequence n) noise noiseNonnegative
            noiseSmall.le slotWeight slotNonnegative slotBounded
        let firstRest := (N).ownPlayReachProbability (strategy who)
          ((N).ownPlay who first.trace |>.filter fun record => !selected record)
        let secondRest := (N).ownPlayReachProbability (strategy who)
          ((N).ownPlay who second.trace |>.filter fun record => !selected record)
        (N).playerReachProbability strategy who first.trace * secondRest ≤
          (1 + noise / ((1 - noise) * floor)) ^
              ((N).ownPlay who first.trace |>.filter selected).length *
            (N).playerReachProbability strategy who second.trace * firstRest := by
  intro who first second selected paired strategy firstRest secondRest
  let ratio := 1 + noise / ((1 - noise) * floor)
  have ratioNonnegative : 0 ≤ ratio := by dsimp [ratio]; positivity
  have products : ∀ {firstRecords secondRecords},
      List.Forall₂ (phaseBindingWaitingPair setup mode runtime leaks bounds plan horizon
        scheduler who) firstRecords secondRecords →
      (N).ownPlayReachProbability (strategy who) firstRecords ≤ ratio ^ firstRecords.length *
        (N).ownPlayReachProbability (strategy who) secondRecords := by
    intro firstRecords secondRecords matched
    induction matched with
    | nil => simp [InformationModel.ownPlayReachProbability]
    | @cons firstRecord secondRecord firstRecords secondRecords matchHead _matchTail ih =>
      have head := waiting_record_ratio setup mode runtime leaks bounds plan horizon scheduler
        finite wellFormed target approximation maximal n capacity floor positive floored noise
          noiseNonnegative noiseSmall slotWeight slotNonnegative slotBounded who firstRecord
            secondRecord matchHead
      rw [InformationModel.ownPlayReachProbability, InformationModel.ownPlayReachProbability]
      have boundedProduct := mul_le_mul head ih
        ((N).ownPlayReachProbability_nonneg _ _)
          (mul_nonneg ratioNonnegative ENNReal.toReal_nonneg)
      simpa only [List.length_cons, pow_succ] using boundedProduct.trans_eq (by ring)
  have selectedBound := products paired
  rw [(N).playerReachProbability_eq_ownPlayReachProbability,
    (N).playerReachProbability_eq_ownPlayReachProbability,
    ownPlayReachProbability_filter setup mode runtime leaks bounds plan horizon scheduler who
      (strategy who) selected ((N).ownPlay who first.trace),
    ownPlayReachProbability_filter setup mode runtime leaks bounds plan horizon scheduler who
      (strategy who) selected ((N).ownPlay who second.trace)]
  have restNonnegative : 0 ≤ firstRest * secondRest :=
    mul_nonneg ((N).ownPlayReachProbability_nonneg (strategy who)
      ((N).ownPlay who first.trace |>.filter fun record => !selected record))
        ((N).ownPlayReachProbability_nonneg (strategy who)
          ((N).ownPlay who second.trace |>.filter fun record => !selected record))
  have scaled := mul_le_mul_of_nonneg_right selectedBound restNonnegative
  dsimp only [firstRest, secondRest, ratio] at scaled ⊢
  nlinarith only [scaled]

/-- Finite genuine source histories supply the floor used by the actual
prefix comparison, without any source-admission or likelihood premise. -/
theorem phase_playerReach_waiting_prefix [setup.FiniteInitialLaw]
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧
      ∀ (who : Player) (first second : (E).History)
        (selected : (N).InfoState who × (E).Action who → Bool),
        List.Forall₂ (phaseBindingWaitingPair setup mode runtime leaks bounds plan horizon
          scheduler who) ((N).ownPlay who first.trace |>.filter selected)
            ((N).ownPlay who second.trace |>.filter selected) →
        let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial
          horizon scheduler wellFormed (approximation.sequence n) noise noiseNonnegative
            noiseSmall.le slotWeight slotNonnegative slotBounded
        let firstRest := (N).ownPlayReachProbability (strategy who)
          ((N).ownPlay who first.trace |>.filter fun record => !selected record)
        let secondRest := (N).ownPlayReachProbability (strategy who)
          ((N).ownPlay who second.trace |>.filter fun record => !selected record)
        (N).playerReachProbability strategy who first.trace * secondRest ≤
          (1 + noise / ((1 - noise) * floor)) ^
              ((N).ownPlay who first.trace |>.filter selected).length *
            (N).playerReachProbability strategy who second.trace * firstRest := by
  obtain ⟨floor, positive, bounded, floored⟩ :=
    setup.exists_commitRecovery_choice_floor finite (approximation.sequence n)
      (approximation.mixed n)
  exact ⟨floor, positive, bounded,
    phase_playerReach_waiting_prefix_of_floor setup mode runtime leaks bounds plan horizon
      scheduler finite wellFormed target approximation maximal n capacity floor positive floored
        noise noiseNonnegative noiseSmall slotWeight slotNonnegative slotBounded⟩

end Vegas
