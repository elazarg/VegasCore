/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairPrefixLikelihood

/-! # Actual raw-mixture binding-send contributions -/

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

/-- The selected raw tier contributes this additive atom to the actual
perturbed response law. It is not the full probability of the observed action. -/
def phaseRawMixtureAtom (noise : ℝ) (who : Player)
    (record : (N).InfoState who × (E).Action who) : ℝ :=
  noise * ((((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
    who record.1).map Subtype.val) (some record.2)).toReal

/-- A marked send retains the actual original binding syntax, including
arbitrary preparation and evidence, and the same-slot canonical image. -/
def phaseRawBindingSendingPair (who : Player)
    (firstRecord secondRecord : (N).InfoState who × (E).Action who) : Prop :=
  ∃ (first second : (app).Control)
    (_firstTrace : (E).Trace (some first)) (_secondTrace : (E).Trace (some second))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (_binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (originalPreparation : Option (Raw L))
    (originalEvidence : EvidenceRequest (serviceGraph setup mode))
    (preparation : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup mode))
    (result : PublicationResult (L.Val payload)),
    first.actor = some who ∧ second.actor = some who ∧
    second.execution.application.SeedRequest who ⟨second.execution.application.attempt, event⟩ ∧
    (∀ message ∈ (app).outputs (second.execution.recall who), PhaseCount.event? message.payload ≠
      some ⟨second.execution.application.attempt, event⟩) ∧
    (∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) ∧
    first.execution.application.current.excluded = ∅ ∧
    second.execution.application.current.excluded = ∅ ∧
    (⟨some ⟨⟨.commitment event (who, .prepared serial), originalPreparation⟩,
        originalEvidence⟩⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (first.execution.recall who) (first.execution.observe app who) ∧
    (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds who (second.execution.recall who)
        (second.execution.observe app who) ∧
    firstRecord = (some (first.execution.recall who, first.execution.observe app who),
      ⟨some ⟨⟨.commitment event (who, .prepared serial), originalPreparation⟩, originalEvidence⟩⟩) ∧
    secondRecord = (some (second.execution.recall who, second.execution.observe app who),
      phaseBindingResponse runtime leaks who event payload result serial)

/-- Forgetting the selected mixture tier leaves the already checked ordinary
sending witness; source accepted-failure atoms remain ordinary source mass. -/
theorem phaseRawBindingSendingPair.toSendingPair (who : Player)
    (first second : (N).InfoState who × (E).Action who)
    (paired : phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    phaseBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who first
      second := by
  obtain ⟨firstControl, secondControl, firstTrace, secondTrace, event, payload, binding, serial,
    originalPreparation, originalEvidence, preparation, evidence, result, firstActor, secondActor,
      request, unsent, values, _firstClear, secondClear, firstMember, secondMember,
        firstRecord, secondRecord⟩ := paired
  exact ⟨firstControl, secondControl, firstTrace, secondTrace, event, payload, binding, serial,
    preparation, evidence, result, _, firstActor, secondActor, request, unsent, values, secondClear,
      firstMember, secondMember, firstRecord, secondRecord⟩

variable (wellFormed : setup.WellFormed)

/-- The raw contribution is exactly one summand of the actual local law.
No canonical accepted-failure or source omission probability is removed. -/
theorem phaseSourcePerturbedStrategy_raw_decomposition
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (record : (N).InfoState who × (E).Action who) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded
    let conditional := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who record.1)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who record.1)
    (((strategy who record.1).map Subtype.val) (some record.2)).toReal =
      phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler noise who record +
        (1 - noise) * ((conditional.map Subtype.val) (some record.2)).toReal := by
  intro strategy conditional
  change (((mix noise noiseNonnegative noiseBounded _ conditional).map Subtype.val)
    (some record.2)).toReal = _
  rw [mix_map, mix_apply_toReal]
  rfl

variable (maximal : plan.phases.IsChain fun before after =>
  before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

/-- The actual single raw-mixture binding-send atom retains its extra noise
weight relative to the canonical same-slot target. One actual source floor
supplies the target lower bound; no source-admission premise is used. -/
theorem phaseRawBindingSendingPair.raw_ratio
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ (assessment.strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight
        slotPositive.le slotBounded
    1 ≤ (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor) ∧
    phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler noise who first ≤
      noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
        (((strategy who second.1).map Subtype.val) (some second.2)).toReal := by
  obtain ⟨firstControl, secondControl, _firstTrace, secondTrace, event, payload, binding, serial,
    originalPreparation, originalEvidence, preparation, evidence, result, _firstActor, _secondActor,
      request, unsent, values, _firstClear, secondClear, _firstMember, secondMember, rfl, rfl⟩ :=
        paired
  intro strategy
  obtain ⟨replacement, selected, compared⟩ :=
    phaseSourcePerturbedStrategy_replacement_ratio_of_floor setup mode runtime leaks bounds plan
      maximal horizon scheduler wellFormed assessment mixed floor positive floored noise
        noiseNonnegative noiseSmall slotWeight slotPositive slotBounded secondControl secondTrace
          who event payload binding request unsent values secondClear serial preparation evidence
            secondMember result
  let inactive : (N).Choice who none := ⟨none, rfl⟩
  let : Subsingleton ((N).Choice who none) := ⟨fun first second => Subtype.ext
    ((show first.1 = none from first.2).trans (show second.1 = none from second.2).symm)⟩
  have inactiveMass : strategy who none inactive = 1 := by
    rw [eq_pure_of_subsingleton (strategy who none) inactive]
    exact PMF.pure_apply_self _
  have targetAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective replacement
  rw [selected] at targetAtom
  have targetUnit := compared none inactive
  change (strategy who none inactive).toReal ≤ _ at targetUnit
  rw [inactiveMass, ENNReal.toReal_one, ← targetAtom] at targetUnit
  have coefficientNonnegative :
      0 ≤ (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor) := by positivity
  have targetUpper := pmf_toReal_apply_le_one
    ((strategy who (some (secondControl.execution.recall who,
      secondControl.execution.observe app who))).map Subtype.val)
    (some (phaseBindingResponse runtime leaks who event payload result serial))
  have oneLe := targetUnit.trans (mul_le_of_le_one_right coefficientNonnegative targetUpper)
  refine ⟨oneLe, ?_⟩
  have uniformUpper := pmf_toReal_apply_le_one
    (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler who
      (some (firstControl.execution.recall who, firstControl.execution.observe app who))).map
        Subtype.val)
    (some (⟨some ⟨⟨.commitment event (who, .prepared serial), originalPreparation⟩,
      originalEvidence⟩⟩ : (app).Action))
  have bounded := (mul_le_mul_of_nonneg_left uniformUpper noiseNonnegative).trans
    (mul_le_mul_of_nonneg_left targetUnit noiseNonnegative)
  dsimp only [phaseRawMixtureAtom]
  nlinarith only [bounded]

end Vegas
