/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryChoiceFloor
import Vegas.Game.PhaseBindingReplacementMass

/-! # Actual binding response ratios from the same auxiliary source strategy -/

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

omit [Fintype Player] in
private theorem source_result_floor (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (floor : ℝ)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ (assessment.strategy who site.1 choice).toReal)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (clear : control.execution.application.current.excluded = ∅)
    (result : PublicationResult (L.Val payload)) :
    floor ≤ (((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who)))).map
          (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1))
            (result, false)).toReal := by
  classical
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler trace who event payload binding request.2.2.1 clear wellFormed
  obtain ⟨source, _sourceTrace, _excluded, _generation, _actor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding request.2.2.1 clear
  rw [decoded] at played ⊢
  obtain ⟨choice, same⟩ := exists_phaseRecoveryBindingChoice setup mode runtime leaks wellFormed
    control.execution who event payload binding _ decoded request.2.2.2.1 result
  have chosen := floored who ⟨_, played⟩ choice
  apply chosen.trans
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  rw [PMF.map_apply]
  have term := ENNReal.le_tsum (f := fun other : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who
        (some (ProtocolState.observe who setup.program source.point))) =>
    @ite ENNReal
      ((result, false) = phaseRecoveryBindingData setup mode event who payload binding other.1)
      (Classical.propDecidable _) (assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who (some _)) other) 0) choice
  simpa only [same, ite_true] using term

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

include maximal

/-- Every admissible raw binding has a canonical replacement at its actual
fresh slot. One common positive source floor bounds its perturbed response
ratio against any original native input, even when the two decoded source
views differ. Source-result, slot-tier and raw-noise factors stay separate. -/
theorem phaseSourcePerturbedStrategy_replacement_ratio_of_floor
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ (assessment.strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1) :
    ∀ (control : (phaseApplication runtime leaks).Control) (_trace : (E).Trace (some control))
        (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
        (_binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
        (_request : control.execution.application.SeedRequest who
          ⟨control.execution.application.attempt, event⟩)
        (_unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
          (control.execution.recall who), PhaseCount.event? message.payload ≠
            some ⟨control.execution.application.attempt, event⟩)
        (_values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
        (_clear : control.execution.application.current.excluded = ∅)
        (serial : Nat) (preparation : Option (Raw L))
        (evidence : EvidenceRequest (serviceGraph setup mode))
        (_member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
          (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks
            bounds who (control.execution.recall who)
              (control.execution.observe (phaseApplication runtime leaks) who))
        (result : PublicationResult (L.Val payload)),
      ∃ replacement : (N).Choice who (some (control.execution.recall who,
        control.execution.observe (phaseApplication runtime leaks) who)),
        replacement.1 = some (phaseBindingResponse runtime leaks who event payload result serial) ∧
        ∀ (originalInput : (phaseApplication runtime leaks).Info)
          (original : (N).Choice who originalInput),
          ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
            wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
              slotBounded who originalInput) original).toReal ≤
          ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
            ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
              scheduler wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight
                slotPositive.le slotBounded who (some (control.execution.recall who,
                  control.execution.observe (phaseApplication runtime leaks) who)))
                    replacement).toReal := by
  intro control trace who event payload binding request unsent values clear serial preparation
    evidence member result
  obtain ⟨replacement, selected, _positive, lower⟩ :=
    phaseSourcePerturbedStrategy_replacement_mass setup mode runtime leaks bounds plan maximal
      horizon scheduler wellFormed assessment mixed noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded control trace who event payload binding request
          unsent values clear serial preparation evidence member result
  refine ⟨replacement, selected, ?_⟩
  intro originalInput original
  have sourceFloor := source_result_floor setup mode runtime leaks wellFormed assessment floor
    floored plan maximal horizon scheduler
      ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
        who event payload binding request clear result
  have capacity : 0 < (bounds.candidateCount : ℝ) := by
    let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
    have typedTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
      dsimp only [inputs]
      rw [PMF.map_comp]
      exact trace
    have bounded := (PhaseCount.binding_slot_mem_of_onePacket runtime leaks bounds plan inputs
      horizon scheduler typedTrace who event payload binding request unsent values serial
        preparation evidence member).1
    exact_mod_cast (show 0 < bounds.candidateCount by omega)
  have denominator : 0 < (1 - noise) * slotWeight * floor :=
    mul_pos (mul_pos (sub_pos.mpr noiseSmall) slotPositive) floorPositive
  have lowerFloor : ((1 - noise) * slotWeight * floor) / (bounds.candidateCount : ℝ) ≤
      ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
          slotBounded who (some (control.execution.recall who,
            control.execution.observe (phaseApplication runtime leaks) who)))
              replacement).toReal := by
    apply le_trans ?_ lower
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right sourceFloor capacity.le)
      (mul_nonneg (sub_nonneg.mpr noiseSmall.le) slotPositive.le)
  have upper := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (show (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
      wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
        slotBounded who originalInput original) ≤ ENNReal.ofReal 1 by
      rw [ENNReal.ofReal_one]
      exact PMF.coe_le_one _ _)
  apply upper.trans
  rw [div_mul_eq_mul_div, le_div_iff₀ denominator]
  calc
    (1 : ℝ) * ((1 - noise) * slotWeight * floor) =
        (((1 - noise) * slotWeight * floor) / (bounds.candidateCount : ℝ)) *
          (bounds.candidateCount : ℝ) := by field_simp
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right lowerFloor capacity.le

/-- Finite genuine auxiliary sites provide a single source floor for all
actual replacement callbacks, independently of their hidden source views. -/
theorem phaseSourcePerturbedStrategy_replacement_ratio
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧
      ∀ (control : (phaseApplication runtime leaks).Control) (_trace : (E).Trace (some control))
        (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
        (_binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
        (_request : control.execution.application.SeedRequest who
          ⟨control.execution.application.attempt, event⟩)
        (_unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
          (control.execution.recall who), PhaseCount.event? message.payload ≠
            some ⟨control.execution.application.attempt, event⟩)
        (_values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
        (_clear : control.execution.application.current.excluded = ∅)
        (serial : Nat) (preparation : Option (Raw L))
        (evidence : EvidenceRequest (serviceGraph setup mode))
        (_member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
          (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks
            bounds who (control.execution.recall who)
              (control.execution.observe (phaseApplication runtime leaks) who))
        (result : PublicationResult (L.Val payload)),
      ∃ replacement : (N).Choice who (some (control.execution.recall who,
        control.execution.observe (phaseApplication runtime leaks) who)),
        replacement.1 = some (phaseBindingResponse runtime leaks who event payload result serial) ∧
        ∀ (originalInput : (phaseApplication runtime leaks).Info)
          (original : (N).Choice who originalInput),
          ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
            wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
              slotBounded who originalInput) original).toReal ≤
          ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
            ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
              scheduler wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight
                slotPositive.le slotBounded who (some (control.execution.recall who,
                  control.execution.observe (phaseApplication runtime leaks) who)))
                    replacement).toReal := by
  obtain ⟨floor, floorPositive, floorBounded, floored⟩ :=
    setup.exists_commitRecovery_choice_floor finite assessment mixed
  exact ⟨floor, floorPositive, floorBounded,
    phaseSourcePerturbedStrategy_replacement_ratio_of_floor setup mode runtime leaks bounds plan
      maximal horizon scheduler wellFormed assessment mixed floor floorPositive floored noise
        noiseNonnegative noiseSmall slotWeight slotPositive slotBounded⟩

end Vegas
