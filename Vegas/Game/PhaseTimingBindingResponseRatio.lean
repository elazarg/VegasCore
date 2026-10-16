/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools
import Vegas.Game.PhaseBindingResponseRatio

/-! # Actual binding replacement bounds for arbitrary timing-pool weights -/

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
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

include maximal

/-- Every legal replacement binding result retains a uniform actual atom
under arbitrary timing weights, including a pool concentrated on WAIT. The
source result may be failure. No all-clear canonical recipe is imposed. -/
theorem phaseTimingComponent_replacement_ratio_of_floor
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ (assessment.strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (current : (app).Control) (trace : (E).Trace (some current))
    (atInput : agent.2.1 = some
      (current.execution.recall agent.1, current.execution.observe app agent.1))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding agent.1 payload)
    (request : current.execution.application.SeedRequest agent.1
      ⟨current.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (current.execution.recall agent.1),
      PhaseCount.event? message.payload ≠ some ⟨current.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : current.execution.application.current.excluded = ∅)
    (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode))
    (member : (⟨some ⟨⟨.commitment event (agent.1, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds agent.1
        (current.execution.recall agent.1) (current.execution.observe app agent.1))
    (result : PublicationResult (L.Val payload)) :
    ∃ replacement : (N).Choice agent.1 agent.2.1,
      replacement.1 =
        some (phaseBindingResponse runtime leaks agent.1 event payload result serial) ∧
      ∀ (originalInput : (app).Info) (originalLaw : PMF ((N).Choice agent.1 originalInput))
        (original : (N).Choice agent.1 originalInput),
        (originalLaw original).toReal ≤
          ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
            ((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
              scheduler bound wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight
                slotPositive.le slotBounded agent)) replacement).toReal := by
  classical
  obtain ⟨rawReplacement, selected, _positive, slotLower⟩ :=
    phaseSourcePerturbedStrategy_replacement_mass setup mode runtime leaks bounds plan maximal
      horizon scheduler wellFormed assessment mixed 0 (by norm_num) (by norm_num) 1
        (by norm_num) (by norm_num) current trace agent.1 event payload binding request unsent
          values clear serial preparation evidence member result
  simp only [phaseSourcePerturbedStrategy, mix_zero, mix_one, sub_zero, one_mul] at slotLower
  have sourceFloor := phaseSourceBindingData_result_lower setup mode runtime leaks wellFormed
    assessment floor floored plan maximal horizon scheduler ((menu).toRawTrace _ _ _ trace)
      agent.1 event payload binding request clear result
  let replacement : (N).Choice agent.1 agent.2.1 :=
    ⟨rawReplacement.1, by rw [atInput]; exact rawReplacement.2⟩
  refine ⟨replacement, selected, ?_⟩
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks agent.2.1 := by
    rw [atInput]
    rintro ⟨past, view, same, excluded⟩
    have viewEq := congrArg Prod.snd (Option.some.inj same)
    have flags := congrArg (fun view : (app).PlayerView => view.application.2.excluded) viewEq
    exact excluded (flags.symm.trans clear)
  have capacity : 0 < (bounds.candidateCount : ℝ) := by
    have initialEq : (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) =
        (initial) := PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
    have physical : ((menu).protocol
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
          scheduler).Trace (some current) := by
      rw [initialEq]
      exact trace
    have bounded := (PhaseCount.binding_slot_mem_of_onePacket runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler physical agent.1 event payload
        binding request unsent values serial preparation evidence member).1
    exact_mod_cast (show 0 < bounds.candidateCount by omega)
  have slotFloor : floor / (bounds.candidateCount : ℝ) ≤
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler agent.1 agent.2.1) replacement).toReal := by
    have lower := (div_le_div_of_nonneg_right sourceFloor capacity.le).trans slotLower
    have mapped := congrArg (fun input : (app).Info =>
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler agent.1 input).map Subtype.val) atInput
    have atom := congrArg (fun law : PMF (Option (app).Action) =>
      (law rawReplacement.1).toReal) mapped
    have firstAtom := pmf_map_apply_of_injective
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler agent.1 agent.2.1) Subtype.val_injective replacement
    have secondAtom := pmf_map_apply_of_injective
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler agent.1 (some
          (current.execution.recall agent.1, current.execution.observe app agent.1)))
      Subtype.val_injective rawReplacement
    have sameValue : replacement.1 = rawReplacement.1 := rfl
    rw [sameValue] at firstAtom
    exact lower.trans_eq ((congrArg ENNReal.toReal secondAtom).symm.trans
      (atom.symm.trans (congrArg ENNReal.toReal firstAtom)))
  have lowerFloor : ((1 - noise) * slotWeight * floor) / (bounds.candidateCount : ℝ) ≤
      ((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        bound wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
          slotBounded agent)) replacement).toReal := by
    apply le_trans ?_ (phaseTimingComponent_mixture_ge_slot setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight
        slotPositive.le slotBounded agent unflagged weights replacement)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left slotFloor
      (mul_nonneg (sub_nonneg.mpr noiseSmall.le) slotPositive.le)
  intro originalInput originalLaw original
  have denominator : 0 < (1 - noise) * slotWeight * floor :=
    mul_pos (mul_pos (sub_pos.mpr noiseSmall) slotPositive) floorPositive
  apply (pmf_toReal_apply_le_one originalLaw original).trans
  rw [div_mul_eq_mul_div, le_div_iff₀ denominator]
  calc
    (1 : ℝ) * ((1 - noise) * slotWeight * floor) =
        (((1 - noise) * slotWeight * floor) / (bounds.candidateCount : ℝ)) *
          (bounds.candidateCount : ℝ) := by field_simp
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right lowerFloor capacity.le

end Vegas
