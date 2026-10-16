/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools
import Vegas.Game.PhaseBindingWaitingRatio

/-! # Actual binding WAIT bounds under arbitrary operational timing weights -/

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
  (bound : (serviceGraph setup mode).EventId → Nat)
  (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

include maximal

/-- The original source omission atom supplies a lower bound on actual silence
for any timing weights. This is a response probability bound: WAIT retains
every later callback, and is not identified with immediate exclusion. -/
theorem phaseTimingComponent_waiting_ratio_of_floor
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ ((approximation.sequence n).strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (weights : PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some agent.1)
    (atInput : agent.2.1 = some
      (current.execution.recall agent.1, current.execution.observe app agent.1))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding agent.1 payload)
    (request : current.execution.application.SeedRequest agent.1
      ⟨current.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (current.execution.recall agent.1),
      PhaseCount.event? message.payload ≠ some ⟨current.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : current.execution.application.current.excluded = ∅) :
    ∃ silent : (N).Choice agent.1 agent.2.1, silent.1 = some ⟨none⟩ ∧
      (1 - noise) * slotWeight * floor ≤
        ((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
            slotWeight slotPositive.le slotBounded agent)) silent).toReal ∧
      ∀ (originalInput : (app).Info) (originalLaw : PMF ((N).Choice agent.1 originalInput))
        (original : (N).Choice agent.1 originalInput),
        (originalLaw original).toReal ≤ (1 / ((1 - noise) * slotWeight * floor)) *
          ((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
            scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
              noiseSmall.le slotWeight slotPositive.le slotBounded agent)) silent).toReal := by
  classical
  let rawSilent : (N).Choice agent.1 (some
      (current.execution.recall agent.1, current.execution.observe app agent.1)) :=
    ⟨some ⟨none⟩, ⟨⟨none⟩, PhaseCount.silence_onePacket runtime leaks bounds _ _ _, rfl⟩⟩
  have sourceFloor := (phaseSourcePerturbedStrategy_waiting_ratio setup mode runtime leaks bounds
    plan horizon scheduler finite wellFormed target approximation maximal n capacity agent.1 event
      payload binding current current trace trace acting acting request request unsent unsent
        values clear clear floor floorPositive floored 0 (by norm_num) (by norm_num) 1
          (by norm_num) (by norm_num) rawSilent rawSilent rfl rfl).2.1
  simp only [phaseSourcePerturbedStrategy, mix_zero, mix_one, sub_zero, one_mul] at sourceFloor
  let silent : (N).Choice agent.1 agent.2.1 :=
    ⟨rawSilent.1, by rw [atInput]; exact rawSilent.2⟩
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks agent.2.1 := by
    rw [atInput]
    rintro ⟨past, view, same, excluded⟩
    have viewEq := congrArg Prod.snd (Option.some.inj same)
    have flags := congrArg (fun view : (app).PlayerView => view.application.2.excluded) viewEq
    exact excluded (flags.symm.trans clear)
  have slotFloor : floor ≤
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed
        (approximation.sequence n) initial horizon scheduler agent.1 agent.2.1) silent).toReal := by
    have mapped := congrArg (fun input : (app).Info =>
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler agent.1 input).map Subtype.val) atInput
    have atom := congrArg (fun law : PMF (Option (app).Action) => (law rawSilent.1).toReal) mapped
    have firstAtom := pmf_map_apply_of_injective
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler agent.1 agent.2.1) Subtype.val_injective silent
    have secondAtom := pmf_map_apply_of_injective
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler agent.1 (some
          (current.execution.recall agent.1, current.execution.observe app agent.1)))
      Subtype.val_injective rawSilent
    have sameValue : silent.1 = rawSilent.1 := rfl
    rw [sameValue] at firstAtom
    exact sourceFloor.trans_eq ((congrArg ENNReal.toReal secondAtom).symm.trans
      (atom.symm.trans (congrArg ENNReal.toReal firstAtom)))
  have lower : (1 - noise) * slotWeight * floor ≤
      ((weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        bound wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
          slotPositive.le slotBounded agent)) silent).toReal := by
    apply le_trans ?_ (phaseTimingComponent_mixture_ge_slot setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
        noiseSmall.le slotWeight slotPositive.le slotBounded agent unflagged weights silent)
    exact mul_le_mul_of_nonneg_left slotFloor
      (mul_nonneg (sub_nonneg.mpr noiseSmall.le) slotPositive.le)
  refine ⟨silent, rfl, lower, ?_⟩
  intro originalInput originalLaw original
  have denominator : 0 < (1 - noise) * slotWeight * floor :=
    mul_pos (mul_pos (sub_pos.mpr noiseSmall) slotPositive) floorPositive
  apply (pmf_toReal_apply_le_one originalLaw original).trans
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ denominator, one_mul]
  exact lower

end Vegas
