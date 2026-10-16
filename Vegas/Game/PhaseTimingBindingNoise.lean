/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingBindingWaitingRatio
import Vegas.Game.PhaseTimingRawMixture

/-! # Near-one raw-noise loss for an actual commitment waiting atom -/

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

/-- At the actual same commitment input, every operational timing mixture
has the original independent omission lower bound. Removing only the RAW tier
therefore changes its WAIT atom by a near-one factor, uniformly over all pool
weights and private timing plans. Later sending remains in the continuation. -/
theorem phaseTimingComponent_silence_noise_comparison
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
    let residual := weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num)
        slotWeight slotPositive.le slotBounded agent)
    let perturbed := weights.bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
        noiseSmall.le slotWeight slotPositive.le slotBounded agent)
    ∃ silent : (N).Choice agent.1 agent.2.1, silent.1 = some ⟨none⟩ ∧
      slotWeight * floor ≤ (residual silent).toReal ∧
      (1 - noise) * (residual silent).toReal ≤ (perturbed silent).toReal ∧
      (perturbed silent).toReal ≤
        (1 + noise / (slotWeight * floor)) * (residual silent).toReal := by
  classical
  intro residual perturbed
  obtain ⟨silent, silentEq, lower, _coarse⟩ :=
    phaseTimingComponent_waiting_ratio_of_floor setup mode runtime leaks bounds plan horizon
      scheduler bound finite wellFormed target approximation maximal n capacity floor floorPositive
        floored 0 (by norm_num) (by norm_num) slotWeight slotPositive slotBounded agent weights
          current trace acting atInput event payload binding request unsent values clear
  have residualLower : slotWeight * floor ≤ (residual silent).toReal := by
    simpa only [sub_zero, one_mul] using lower
  have decomposition := phaseTimingComponent_mixture_raw_mixture setup mode runtime leaks bounds
    initial horizon scheduler bound wellFormed (approximation.sequence n) noise noiseNonnegative
      noiseSmall.le slotWeight slotPositive.le slotBounded agent weights
  have atom : (perturbed silent).toReal = noise *
      (((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) silent).toReal +
        (1 - noise) * (residual silent).toReal := by
    dsimp only [perturbed]
    rw [decomposition, mix_apply_toReal]
  have rawNonnegative : 0 ≤
      (((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) silent).toReal :=
    ENNReal.toReal_nonneg
  have rawBounded := pmf_toReal_apply_le_one
    ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) silent
  have denominator : 0 < slotWeight * floor := mul_pos slotPositive floorPositive
  have error : noise ≤ noise / (slotWeight * floor) * (residual silent).toReal := by
    rw [div_mul_eq_mul_div, le_div_iff₀ denominator]
    exact mul_le_mul_of_nonneg_left residualLower noiseNonnegative
  refine ⟨silent, silentEq, residualLower, ?_, ?_⟩
  · rw [atom]
    exact le_add_of_nonneg_left (mul_nonneg noiseNonnegative rawNonnegative)
  · rw [atom]
    nlinarith [mul_nonneg noiseNonnegative (show 0 ≤ (residual silent).toReal from
      ENNReal.toReal_nonneg), mul_le_mul_of_nonneg_left rawBounded noiseNonnegative]

end Vegas
