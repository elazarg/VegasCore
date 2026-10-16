/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingSwapWaiting
import Vegas.Game.PhaseRepairNoise

/-! # The chosen binding-send noise also controls hidden-swap waiting error -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

/-- At an actual active callback, the SAME noise sequence whose finite-depth
binding-send rate vanishes also makes the hidden-swap WAIT ratio tend to one.
The source and slot sequences retain their original decay rates. -/
theorem phase_binding_waiting_factor_tendsto
    (capacity : horizon ≤ bounds.candidateCount)
    (remaining : Nat) (who : Player) (original : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
        horizon scheduler).Trace (some ⟨remaining, some who, original⟩))
    (floor noise slot : ℕ → ℝ)
    (floorPositive : ∀ n, 0 < floor n) (floorBounded : ∀ n, floor n ≤ 1)
    (noiseNonnegative : ∀ n, 0 ≤ noise n) (noiseSmall : ∀ n, noise n < 1)
    (slotPositive : ∀ n, 0 < slot n) (slotBounded : ∀ n, slot n ≤ 1)
    (sendRate : Tendsto (fun n => noise n *
      ((bounds.candidateCount : ℝ) / ((1 - noise n) * slot n * floor n)) ^
        (2 * horizon + 1)) atTop (nhds 0)) :
    Tendsto (fun n => noise n / ((1 - noise n) * (slot n * floor n))) atTop (nhds 0) ∧
      ∀ depth : Nat, Tendsto
        (fun n => (1 + noise n / ((1 - noise n) * (slot n * floor n))) ^ depth)
          atTop (nhds 1) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  let inputs := setup.initialLaw.map encodeInputs
  have nested : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact raw
  obtain ⟨serial, bounded, _selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler ⟨remaining, some who, original⟩ nested who rfl
  have capacityPositive : 0 < bounds.candidateCount :=
    (Nat.zero_le serial).trans_lt (bounded.trans_le capacity)
  have capacityOne : (1 : ℝ) ≤ bounds.candidateCount := by exact_mod_cast capacityPositive
  have relative : Tendsto (fun n => noise n / ((1 - noise n) * (slot n * floor n)))
      atTop (nhds 0) := by
    apply squeeze_zero (fun n => div_nonneg (noiseNonnegative n)
      (mul_nonneg (sub_nonneg.mpr (noiseSmall n).le)
        (mul_nonneg (slotPositive n).le (floorPositive n).le))) (fun n => ?_) sendRate
    let denominator := (1 - noise n) * (slot n * floor n)
    have positive : 0 < denominator :=
      mul_pos (sub_pos.mpr (noiseSmall n)) (mul_pos (slotPositive n) (floorPositive n))
    have atMostOne : denominator ≤ 1 := by
      have first : 1 - noise n ≤ 1 := by linarith [noiseNonnegative n]
      have second : slot n * floor n ≤ 1 :=
        (mul_le_mul_of_nonneg_right (slotBounded n) (floorPositive n).le).trans
          (by simpa using floorBounded n)
      exact (mul_le_mul_of_nonneg_right first
        (mul_pos (slotPositive n) (floorPositive n)).le).trans (by simpa using second)
    have baseOne : 1 ≤ (bounds.candidateCount : ℝ) / denominator := by
      rw [le_div_iff₀ positive]
      simpa only [one_mul] using atMostOne.trans capacityOne
    have inverse : 1 / denominator ≤ (bounds.candidateCount : ℝ) / denominator :=
      div_le_div_of_nonneg_right capacityOne positive.le
    have powered := le_self_pow₀ baseOne (show 2 * horizon + 1 ≠ 0 by omega)
    calc
      noise n / denominator = noise n * (1 / denominator) := by ring
      _ ≤ noise n * ((bounds.candidateCount : ℝ) / denominator) :=
        mul_le_mul_of_nonneg_left inverse (noiseNonnegative n)
      _ ≤ noise n * ((bounds.candidateCount : ℝ) / denominator) ^ (2 * horizon + 1) :=
        mul_le_mul_of_nonneg_left powered (noiseNonnegative n)
      _ = _ := by dsimp only [denominator]; congr 3; ring
  refine ⟨relative, fun depth => ?_⟩
  simpa only [add_zero, one_pow] using
    ((tendsto_const_nhds (x := (1 : ℝ))).add relative).pow depth

end Vegas
