/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseOpponentRawBindingMass
import Vegas.Game.PhaseRepairNoise

/-! # Vanishing opponent raw-send contributions at complete native information -/

noncomputable section

namespace Vegas

open Filter

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

variable [setup.FiniteInitialLaw]
  [nature : (phaseApplication runtime leaks).FiniteNature
    (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)))
      scheduler]

include maximal in
/-- Choose actual native noise AFTER the same source approximation and slot
weights. Every actual complete clear ready-binding information fiber then has
vanishing normalized opponent RAW-send contribution, even if its own mass
vanishes faster than the raw-noise sequence. -/
theorem exists_phase_opponent_raw_binding_share_vanishes
    (capacity : horizon ≤ bounds.candidateCount) (covered : bounds.CoversOutputValues)
    (slotWeight : ℕ → ℝ) (slotPositive : ∀ n, 0 < slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1) :
    ∃ (floor noise : ℕ → ℝ)
      (_floorPositive : ∀ n, 0 < floor n) (noisePositive : ∀ n, 0 < noise n)
      (noiseSmall : ∀ n, noise n < 1 / 2),
      (∀ n player (site : setup.commitRecoveryModel.InformationSite player)
        (choice : setup.commitRecoveryModel.Choice player site.1),
        floor n ≤ ((approximation.sequence n).strategy player site.1 choice).toReal) ∧
      Filter.Tendsto noise Filter.atTop (nhds 0) ∧
      ∀ (focal : Player) (site : (N).InformationSite focal)
        (original : (phaseApplication runtime leaks).Control)
        (originalTrace : (E).Trace (some original)),
        (N).infoOf focal originalTrace = site.1 → original.actor = some focal →
        ∀ (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
        (serviceGraph setup mode).outputLayout event = .binding focal payload →
        original.execution.application.current.excluded = ∅ →
        original.execution.application.SeedRequest focal
          ⟨original.execution.application.attempt, event⟩ →
        Filter.Tendsto (fun n =>
          phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler
            (noise n) focal
            (phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
              wellFormed (approximation.sequence n) (noise n) (noisePositive n).le
                (by linarith [noiseSmall n]) (slotWeight n) (slotPositive n).le (slotBounded n))
            site) Filter.atTop (nhds 0) := by
  obtain ⟨floor, noise, floorPositive, _floorBounded, floored, noisePositive, noiseSmall,
    noiseVanishes, _noiseRelative, sendVanishes, waitsConverge⟩ :=
    exists_phase_repair_noise setup finite (approximation.sequence) approximation.mixed
      slotWeight slotPositive (bounds.candidateCount : ℝ) (Nat.cast_nonneg _) (2 * horizon + 1)
  refine ⟨floor, noise, floorPositive, noisePositive, noiseSmall, floored, noiseVanishes, ?_⟩
  intro focal site original originalTrace atSite active event payload output clear request
  have rateVanishes : Filter.Tendsto (fun n =>
      ((Fintype.card Player : ℝ) * (2 * horizon + 1) * Nat.card (E).History) *
        (noise n * ((bounds.candidateCount : ℝ) /
          ((1 - noise n) * slotWeight n * floor n)) ^ (2 * horizon + 1) *
            (1 + noise n / ((1 - noise n) * floor n)) ^ (2 * horizon + 1)))
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero] using
      (tendsto_const_nhds (x := (Fintype.card Player : ℝ) * (2 * horizon + 1) *
        Nat.card (E).History)).mul (sendVanishes.mul waitsConverge)
  apply squeeze_zero _ _ rateVanishes
  · intro n
    exact (phase_opponent_raw_binding_share_le setup mode runtime leaks bounds plan horizon
      scheduler
      finite wellFormed target approximation maximal n capacity (floor n) (floorPositive n)
        (floored n) (noise n) (noisePositive n).le (by linarith [noiseSmall n]) (slotWeight n)
          (slotPositive n) (slotBounded n) (noisePositive n) covered focal site original
            originalTrace
            atSite active event payload output clear request).1
  · intro n
    exact (phase_opponent_raw_binding_share_le setup mode runtime leaks bounds plan horizon
      scheduler
      finite wellFormed target approximation maximal n capacity (floor n) (floorPositive n)
        (floored n) (noise n) (noisePositive n).le (by linarith [noiseSmall n]) (slotWeight n)
          (slotPositive n) (slotBounded n) (noisePositive n) covered focal site original
            originalTrace
            atSite active event payload output clear request).2

end Vegas
