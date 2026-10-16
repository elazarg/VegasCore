/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueComparison
import GameTheoryExtensions.Analysis.Protocol.ContinuationFactorUniqueness

/-! # Canonical native marks for an actual continuation suffix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- The actual trace suffix fixes one marker for ALL immutable member
profiles. Any conditionally certified witness returned by the stopped bound
is at most this same marker: nonzero coefficients are uniquely determined,
while zero coefficients contribute nothing. -/
theorem exists_binding_marker_of_tracePrefix
    (noise : ℝ) (nonnegative : 0 ≤ noise) (focal : Player)
    (entry final : (E).History) (isPrefix : TracePrefix entry.trace final.trace) :
    ∃ records : ∀ who, List ((N).InfoState who × (E).Action who),
      ∃ chance : ℝ, 0 ≤ chance ∧
        (∀ who, (N).ownPlay who final.trace =
          records who ++ (N).ownPlay who entry.trace) ∧
        (∀ who record, record ∈ records who →
          ∃ (before : (E).History) (joint : ∀ player, Option ((E).Action player))
            (legal : (E).Legal before.state joint) (next : (E).State)
            (realized : next ∈ ((E).step before.state ⟨joint, legal⟩).support),
            TracePrefix entry.trace before.trace ∧
            TracePrefix (before.trace.extend joint legal realized) final.trace ∧
            (N).infoOf who before.trace = record.1 ∧ joint who = some record.2) ∧
        (∀ profile : ∀ who, (N).BehavioralPolicy who,
          (((N).runBehavioralFrom profile (final.trace.length - entry.trace.length)
            entry) final).toReal =
              chance * ∏ who, (N).ownPlayReachProbability (profile who) (records who)) ∧
        (∀ chosen : ∀ who, List ((N).InfoState who × (E).Action who),
          ∀ coefficient : ℝ,
          (coefficient ≠ 0 →
            (∀ who, (N).ownPlay who final.trace =
              chosen who ++ (N).ownPlay who entry.trace) ∧
            (∀ profile : ∀ who, (N).BehavioralPolicy who,
              (((N).runBehavioralFrom profile (final.trace.length - entry.trace.length)
                entry) final).toReal =
                  coefficient * ∏ who,
                    (N).ownPlayReachProbability (profile who) (chosen who))) →
          ∀ profile : ∀ who, (N).BehavioralPolicy who,
            binding_marker_density setup mode runtime leaks bounds runtimePlan horizon scheduler
              noise focal profile chosen coefficient ≤
                binding_marker_density setup mode runtime leaks bounds runtimePlan horizon
                  scheduler noise focal profile records chance) := by
  classical
  obtain ⟨records, recordEq, callbacks, chance, chanceNonnegative, factor⟩ :=
    (N).exists_continuation_ownPlay_factor entry.trace final.trace isPrefix
  refine ⟨records, chance, chanceNonnegative, recordEq, callbacks, factor, ?_⟩
  intro chosen coefficient certified profile
  by_cases zero : coefficient = 0
  · unfold binding_marker_density
    rw [zero, zero_mul]
    apply mul_nonneg chanceNonnegative
    apply Finset.sum_nonneg
    intro index _member
    apply mul_nonneg _ (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
    split_ifs
    · exact mul_nonneg nonnegative ENNReal.toReal_nonneg
    · exact le_rfl
  · obtain ⟨chosenRecords, chosenFactor⟩ := certified zero
    obtain ⟨sameRecords, sameChance⟩ := (N).continuation_ownPlay_factor_unique
      ((menu).uniformAssessment initial horizon scheduler)
        ((menu).uniform_fullyMixed initial horizon scheduler) entry.trace final.trace
          chosen records chosenRecords recordEq coefficient chance chosenFactor factor
    rw [sameRecords, sameChance]

end Vegas
