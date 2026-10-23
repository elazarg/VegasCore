/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryComparisonSite
import Vegas.Game.RecoveryNativePrefixBounds
import Vegas.Game.OnePacketLateRecords

/-! # Same-key operational records under the actual recovery beliefs -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

/-- The existing pending-event lumping for the comparison profile assembled from
the unchanged recovery completion weights. -/
def nativeComparisonLumping [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (n : ℕ) (who : Player) :=
  certificateLumping setup leaks bounds horizon (NativeScheduler) sequence scale positive le_one
    covers (Nat.succ_le_of_lt (Nat.zero_lt_of_lt (capacity who))) (le_refl bounds.candidateCount)
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
      weights)
    (nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence scale positive
      le_one weights) n who

open Classical in
/-- The original native keyed-record estimate applies to comparison profiles
built from the same recovery weights, without a native service contract. -/
theorem nativeComparison_keyed_record_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) :
    ∃ drift : ℕ → ℝ, Tendsto drift atTop (nhds 0) ∧
      ∀ n who, ∃ recordLaw : LateKey setup leaks →
        PMF (List (Option (OperationalState setup leaks))),
        ∀ site : (N).InformationSite who,
          ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
          ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
          ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
            ((N).agentAt site) →
          ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
          |expect (((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
              positive le_one weights n).belief who site).map
              (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler)
                history.1.trace))
              (lumpedFailure setup leaks bounds horizon (NativeScheduler)
                (nativeComparisonLumping setup leaks bounds horizon scheduler sequence scale
                  positive le_one weights covers capacity n who) (2 * horizon + 1) key option) -
            expect (recordLaw key)
              (lumpedFailure setup leaks bounds horizon (NativeScheduler)
                (nativeComparisonLumping setup leaks bounds horizon scheduler sequence scale
                  positive le_one weights covers capacity n who) (2 * horizon + 1) key option)| ≤
            drift n := by
  let inputs := nativeBaseInputs setup leaks bounds horizon scheduler wellFormed independent
    sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have mixed := nativeComparisonSequence_fullyMixed setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have bayes := nativeComparisonSequence_bayes setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have records := inputs.lateRecords_of_keyed setup leaks bounds horizon (NativeScheduler)
    wellFormed independent
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup leaks bounds horizon scheduler sequence inputs.scale positive
      le_one weights) assembled mixed bayes
  simpa only [nativeComparisonLumping] using records

end Vegas.RecoveryOnePacket
