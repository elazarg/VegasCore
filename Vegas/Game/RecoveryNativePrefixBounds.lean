/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.OnePacketBaseAssembly
import Vegas.Game.OnePacketBindingRepairAssembly
import Vegas.Game.OnePacketBlindConstruction

/-! # Prefix estimates for the native comparison sequence

The same recovery completion weights give a native comparison sequence with
vanishing unforced posterior mass and operational-record decorrelation. These
are prefix estimates; no native service or continuation contract is used.
-/

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

def nativeBaseInputs
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((N).InfoState who)] (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount) :
    OnePacketBaseInputs setup leaks bounds horizon (NativeScheduler) sequence
      bounds.candidateCount := by
  refine OnePacketBaseInputs.ofCounterparts wellFormed sequence sourceMixed (2 * horizon + 2)
    0 (le_refl 0) covers coversInputs capacity slots_pos ?_
  intro weights targetSequence assembled mixed _bayes who site notFree notOwing
    past view atSite event turn
  exact OnePacketCounterpartInputs.ofBindingRepairs wellFormed independent sourceMixed
    (fun n => trembleScale_pos
      (combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n)))
    (fun n => trembleScale_le_one
      (combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n)).le
      (combinedFloor_le_one setup leaks bounds horizon (NativeScheduler) (sequence n)))
    (fun _ => rfl) covers coversInputs capacity weights assembled mixed
    notFree notOwing atSite turn

open Classical in
/-- The original prefix certificate applies to the native sequence assembled
from the unchanged recovery completion weights. -/
theorem nativeComparison_prefix_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((N).InfoState who)]
    [∀ who, DecidableEq ((R).InfoState who)]
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
    ∃ drift error : ℕ → ℝ,
      Tendsto drift atTop (nhds 0) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
          ((N).agentAt site) →
        pendingEvent setup leaks who site.1 ≠ none →
        expect ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n).belief who site)
          (fun history => if Vegas.ForcedState setup leaks who history.1.state
            then (0 : ℝ) else 1) ≤ drift n ∧
        BeliefDecorrelated ((nativeComparisonSequence setup leaks bounds horizon scheduler
            sequence scale positive le_one weights n).belief who site)
          (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler)
            history.1.trace)
          (fun history => Vegas.nativeDecodedState setup leaks history.1.state) (error n) := by
  let inputs := nativeBaseInputs setup leaks bounds horizon scheduler wellFormed independent
    sequence sourceMixed covers coversInputs capacity slots_pos
  have scaleIdentity : scale = inputs.scale := funext scaleEq
  subst scale
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  let nativeWeights := fun n =>
    nativeComparisonWeights setup leaks bounds horizon scheduler (weights n)
  have assembled : OnePacketAssembled setup leaks bounds horizon (NativeScheduler) sequence
      inputs.scale inputs.scale_pos inputs.scale_le_one nativeWeights target :=
    nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence
      inputs.scale positive le_one weights
  have mixed : ∀ n, (target n).IsFullyMixed :=
    nativeComparisonSequence_fullyMixed setup leaks bounds horizon scheduler sequence
      inputs.scale positive le_one weights
  have bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon (NativeScheduler)).decisionInformationAntichain :=
    nativeComparisonSequence_bayes setup leaks bounds horizon scheduler sequence
      inputs.scale positive le_one weights
  obtain ⟨drift, driftLimit, unforced⟩ := inputs.nonLateUnforced setup leaks bounds horizon
    (NativeScheduler) wellFormed nativeWeights target assembled mixed bayes
  obtain ⟨error, errorLimit, decorrelated⟩ := inputs.nonLateDecorrelated setup leaks bounds horizon
    (NativeScheduler) wellFormed sourceMixed nativeWeights target assembled mixed bayes
  exact ⟨drift, error, driftLimit, errorLimit, fun n who site notFree notOwing notKeyed pending =>
    ⟨unforced n who site notFree notOwing notKeyed pending,
      decorrelated n who site notFree notOwing notKeyed pending⟩⟩

end Vegas.RecoveryOnePacket
