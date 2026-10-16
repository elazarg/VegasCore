/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueLikelihood
import Interaction.ReactiveMixtureLikelihood
/-! # Original global source-memory density after actual native recall -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
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
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueHistoryDensityPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The actual original plan/value-policy posterior has an exact observed-word
Bayes density whose dependence on the source member is confined to binding
SEND factors. Every other original response probability remains in the explicit
operational factor, including RAW opening WAIT. The factor may depend on the
full physical history and plan; no AUX-fiber proportionality is assumed. -/
theorem phaseTimingPlanPolicy_value_history_density
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    let recalled := control.execution.recall who
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let reference := sourcePrior.support_nonempty.choose
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let binding := fun index : Fin recalled.length => phaseRawBindingRecord setup mode runtime
      leaks bounds runtimePlan horizon scheduler who
        (some (recalled.take index.val, recalled[index.val].beforeView), recalled[index.val].action)
    let atom := fun memory (index : Fin recalled.length) =>
      (family memory (recalled.take index.val) recalled[index.val].beforeView
        recalled[index.val].action).toReal
    let operational := fun plan =>
      ∏ index ∈ Finset.univ.filter (fun index => ¬ binding index), atom (plan, reference) index
    let observed := (((app).privateTranscript recalled).map (fun record =>
      ((app).policyMixture original family).policy record.1.1 record.1.2 record.2)).prod
    (∀ plan, 0 ≤ operational plan) ∧ ∀ memory,
      observed.toReal *
          (((app).policyMixture original family).posterior recalled memory).toReal =
        (original memory).toReal * operational memory.1 *
          ∏ index ∈ Finset.univ.filter binding, atom memory index := by
  intro recalled sourcePrior reference original family binding atom operational observed
  have split (plan) := phaseTimingPlanPolicy_value_recall_factors setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who reference
        control trace clear
  refine ⟨fun plan => (split plan).1, ?_⟩
  intro memory
  have density := congrArg ENNReal.toReal
    ((app).policyMixture_likelihood_density original family [] recalled memory)
  simp only [ENNReal.toReal_mul, List.nil_append] at density
  have initialPosterior : ((app).policyMixture original family).posterior [] = original := rfl
  rw [initialPosterior] at density
  have product := (app).privateTranscriptFrom_product (family memory) [] recalled
  simp only [List.nil_append] at product
  change observed.toReal *
      (((app).policyMixture original family).posterior recalled memory).toReal = _
  calc
    _ = (original memory).toReal *
        ((((app).privateTranscriptFrom [] recalled).map (fun record =>
          family memory record.1.1 record.1.2 record.2)).prod).toReal := density
    _ = _ := by
      rw [product, (split memory.1).2 memory.2]
      exact (mul_assoc ..).symm

end Vegas
