/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueRealization

/-! # Actual runtime responses from original global private plans -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

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

local instance : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The original global source-policy and timing-plan mixture realizes the
literal assembled runtime response at an authentic clear unsent binding.
Both immutable priors are conditioned on the actual entire own recall. -/
theorem phaseTimingPlanPolicy_value_strategy_of_history
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
    (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩) :
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    ((app).policyMixture original family).policy (control.execution.recall who)
        (control.execution.observe (app) who) =
      ((menu).decodeProfile initial horizon scheduler
        ((N).agentBehavior (N).playedInformation fallback
          (fun agent => (weights (pool agent)).bind
            (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
              wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
                slotNonnegative slotBounded agent)))) who (control.execution.recall who)
                  (control.execution.observe (app) who) := by
  intro sourcePrior original family
  let past := control.execution.recall who
  let view := control.execution.observe (app) who
  let decoded := phaseSourceView? setup mode runtime leaks who event view
  let current := setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who
    decoded
  obtain ⟨played, joint⟩ := phaseTimingPlanPolicy_value_joint_of_history setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
      weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control trace active clear event payload binding request unsent
  let agent : Agent := ⟨who, ⟨some (past, view), played⟩⟩
  change (((app).policyMixture original family).posterior past).map
      (fun memory => (memory.1 (pool agent), memory.2 decoded)) =
        (weights (pool agent)).bind (fun part => current.map (Prod.mk part)) at joint
  obtain ⟨readout, averaged⟩ := phaseTimingPlanPolicy_value_readout_of_history setup mode runtime
    leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
      finite noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control trace active clear event payload binding request
  let basePlan := fun p : Pool => (weights p).support_nonempty.choose
  let baseSource := sourcePrior.support_nonempty.choose
  let fixed := fun part => Function.update basePlan (pool agent) part
  let changed := fun member => setup.commitRecoveryValueAssessment wellFormed assessment who member
  let kernel := fun pair : Parts (pool agent) × ((setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Choice who decoded) =>
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
    scheduler bound fallback wellFormed
      (changed (Function.update baseSource decoded pair.2)) noise noiseNonnegative noiseBounded
        slotWeight slotNonnegative slotBounded (fixed pair.1) who past view
  have planLocal (profile : setup.commitRecoveryModel.BehavioralAssessment)
      (first second : (p : Pool) → Parts p) (same : first (pool agent) = second (pool agent)) :
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed profile noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded first who past view =
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed profile noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded second who past view := by
    rw [phaseTimingPlanPolicy_apply, phaseTimingPlanPolicy_apply, dite_eq_left played,
      dite_eq_left played]
    exact congrArg (fun part =>
      ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed profile noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded agent part).map (fun choice => choice.1.getD ⟨none⟩))) same
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  have depends (plan : (p : Pool) → Parts p) (member) :
      family (plan, member) past view = kernel (plan (pool agent), member decoded) := by
    apply (planLocal (changed member) plan (fixed (plan (pool agent))) (by
      simp only [fixed, Function.update_self])).trans
    exact phaseTimingPlanPolicy_value_binding_congr setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded (fixed (plan (pool agent))) who member
          (Function.update baseSource decoded (member decoded)) control.execution valid clear event
            payload binding request played
              (@Function.update_self
                ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).InfoState
                  who)
                ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).Choice
                  who) (Classical.decEq _) decoded (member decoded) baseSource).symm
  have row (part : Parts (pool agent)) :
      current.bind (fun choice => kernel (part, choice)) =
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded (fixed part) who past view := by
    have originalRow := averaged (fixed part)
    change sourcePrior.bind (fun member => family (fixed part, member) past view) = _ at originalRow
    have transformed : sourcePrior.bind (fun member => family (fixed part, member) past view) =
        sourcePrior.bind (fun member => kernel (part, member decoded)) := by
      apply congrArg (PMF.bind sourcePrior)
      funext member
      have meaning := depends (fixed part) member
      simpa only [fixed, Function.update_self] using meaning
    have projected := congrArg (fun law => law.bind (fun choice => kernel (part, choice))) readout
    have normalized : sourcePrior.bind (fun member => kernel (part, member decoded)) =
        current.bind (fun choice => kernel (part, choice)) :=
      (PMF.bind_map sourcePrior (fun member => member decoded)
        (fun choice => kernel (part, choice))).symm.trans projected
    exact normalized.symm.trans (transformed.symm.trans originalRow)
  calc
    _ = (((app).policyMixture original family).posterior past).bind
        (fun memory => kernel (memory.1 (pool agent), memory.2 decoded)) := by
      rw [ReactiveApplication.policyMixture_policy]
      apply congrArg (PMF.bind _)
      funext memory
      exact depends memory.1 memory.2
    _ = ((((app).policyMixture original family).posterior past).map
        (fun memory => (memory.1 (pool agent), memory.2 decoded))).bind kernel :=
      (PMF.bind_map (((app).policyMixture original family).posterior past)
        (fun memory => (memory.1 (pool agent), memory.2 decoded)) kernel).symm
    _ = ((weights (pool agent)).bind (fun part => current.map (Prod.mk part))).bind kernel :=
      congrArg (fun law => law.bind kernel) joint
    _ = (weights (pool agent)).bind (fun part =>
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded (fixed part) who past view) := by
      rw [PMF.bind_bind]
      apply congrArg (PMF.bind _)
      funext part
      exact (PMF.bind_map ..).trans (row part)
    _ = (weights (pool agent)).bind (fun part =>
        ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded agent part).map (fun choice => choice.1.getD ⟨none⟩))) := by
      apply congrArg (PMF.bind _)
      funext part
      rw [phaseTimingPlanPolicy_apply, dite_eq_left played]
      change ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded agent ((fixed part) (pool agent))).map _) = _
      rw [show (fixed part) (pool agent) = part from Function.update_self ..]
    _ = _ := by
      simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
        ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
        InformationModel.agentBehavior, dite_eq_left played]
      exact (PMF.map_bind ..).symm

end Vegas
