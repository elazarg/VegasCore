/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueJoint
import Vegas.Game.PhaseRecoveryValueFuture
import Interaction.ReactiveMixtureExtraCoordinate
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Joint original timing and source coordinates at actual callbacks -/

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

local instance coordinatePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- At an authentic unsent binding, both currently read private coordinates
retain their original product independently of every other source and timing
coordinate after the entire actual recall. No entry prior is refreshed. -/
theorem phaseTimingPlanPolicy_value_coordinates_of_history
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
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
 : ∃ played : some (control.execution.recall who, control.execution.observe (app) who) ∈
      (N).playedInformation who,
    let agent : Agent := ⟨who, ⟨some (control.execution.recall who,
      control.execution.observe (app) who), played⟩⟩
    let view := phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (app) who)
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    ∃ remainder : PMF (((p : {p // p ≠ pool agent}) → Parts p.val) ×
        ((point : {point // point ≠ view}) → (setup.informationModel
          (CommitmentInterface.forfeiture setup.program)).Choice who point.val)),
      (((app).policyMixture original family).posterior (control.execution.recall who)).map
          (fun memory => ((memory.1 (pool agent), memory.2 view),
            (fun p : {p // p ≠ pool agent} => memory.1 p.val,
              fun point : {point // point ≠ view} => memory.2 point.val))) =
        (weights (pool agent)).bind fun part =>
          (setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who view).bind
            fun choice => remainder.map fun rest => ((part, choice), rest) := by
  obtain ⟨played, _marginal⟩ := phaseTimingPlanPolicy_value_joint_of_history setup mode runtime
    leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
      weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control
        trace active clear event payload binding request unsent
  refine ⟨played, ?_⟩
  intro agent view sourcePrior original family
  let current := setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who view
  let posterior := ((app).policyMixture original family).posterior (control.execution.recall who)
  obtain ⟨sourceRest, sourceFactor⟩ := phaseTimingPlanPolicy_value_posterior_of_history setup mode
    runtime leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment
      mixed finite noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        (independentProduct weights) who control trace clear event payload binding request unsent
  obtain ⟨planRest, planFactor⟩ := (app).policyMixture_posterior_coordinate_extra weights
    sourcePrior
    family (pool agent) (control.execution.recall who) (fun before entry recorded plan other part =>
      congrArg (fun law : PMF (app).Action => law entry.action)
        (phaseTimingPlanPolicy_unread setup mode runtime leaks bounds initial horizon scheduler
          bound fallback wellFormed
            (setup.commitRecoveryValueAssessment wellFormed assessment who other) noise
              noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
                (control.execution.recall who) (control.execution.observe (app) who) played before
                  entry recorded plan part))
  let rest := planRest.map fun pair => (pair.1,
    fun point : {point // point ≠ view} => pair.2 point.val)
  refine ⟨rest, ?_⟩
  have sourceMarginal : posterior.map (fun memory => (memory.1,
      fun point : {point // point ≠ view} => memory.2 point.val)) = sourceRest := by
    have projected := congrArg (PMF.map Prod.snd) sourceFactor
    have mapped : posterior.map (fun memory => (memory.1,
        fun point : {point // point ≠ view} => memory.2 point.val)) =
          sourceRest.map (fun rest => rest) := by
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, PMF.map_const, PMF.bind_const]
        using projected
    exact mapped.trans (PMF.map_id _)
  have restFactor : sourceRest.map (fun pair => (pair.1 (pool agent),
      (fun p : {p // p ≠ pool agent} => pair.1 p.val, pair.2))) =
        (weights (pool agent)).bind (fun part => rest.map (Prod.mk part)) := by
    have projected := congrArg (PMF.map fun pair => (pair.1,
      (pair.2.1, fun point : {point // point ≠ view} => pair.2.2 point.val))) planFactor
    have mapped := congrArg (PMF.map fun pair => (pair.1 (pool agent),
      (fun p : {p // p ≠ pool agent} => pair.1 p.val, pair.2))) sourceMarginal
    have same : posterior.map (fun memory => (memory.1 (pool agent),
        (fun p : {p // p ≠ pool agent} => memory.1 p.val,
          fun point : {point // point ≠ view} => memory.2 point.val))) =
        (weights (pool agent)).bind (fun part => rest.map (Prod.mk part)) := by
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, rest] using projected
    have equality : sourceRest.map (fun pair => (pair.1 (pool agent),
        (fun p : {p // p ≠ pool agent} => pair.1 p.val, pair.2))) =
          posterior.map (fun memory => (memory.1 (pool agent),
            (fun p : {p // p ≠ pool agent} => memory.1 p.val,
              fun point : {point // point ≠ view} => memory.2 point.val))) := by
      simpa only [PMF.map_comp, Function.comp_def] using mapped.symm
    exact equality.trans same
  have projected := congrArg (PMF.map fun pair =>
    ((pair.2.1 (pool agent), pair.1),
      (fun p : {p // p ≠ pool agent} => pair.2.1 p.val, pair.2.2))) sourceFactor
  change posterior.map _ = _
  calc
    _ = current.bind (fun choice => sourceRest.map (fun pair =>
          ((pair.1 (pool agent), choice),
            (fun p : {p // p ≠ pool agent} => pair.1 p.val, pair.2)))) := by
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, current] using projected
    _ = current.bind (fun choice => (weights (pool agent)).bind fun part =>
          rest.map fun tail => ((part, choice), tail)) := by
      apply congrArg (PMF.bind current)
      funext choice
      have transformed := congrArg (PMF.map fun pair => ((pair.1, choice), pair.2)) restFactor
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def] using transformed
    _ = _ := PMF.bind_comm current (weights (pool agent)) _

end Vegas
