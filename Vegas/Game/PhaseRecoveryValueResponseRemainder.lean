/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueCoordinates
import Vegas.Game.PhaseRecoveryValueFuture
import Interaction.ReactiveMixtureExtraCoordinate
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Actual binding responses and all remaining immutable memory -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

private theorem bind_response_product {Memory Coordinate Rest Action : Type}
    (prior : PMF Memory) (left : Memory → Coordinate) (right : Memory → Rest)
    (coordinates : PMF Coordinate) (remaining : PMF Rest)
    (factor : prior.map (fun memory => (left memory, right memory)) =
      coordinates.bind (fun coordinate => remaining.map (Prod.mk coordinate)))
    (kernel : Coordinate → PMF Action) :
    prior.bind (fun memory => (kernel (left memory)).map
        (fun action => (action, right memory))) =
      (coordinates.bind kernel).bind (fun action => remaining.map (Prod.mk action)) := by
  calc
    _ = (prior.map (fun memory => (left memory, right memory))).bind
          (fun pair => (kernel pair.1).map fun action => (action, pair.2)) :=
      (PMF.bind_map ..).symm
    _ = coordinates.bind (fun coordinate => remaining.bind fun tail =>
          (kernel coordinate).map fun action => (action, tail)) := by
      rw [factor, PMF.bind_bind]
      apply congrArg (PMF.bind coordinates)
      funext coordinate
      exact PMF.bind_map ..
    _ = coordinates.bind (fun coordinate => (kernel coordinate).bind fun action =>
          remaining.map (Prod.mk action)) := by
      apply congrArg (PMF.bind coordinates)
      funext coordinate
      simp_rw [← PMF.bind_pure_comp, Function.comp_def]
      exact PMF.bind_comm remaining (kernel coordinate) (fun tail action => PMF.pure (action, tail))
    _ = _ := (PMF.bind_bind ..).symm

private theorem response_remainder_of_coordinates {Memory Coordinate Rest Action : Type}
    (prior : PMF Memory) (left : Memory → Coordinate) (right : Memory → Rest)
    (coordinates : PMF Coordinate) (remaining : PMF Rest)
    (factor : prior.map (fun memory => (left memory, right memory)) =
      coordinates.bind (fun coordinate => remaining.map (Prod.mk coordinate)))
    (policies : Memory → PMF Action) (kernel : Coordinate → PMF Action)
    (depends : ∀ memory, policies memory = kernel (left memory)) :
    prior.bind (fun memory => (policies memory).map (fun action => (action, right memory))) =
      (prior.bind policies).bind (fun action => (prior.map right).map (Prod.mk action)) := by
  have rightLaw : prior.map right = remaining := by
    calc
      _ = (prior.map (fun memory => (left memory, right memory))).map Prod.snd :=
        (PMF.map_comp ..).symm
      _ = (coordinates.bind (fun coordinate => remaining.map (Prod.mk coordinate))).map
          Prod.snd := congrArg (PMF.map Prod.snd) factor
      _ = remaining := by
        have mapped := bindPairLaw_map_snd coordinates (fun _ => remaining)
        exact mapped.trans (PMF.bind_const _ _)
  have leftLaw : prior.map left = coordinates := by
    calc
      _ = (prior.map (fun memory => (left memory, right memory))).map Prod.fst :=
        (PMF.map_comp ..).symm
      _ = (coordinates.bind (fun coordinate => remaining.map (Prod.mk coordinate))).map
          Prod.fst := congrArg (PMF.map Prod.fst) factor
      _ = coordinates := bindPairLaw_map_fst coordinates (fun _ => remaining)
  have actionLaw : prior.bind policies = coordinates.bind kernel := by
    calc
      _ = prior.bind (fun memory => kernel (left memory)) := congrArg (PMF.bind prior)
        (funext depends)
      _ = (prior.map left).bind kernel := (PMF.bind_map ..).symm
      _ = _ := congrArg (fun law => law.bind kernel) leftLaw
  calc
    _ = prior.bind (fun memory => (kernel (left memory)).map
          (fun action => (action, right memory))) := by simp_rw [depends]
    _ = (coordinates.bind kernel).bind (fun action => remaining.map (Prod.mk action)) :=
      bind_response_product prior left right coordinates remaining factor kernel
    _ = _ := by rw [actionLaw, rightLaw]

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

local instance responsePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
private theorem response_kernel
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (control : (app).Control) {draw}
    (valid : control.execution.application.Invariant draw)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (played : some (control.execution.recall who, control.execution.observe (app) who) ∈
      (N).playedInformation who)
    (baseSource : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    let agent : Agent := ⟨who, ⟨some (control.execution.recall who,
      control.execution.observe (app) who), played⟩⟩
    let past := control.execution.recall who
    let view := control.execution.observe (app) who
    let decoded := phaseSourceView? setup mode runtime leaks who event view
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let coordinates := fun memory : ((p : Pool) → Parts p) × (setup.informationModel
        (CommitmentInterface.forfeiture setup.program)).Policy who =>
      (memory.1 (pool agent), memory.2 decoded)
    ∃ kernel : Parts (pool agent) × ((setup.informationModel
        (CommitmentInterface.forfeiture setup.program)).Choice who decoded) → PMF (app).Action,
      ∀ memory, family memory past view = kernel (coordinates memory) := by
  intro agent past view decoded family coordinates
  let basePlan := fun p : Pool => (weights p).support_nonempty.choose
  let fixed := fun part => Function.update basePlan (pool agent) part
  let changed := fun member => setup.commitRecoveryValueAssessment wellFormed assessment who member
  let kernel := fun pair : Parts (pool agent) × ((setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Choice who decoded) =>
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
    scheduler bound fallback wellFormed (changed (Function.update baseSource decoded pair.2)) noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded (fixed pair.1) who
        past view
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
  refine ⟨kernel, ?_⟩
  intro memory
  apply (planLocal (changed memory.2) memory.1 (fixed (memory.1 (pool agent))) (by
    simp only [fixed, Function.update_self])).trans
  exact phaseTimingPlanPolicy_value_binding_congr setup mode runtime leaks bounds initial horizon
    scheduler bound fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
      slotNonnegative slotBounded (fixed (memory.1 (pool agent))) who memory.2
        (Function.update baseSource decoded (memory.2 decoded)) control.execution valid clear
          event
          payload binding request played
            (@Function.update_self
              ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).InfoState
                who)
              ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).Choice
                who) (Classical.decEq _) decoded (memory.2 decoded) baseSource).symm

open Classical in
/-- At an actual clear unsent binding, the original immutable implementation's
current raw response is independent of all remaining source-policy and timing
coordinates. RAW noise and the actual entire own recall remain in the joint. -/
theorem phaseTimingPlanPolicy_response_remainder_of_history
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
    let decoded := phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (app) who)
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let posterior := ((app).policyMixture original family).posterior (control.execution.recall who)
    let readRest := fun memory : ((p : Pool) → Parts p) × (setup.informationModel
        (CommitmentInterface.forfeiture setup.program)).Policy who =>
      (fun p : {p // p ≠ pool agent} => memory.1 p.val,
        fun point : {point // point ≠ decoded} => memory.2 point.val)
    posterior.bind (fun memory =>
        (family memory (control.execution.recall who) (control.execution.observe (app) who)).map
          (fun response => (response, readRest memory))) =
      (((app).policyMixture original family).policy (control.execution.recall who)
        (control.execution.observe (app) who)).bind
          (fun response => (posterior.map readRest).map (Prod.mk response)) := by
  obtain ⟨played, factor⟩ := phaseTimingPlanPolicy_value_coordinates_of_history setup mode runtime
    leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
      finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control trace active clear event payload binding request unsent
  refine ⟨played, ?_⟩
  intro agent decoded sourcePrior original family posterior readRest
  obtain ⟨rest, factor⟩ := factor
  let past := control.execution.recall who
  let view := control.execution.observe (app) who
  let current := setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who
    decoded
  let coordinates := fun memory : ((p : Pool) → Parts p) × (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who =>
    (memory.1 (pool agent), memory.2 decoded)
  let coordinateLaw := (weights (pool agent)).bind fun part => current.map (Prod.mk part)
  have pairFactor : posterior.map (fun memory => (coordinates memory, readRest memory)) =
      coordinateLaw.bind (fun coordinate => rest.map (Prod.mk coordinate)) := by
    simpa only [coordinateLaw, PMF.bind_bind, PMF.bind_map, Function.comp_def] using factor
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  obtain ⟨kernel, depends⟩ := response_kernel setup mode runtime leaks bounds runtimePlan horizon
    scheduler bound fallback wellFormed assessment weights noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded who control valid clear event payload binding request
        played sourcePrior.support_nonempty.choose
  have locality : ∀ memory, family memory past view = kernel (coordinates memory) := depends
  have equality := response_remainder_of_coordinates posterior coordinates readRest coordinateLaw
    rest pairFactor (fun memory => family memory past view) kernel locality
  simpa only [ReactiveApplication.policyMixture_policy] using equality

end Vegas
