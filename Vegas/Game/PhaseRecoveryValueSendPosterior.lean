/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueMarkedFuture
import Vegas.Game.PhaseRecoveryValueFutureProduct
import Vegas.Game.PhaseRecoveryValueFuture
import Interaction.ReactiveMixtureExtraCoordinate
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Remaining actual likelihood after observing a binding send -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

private theorem posterior_readout_of_product {Memory Action Readout : Type}
    (prior : PMF Memory) (responses : Memory → PMF Action) (read : Memory → Readout)
    (law : PMF Action)
    (factor : prior.bind (fun memory => (responses memory).map
      (fun action => (action, read memory))) =
        law.bind (fun action => (prior.map read).map (Prod.mk action)))
    (action : Action) :
    ((fiberPosterior (prior.bind fun memory => (responses memory).map
        (fun action => (action, memory))) Prod.fst action).map Prod.snd).map read =
      prior.map read := by
  let joint := prior.bind fun memory => (responses memory).map (fun action => (action, memory))
  have tagged : joint.map (fun pair => (pair.1, read pair.2)) =
      law.bind (fun action => (prior.map read).map (Prod.mk action)) := by
    simpa only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def] using factor
  have transported : ((fiberPosterior joint Prod.fst action).map Prod.snd).map read =
      (fiberPosterior (joint.map (fun pair => (pair.1, read pair.2))) Prod.fst action).map
        Prod.snd := by
    by_cases present : action ∈ (joint.map Prod.fst).support
    · have moved := map_fiberPosterior_readout joint
        (fun pair => (pair.1, read pair.2)) Prod.fst action present
      have mapped := congrArg (PMF.map Prod.snd) moved
      simpa only [PMF.map_comp, Function.comp_def] using mapped
    · have absent : action ∉ ((joint.map (fun pair => (pair.1, read pair.2))).map
          Prod.fst).support := by
        simpa only [PMF.map_comp, Function.comp_def] using present
      rw [fiberPosterior_of_not_mem_support _ _ present,
        fiberPosterior_of_not_mem_support _ _ absent]
      simp only [PMF.map_comp, Function.comp_def]
  change ((fiberPosterior joint Prod.fst action).map Prod.snd).map read = _
  rw [transported, tagged]
  exact fiberPosterior_snd_bindPairLaw_const law (prior.map read) action

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

local instance sendPosteriorPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- Observing the actual binding send does not change the implementation's
law of its complete later recorded likelihood. The consumed source and timing
coordinates can update, while every coordinate read later keeps its exact law. -/
theorem phaseTimingPlanPolicy_send_future_posterior_of_history
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
    (final : (app).Control)
    (finalTrace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (finalClear : final.execution.application.current.excluded = ∅)
    (sentRecord : (app).PlayerEntry) (suffix : List (app).PlayerEntry)
    (recalled : final.execution.recall who = control.execution.recall who ++ sentRecord :: suffix)
    (viewed : sentRecord.beforeView = control.execution.observe (app) who)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : sentRecord.action.transmission = some material)
    (candidate : Handle (serviceGraph setup mode))
    (named : material.call.packet = .commitment event candidate) :
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let posterior := ((app).policyMixture original family).posterior (control.execution.recall who)
    let futureWeight := fun memory => ∏ index : Fin suffix.length,
      (family memory (control.execution.recall who ++ sentRecord :: suffix.take index.val)
        suffix[index.val].beforeView suffix[index.val].action).toReal
    (((app).policyMixture original family).posterior
        (control.execution.recall who ++ [sentRecord])).map futureWeight =
      posterior.map futureWeight := by
  intro sourcePrior original family posterior futureWeight
  have independent := phaseTimingPlanPolicy_response_future_product_of_history setup mode runtime
    leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
      finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control trace active clear event payload binding request unsent final finalTrace finalClear
          sentRecord suffix recalled viewed material transmitted candidate named
  rw [ReactiveApplication.Implementation.posterior_snoc]
  change ((fiberPosterior (posterior.bind fun memory =>
    (family memory (control.execution.recall who) sentRecord.beforeView).map
      (fun response => (response, memory))) Prod.fst sentRecord.action).map Prod.snd).map
        futureWeight = posterior.map futureWeight
  have responseEq (memory) : family memory (control.execution.recall who) sentRecord.beforeView =
      family memory (control.execution.recall who) (control.execution.observe (app) who) :=
    congrArg (family memory (control.execution.recall who)) viewed
  have current := posterior_readout_of_product posterior
    (fun memory => family memory (control.execution.recall who)
      (control.execution.observe (app) who)) futureWeight
    (((app).policyMixture original family).policy (control.execution.recall who)
      (control.execution.observe (app) who)) independent sentRecord.action
  have jointEq : (posterior.bind fun memory =>
      (family memory (control.execution.recall who) sentRecord.beforeView).map
        (fun response => (response, memory))) =
      posterior.bind (fun memory =>
        (family memory (control.execution.recall who) (control.execution.observe (app) who)).map
          (fun response => (response, memory))) := by
    apply congrArg (PMF.bind posterior)
    funext memory
    exact congrArg (PMF.map fun response => (response, memory)) (responseEq memory)
  exact (congrArg (fun joint => ((fiberPosterior joint Prod.fst sentRecord.action).map
    Prod.snd).map futureWeight) jointEq).trans current

end Vegas
