/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueResponseRemainder
import Vegas.Game.PhaseRecoveryValueFutureProduct
import Vegas.Game.PhaseRecoveryValueFuture
import Interaction.ReactiveMixtureExtraCoordinate
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Actual sent responses and all subsequent private likelihood factors -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

private theorem response_readout_product {Memory Rest Action : Type}
    (prior : PMF Memory) (responses : Memory → PMF Action) (right : Memory → Rest)
    (law : PMF Action)
    (factor : prior.bind (fun memory => (responses memory).map
      (fun action => (action, right memory))) =
        law.bind (fun action => (prior.map right).map (Prod.mk action)))
    (weight : Memory → ℝ) (readout : Rest → ℝ)
    (depends : ∀ memory, weight memory = readout (right memory)) :
    prior.bind (fun memory => (responses memory).map (fun action => (action, weight memory))) =
      law.bind (fun action => (prior.map weight).map (Prod.mk action)) := by
  have projected := congrArg (PMF.map fun pair => (pair.1, readout pair.2)) factor
  have weightEq : weight = fun memory => readout (right memory) := funext depends
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, weightEq] using projected

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

local instance futureResponsePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- At an actual binding send, the complete later observed response likelihood
is independent of the current raw response under the ORIGINAL private-memory
posterior. Both coordinates consumed here are absent from every later factor;
all original source failures and RAW atoms remain in this exact joint law. -/
theorem phaseTimingPlanPolicy_response_future_product_of_history
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
    posterior.bind (fun memory =>
        (family memory (control.execution.recall who) (control.execution.observe (app) who)).map
          (fun response => (response, futureWeight memory))) =
      (((app).policyMixture original family).policy (control.execution.recall who)
        (control.execution.observe (app) who)).bind
          (fun response => (posterior.map futureWeight).map (Prod.mk response)) := by
  rcases sentRecord with ⟨oldView, oldAction, oldEmission⟩
  change oldView = control.execution.observe (app) who at viewed
  subst oldView
  let sentRecord : (app).PlayerEntry :=
    ⟨control.execution.observe (app) who, oldAction, oldEmission⟩
  intro sourcePrior original family posterior futureWeight
  obtain ⟨played, responseRest⟩ := phaseTimingPlanPolicy_response_remainder_of_history setup mode
    runtime leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment
      mixed finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded who control trace active clear event payload binding request unsent
  let agent : Agent := ⟨who, ⟨some (control.execution.recall who,
    control.execution.observe (app) who), played⟩⟩
  let decoded := phaseSourceView? setup mode runtime leaks who event
    (control.execution.observe (app) who)
  let choices := fun point => (setup.informationModel
    (CommitmentInterface.forfeiture setup.program)).Choice who point
  let readRest := fun memory : ((p : Pool) → Parts p) × (∀ point, choices point) =>
    (fun p : {p // p ≠ pool agent} => memory.1 p.val,
      fun point : {point // point ≠ decoded} => memory.2 point.val)
  let defaultPart := (weights (pool agent)).support_nonempty.choose
  let defaultChoice := (setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy
    who decoded).support_nonempty.choose
  let restore := fun tail : ((p : {p // p ≠ pool agent}) → Parts p.val) ×
      ((point : {point // point ≠ decoded}) → choices point.val) =>
    ((Equiv.piSplitAt (pool agent) Parts).symm (defaultPart, tail.1),
      (Equiv.piSplitAt decoded choices).symm (defaultChoice, tail.2))
  let future := fun tail => futureWeight (restore tail)
  have depends (memory) : futureWeight memory = future (readRest memory) := by
    let nextSource := Function.update memory.2 decoded defaultChoice
    let nextPlan := Function.update memory.1 (pool agent) defaultPart
    have same : ∀ point, point ≠ phaseSourceView? setup mode runtime leaks who event
        sentRecord.beforeView → memory.2 point = nextSource point := by
      intro point different
      have different : point ≠ decoded := different
      dsimp only [nextSource]
      exact (@Function.update_of_ne _ _ (Classical.decEq _) _ _ different defaultChoice
        memory.2).symm
    have sourceEq := phaseTimingPlanPolicy_source_after_send_product setup mode runtime leaks
      bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed noise
        noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who memory.2
          nextSource final finalTrace finalClear (control.execution.recall who) sentRecord material
            transmitted event candidate named same suffix recalled
    have oldPlayed : some (control.execution.recall who, sentRecord.beforeView) ∈
        (N).playedInformation who := played
    have planEq := phaseTimingPlanPolicy_prior_part_product setup mode runtime leaks bounds
      runtimePlan horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who nextSource) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who final finalTrace
            (control.execution.recall who) sentRecord suffix recalled oldPlayed memory.1 defaultPart
    have restored : restore (readRest memory) = (nextPlan, nextSource) := by
      apply Prod.ext
      · funext p
        by_cases equal : p = pool agent
        · subst p
          simp [restore, readRest, Equiv.piSplitAt, nextPlan]
        · simp [restore, readRest, Equiv.piSplitAt, nextPlan, equal]
      · funext point
        by_cases equal : point = decoded
        · subst point
          simp [restore, readRest, Equiv.piSplitAt, nextSource]
        · simp [restore, readRest, Equiv.piSplitAt, nextSource, equal]
    change futureWeight memory = futureWeight (restore (readRest memory))
    rw [restored]
    exact sourceEq.trans planEq.symm
  exact response_readout_product posterior
    (fun memory => family memory (control.execution.recall who)
      (control.execution.observe (app) who)) readRest
    (((app).policyMixture original family).policy (control.execution.recall who)
      (control.execution.observe (app) who)) responseRest futureWeight future depends

end Vegas
