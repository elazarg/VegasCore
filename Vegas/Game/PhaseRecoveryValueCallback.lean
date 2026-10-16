/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueStrategy
import Vegas.Pending.PhaseBindingMemoryCallback

/-! # Complete clear-callback realization of immutable original policies -/

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
/-- At every genuine clear acting callback, the original immutable global
source-policy and timing-plan mixture equals the literal assembled response.
Sent or absent requests are silent; openings keep their complete raw law. -/
theorem phaseTimingPlanPolicy_value_callback_of_history
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
    (clear : control.execution.application.current.excluded = ∅) :
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
  let baseline := fun plan => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
    horizon scheduler bound fallback wellFormed assessment noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded plan who past view
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, absent⟩
    rw [active] at absent
    cases absent
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some control, trace⟩) running
  have observed : (N).infoOf who trace = some (past, view) :=
    ((menu).info initial horizon scheduler who trace).trans (by
      simp only [ReactiveApplication.observe, active, ite_true]
      rfl)
  rw [observed] at played
  let agent : Agent := ⟨who, ⟨some (past, view), played⟩⟩
  have insensitive (same : ∀ plan member, family (plan, member) past view = baseline plan) :
      ((app).policyMixture original family).policy past view =
        ((menu).decodeProfile initial horizon scheduler
          ((N).agentBehavior (N).playedInformation fallback
            (fun agent => (weights (pool agent)).bind
              (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler
                bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
                  slotNonnegative slotBounded agent)))) who past view := by
    let basePlan := fun p : Pool => (weights p).support_nonempty.choose
    let fixed := fun part => Function.update basePlan (pool agent) part
    let kernel := fun part : Parts (pool agent) => baseline (fixed part)
    have evaluation (plan : (p : Pool) → Parts p) :
        baseline plan = ((phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded agent (plan (pool agent))).map
              (fun choice => choice.1.getD ⟨none⟩)) := by
      exact (phaseTimingPlanPolicy_apply setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded plan who past view).trans (by rw [dite_eq_left played])
    have depends (memory) : family memory past view = kernel (memory.1 (pool agent)) := by
      apply (same memory.1 memory.2).trans
      apply (evaluation memory.1).trans
      apply (congrArg (fun part => ((phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded agent part).map
            (fun choice => choice.1.getD ⟨none⟩)))
              (Function.update_self (pool agent) (memory.1 (pool agent)) basePlan).symm).trans
      exact (evaluation (fixed (memory.1 (pool agent)))).symm
    have marginal := phaseTimingPlanPolicy_pool_posterior setup mode runtime leaks bounds
      runtimePlan horizon scheduler bound fallback wellFormed
        (fun member => setup.commitRecoveryValueAssessment wellFormed assessment who member)
          sourcePrior weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded who past view played
    calc
      _ = (((app).policyMixture original family).posterior past).bind
          (fun memory => kernel (memory.1 (pool agent))) := by
        rw [ReactiveApplication.policyMixture_policy]
        apply congrArg (PMF.bind _)
        exact funext depends
      _ = ((((app).policyMixture original family).posterior past).map
          (fun memory => memory.1 (pool agent))).bind kernel :=
        (PMF.bind_map (((app).policyMixture original family).posterior past)
          (fun memory => memory.1 (pool agent)) kernel).symm
      _ = (weights (pool agent)).bind kernel := congrArg (fun law => law.bind kernel) marginal
      _ = (weights (pool agent)).bind (fun part =>
          ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
              slotBounded agent part).map (fun choice => choice.1.getD ⟨none⟩))) := by
        apply congrArg (PMF.bind _)
        funext part
        exact (evaluation (fixed part)).trans (congrArg (fun part =>
          ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
              slotBounded agent part).map (fun choice => choice.1.getD ⟨none⟩)))
                (Function.update_self ..))
      _ = _ := by
        simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
          ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
          InformationModel.agentBehavior, dite_eq_left played]
        exact (PMF.map_bind ..).symm
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  have controlEq : control = ⟨control.remaining, some who, control.execution⟩ := by
    cases control with
    | mk remaining actor execution => cases active; rfl
  have actual : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨control.remaining, some who, control.execution⟩) := controlEq ▸ trace
  by_cases usable : ∃ coordinate, control.execution.application.SeedRequest who coordinate ∧
      ∀ message ∈ (app).outputs past, PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨⟨attempt, event⟩, request, unsent⟩ := usable
    have address : attempt = control.execution.application.attempt := request.1
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        exact phaseTimingPlanPolicy_value_strategy_of_history setup mode runtime leaks bounds
          runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
            weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
              control trace active clear event payload outputEq request unsent
    | resolve owner payload field checks outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        apply insensitive
        intro plan member
        exact phaseTimingPlanPolicy_opening_congr setup mode runtime leaks bounds initial horizon
          scheduler bound fallback wellFormed
            (setup.commitRecoveryValueAssessment wellFormed assessment who member) assessment noise
              noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
                control.execution valid clear event payload field checks outputEq codeEq request
                  played
    | sample payload law outputEq codeEq =>
        have noOwner : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have owned := request.2.2.2.1
        rw [noOwner] at owned
        cases owned
  · have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      runtimePlan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler
        control.remaining who control.execution actual clear usable
    have forced (source : setup.commitRecoveryModel.BehavioralAssessment) (plan) :
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
              slotNonnegative slotBounded plan who past view = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro response supported
      have offered := phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial
        horizon scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded plan who past view response supported
      change response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view at offered
      rw [singleton] at offered
      exact Finset.mem_singleton.mp offered
    apply insensitive
    intro plan member
    exact (forced _ plan).trans (forced assessment plan).symm

end Vegas
