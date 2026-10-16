/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValuePlan
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Original source coordinates unread by actual response recall -/

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

open Classical in
/-- Before an actual unsent binding callback, changing only its current
ordinary source-policy coordinate preserves every observed own response atom.
Actual raw sends, repeated silent waits, openings and idle callbacks are all
classified from the genuine initialized history; no source-origin or sorted
recall premise is supplied. -/
theorem phaseTimingPlanPolicy_source_coordinate_unread
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout selected = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (same : ∀ point, point ≠ phaseSourceView? setup mode runtime leaks who selected
      (control.execution.observe (app) who) → first point = second point) :
    ∀ (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry),
      earlier ++ [entry] <+: control.execution.recall who →
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who
              first) noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
                plan who earlier entry.beforeView entry.action =
          phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who
              second) noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
                plan who earlier entry.beforeView entry.action := by
  intro earlier entry recorded
  obtain ⟨later, recalled⟩ := recorded
  have recalled : control.execution.recall who = earlier ++ entry :: later := by
    simpa only [List.append_assoc, List.singleton_append] using recalled.symm
  obtain ⟨before, prior, isPrefix, active, pastEq, viewed, allowed⟩ :=
    (menu).recorded_response_at initial horizon scheduler control trace who earlier entry later
      recalled
  have previousClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have raw := (menu).toRawTrace initial horizon scheduler prior
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some before) := by
    change ¬ (before.remaining = 0 ∧ before.actor = none)
    rintro ⟨_, absent⟩
    rw [active] at absent
    cases absent
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some before, prior⟩) running
  have observed : (N).infoOf who prior =
      some (before.execution.recall who, before.execution.observe (app) who) :=
    ((menu).info initial horizon scheduler who prior).trans (by
      simp only [ReactiveApplication.observe, active, ite_true])
  rw [observed] at played
  have beforeEq : before = ⟨before.remaining, some who, before.execution⟩ := by
    cases before with
    | mk remaining actor execution => cases active; rfl
  have beforeTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some who, before.execution⟩) := beforeEq ▸ prior
  let firstSource := setup.commitRecoveryValueAssessment wellFormed assessment who first
  let secondSource := setup.commitRecoveryValueAssessment wellFormed assessment who second
  by_cases requested : ∃ coordinate, before.execution.application.SeedRequest who coordinate
  · obtain ⟨⟨attempt, event⟩, oldRequest⟩ := requested
    have address : attempt = before.execution.application.attempt := oldRequest.1
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner kind outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans oldRequest.2.2.2.1)
        subst owner
        by_cases silent : entry.action = ⟨none⟩
        · rw [← pastEq, viewed, silent]
          have sourceTrace : ((app).protocol (setup.initialLaw.map fun draw =>
              PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) horizon scheduler).Trace
                (some before) := by
            have initialEq : initial = setup.initialLaw.map (fun draw =>
                PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) := PMF.map_comp ..
            exact initialEq ▸ raw
          exact phaseTimingPlanPolicy_value_silence_of_history setup mode runtime leaks bounds
            initial horizon scheduler bound fallback wellFormed assessment mixed noise
              noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who first
                second runtimePlan maximal before sourceTrace valid previousClear event kind
                  outputEq oldRequest played
        · obtain ⟨material, transmitted⟩ :
              ∃ material, entry.action.transmission = some material := by
            cases transmitted : entry.action.transmission with
            | none =>
                apply False.elim
                apply silent
                cases actionEq : entry.action with
                | mk transmission => simp only [actionEq] at transmitted; cases transmitted; rfl
            | some material => exact ⟨material, rfl⟩
          have actionEq : entry.action = ⟨some material⟩ := by
            cases actionEq : entry.action with
            | mk transmission => simp only [actionEq] at transmitted; cases transmitted; rfl
          have offered : (⟨some material⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime
              leaks bounds who (before.execution.recall who)
                (before.execution.observe (app) who) := by
            change entry.action ∈ PhaseCount.onePacketActions runtime leaks bounds who earlier
              (before.execution.observe (app) who) at allowed
            simpa only [pastEq, actionEq] using allowed
          obtain ⟨serial, preparation, evidence, materialEq, _bounded, _fresh⟩ :=
            PhaseCount.onePacket_binding_shape runtime leaks bounds runtimePlan
              (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler
                before.remaining who before.execution beforeTrace event kind outputEq oldRequest
                  material offered
          have different := phaseSourceView?_ne_recorded_binding_of_unsent setup mode runtime leaks
            bounds runtimePlan inputs horizon scheduler trace clear who earlier entry later recalled
              material transmitted event (who, .prepared serial) (by rw [materialEq]) selected
                payload binding request unsent
          have localSame := same _ different
          rw [viewed] at localSame
          have equality := phaseTimingPlanPolicy_value_binding_congr setup mode runtime leaks
            bounds initial horizon scheduler bound fallback wellFormed assessment noise
              noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who first
                second before.execution valid previousClear event kind outputEq oldRequest played
                  localSame
          rw [← pastEq, viewed]
          exact congrArg (fun law : PMF (app).Action => law entry.action) equality
    | resolve owner kind field checks outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans oldRequest.2.2.2.1)
        subst owner
        have equality := phaseTimingPlanPolicy_opening_congr setup mode runtime leaks bounds
          initial horizon scheduler bound fallback wellFormed firstSource secondSource noise
            noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
              before.execution valid previousClear event kind field checks outputEq codeEq
                oldRequest played
        rw [← pastEq, viewed]
        exact congrArg (fun law : PMF (app).Action => law entry.action) equality
    | sample kind law outputEq codeEq =>
        have noOwner : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have owned := oldRequest.2.2.2.1
        rw [noOwner] at owned
        cases owned
  · have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds
      runtimePlan inputs horizon scheduler before.remaining who before.execution beforeTrace
        previousClear (fun coordinate present => requested ⟨coordinate, present⟩)
    have forced (source : setup.commitRecoveryModel.BehavioralAssessment) :
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
              slotNonnegative slotBounded plan who (before.execution.recall who)
                (before.execution.observe (app) who) = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro response supported
      have offered := phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial
        horizon scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded plan who _ _ response supported
      change response ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (before.execution.recall who) (before.execution.observe (app) who) at offered
      rw [singleton] at offered
      exact Finset.mem_singleton.mp offered
    rw [← pastEq, viewed, forced, forced]

end Vegas
