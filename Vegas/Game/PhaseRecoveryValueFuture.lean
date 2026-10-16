/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValuePlan
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Source coordinates unused after actual binding sends -/

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
/-- Once an actual permitted binding send has been recorded, changing only
that source coordinate preserves every later recorded own response atom.
Silence remains neutral, and a later permitted send queries a different source
coordinate. Accepted typed failures and arbitrary preparation are retained. -/
theorem phaseTimingPlanPolicy_source_coordinate_after_send
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
    (firstPast : List (app).PlayerEntry) (sentRecord : (app).PlayerEntry)
    (sentMaterial : WitnessedSubmission (serviceGraph setup mode))
    (sentTransmission : sentRecord.action.transmission = some sentMaterial)
    (sentEvent : (serviceGraph setup mode).EventId)
    (candidate : Handle (serviceGraph setup mode))
    (sentNamed : sentMaterial.call.packet = .commitment sentEvent candidate)
    (same : ∀ point, point ≠ phaseSourceView? setup mode runtime leaks who sentEvent
      sentRecord.beforeView → first point = second point)
    (between : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : control.execution.recall who =
      firstPast ++ sentRecord :: between ++ entry :: later) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who first)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (firstPast ++ sentRecord :: between) entry.beforeView entry.action =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who second)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (firstPast ++ sentRecord :: between) entry.beforeView entry.action := by
  let earlier := firstPast ++ sentRecord :: between
  change phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who first)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            earlier entry.beforeView entry.action =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who second)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            earlier entry.beforeView entry.action
  have recalled : control.execution.recall who = earlier ++ entry :: later := by
    simpa only [earlier, List.append_assoc, List.cons_append] using recalled
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
          have waiting := PhaseCount.unsent_of_nonsilent runtime leaks bounds runtimePlan
            (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining
              who before.execution beforeTrace ⟨before.execution.application.attempt, event⟩
                oldRequest material offered
          have oldRecalled : before.execution.recall who = firstPast ++ sentRecord :: between :=
            pastEq
          have different := phaseSourceView?_ne_recorded_binding_of_unsent setup mode runtime leaks
            bounds runtimePlan inputs horizon scheduler prior previousClear who firstPast sentRecord
              between oldRecalled sentMaterial sentTransmission sentEvent candidate sentNamed event
                kind outputEq oldRequest waiting
          have localSame := same _ (Ne.symm different)
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
        (fun coordinate present => requested ⟨coordinate, present⟩)
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


open Classical in
/-- A previously recorded pool coordinate cannot change a later played
response law. Genuine keyed parts do not recur because recall grows; the
unkeyed part is a singleton even when its pool occurs repeatedly. -/
theorem phaseTimingPlanPolicy_prior_part_unread
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (before : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (recorded : before ++ [entry] <+: past)
    (oldPlayed : some (before, entry.beforeView) ∈ (N).playedInformation who)
    (played : some (past, view) ∈ (N).playedInformation who) :
    let previous : Agent := ⟨who, ⟨some (before, entry.beforeView), oldPlayed⟩⟩
    ∀ (plan : (p : Pool) → Parts p)
      (part : Parts (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        previous)),
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded (Function.update plan
              (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
                previous) part) who past view =
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded plan who past view := by
  intro previous plan part
  let current : Agent := ⟨who, ⟨some (past, view), played⟩⟩
  let pool := phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
  have same : (Function.update plan (pool previous) part) (pool current) = plan (pool current) := by
    obtain singleton | fresh := phaseTimingPool_fresh_or_subsingleton setup mode runtime leaks
      bounds initial horizon scheduler bound who past view played
    · exact @Subsingleton.elim _ singleton _ _
    · exact Function.update_of_ne (Ne.symm (fresh before entry recorded oldPlayed)) _ _
  rw [phaseTimingPlanPolicy_apply, phaseTimingPlanPolicy_apply, dite_eq_left played,
    dite_eq_left played]
  exact congrArg (fun selected =>
    (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        current selected).map (fun choice => choice.1.getD ⟨none⟩)) same

end Vegas
