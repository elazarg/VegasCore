/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueFuture
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Actual downstream products after binding sends -/

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
/-- The complete product of the actual later response atoms is unchanged
when only the already-sent source coordinate changes. Every factor is derived
from the actual recorded history, with the original noisy future law retained. -/
theorem phaseTimingPlanPolicy_source_after_send_product
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
    (suffix : List (app).PlayerEntry)
    (recalled : control.execution.recall who = firstPast ++ sentRecord :: suffix) :
    let firstPolicy := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who first)
        noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
    let secondPolicy := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who second) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
    (∏ index : Fin suffix.length,
      (firstPolicy (firstPast ++ sentRecord :: suffix.take index.val)
        suffix[index.val].beforeView suffix[index.val].action).toReal) =
      ∏ index : Fin suffix.length,
        (secondPolicy (firstPast ++ sentRecord :: suffix.take index.val)
          suffix[index.val].beforeView suffix[index.val].action).toReal := by
  intro firstPolicy secondPolicy
  apply Finset.prod_congr rfl
  intro index _member
  have cut : suffix.take (index.val + 1) ++ suffix.drop (index.val + 1) = suffix :=
    List.take_append_drop ..
  rw [List.take_succ_eq_append_getElem index.isLt] at cut
  have split : suffix = suffix.take index.val ++ suffix[index.val] ::
      suffix.drop (index.val + 1) := by
    simpa only [List.append_assoc, List.singleton_append] using cut.symm
  have recorded : control.execution.recall who = firstPast ++ sentRecord ::
      suffix.take index.val ++ suffix[index.val] :: suffix.drop (index.val + 1) := by
    exact recalled.trans (by
      simpa only [List.cons_append, List.append_assoc] using
        congrArg (fun rest => firstPast ++ sentRecord :: rest) split)
  exact congrArg ENNReal.toReal
    (phaseTimingPlanPolicy_source_coordinate_after_send setup mode runtime leaks bounds runtimePlan
      horizon scheduler bound maximal fallback wellFormed assessment mixed noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan who first second control trace
          clear
          firstPast sentRecord sentMaterial sentTransmission sentEvent candidate sentNamed same
            (suffix.take index.val) suffix[index.val] (suffix.drop (index.val + 1)) recorded)

open Classical in
/-- The full actual downstream response product does not read an earlier
played timing-pool coordinate. All later played inputs and full prior recalls
are extracted from the same initialized counted history. -/
theorem phaseTimingPlanPolicy_prior_part_product
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (firstPast : List (app).PlayerEntry) (sentRecord : (app).PlayerEntry)
    (suffix : List (app).PlayerEntry)
    (recalled : control.execution.recall who = firstPast ++ sentRecord :: suffix)
    (oldPlayed : some (firstPast, sentRecord.beforeView) ∈ (N).playedInformation who) :
    let previous : Agent := ⟨who, ⟨some (firstPast, sentRecord.beforeView), oldPlayed⟩⟩
    ∀ (plan : (p : Pool) → Parts p)
      (part : Parts (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        previous)),
      let changed := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded (Function.update plan
            (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
              previous) part) who
      let original := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
        scheduler
        bound fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded plan who
      (∏ index : Fin suffix.length,
        (changed (firstPast ++ sentRecord :: suffix.take index.val)
          suffix[index.val].beforeView suffix[index.val].action).toReal) =
        ∏ index : Fin suffix.length,
          (original (firstPast ++ sentRecord :: suffix.take index.val)
            suffix[index.val].beforeView suffix[index.val].action).toReal := by
  intro previous plan part changed original
  apply Finset.prod_congr rfl
  intro index _member
  let past := firstPast ++ sentRecord :: suffix.take index.val
  have cut : suffix.take (index.val + 1) ++ suffix.drop (index.val + 1) = suffix :=
    List.take_append_drop ..
  rw [List.take_succ_eq_append_getElem index.isLt] at cut
  have split : suffix = suffix.take index.val ++ suffix[index.val] ::
      suffix.drop (index.val + 1) := by
    simpa only [List.append_assoc, List.singleton_append] using cut.symm
  have recorded : control.execution.recall who = past ++ suffix[index.val] ::
      suffix.drop (index.val + 1) := recalled.trans (by
    simpa only [past, List.cons_append, List.append_assoc] using
      congrArg (fun rest => firstPast ++ sentRecord :: rest) split)
  obtain ⟨before, prior, _isPrefix, active, pastEq, viewed, _allowed⟩ :=
    (menu).recorded_response_at initial horizon scheduler control trace who past suffix[index.val]
      (suffix.drop (index.val + 1)) recorded
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some before) := by
    change ¬ (before.remaining = 0 ∧ before.actor = none)
    rintro ⟨_, absent⟩
    rw [active] at absent
    cases absent
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some before, prior⟩) running
  have observed : (N).infoOf who prior =
      some (past, suffix[index.val].beforeView) :=
    ((menu).info initial horizon scheduler who prior).trans (by
      simp only [ReactiveApplication.observe, active, ite_true, pastEq, ← viewed])
  rw [observed] at played
  have earlier : firstPast ++ [sentRecord] <+: past := by
    refine ⟨suffix.take index.val, ?_⟩
    simp only [past, List.append_assoc, List.singleton_append]
  have equality := phaseTimingPlanPolicy_prior_part_unread setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound fallback wellFormed source noise noiseNonnegative
      noiseBounded slotWeight slotNonnegative slotBounded who firstPast sentRecord past
        suffix[index.val].beforeView earlier oldPlayed played plan part
  exact congrArg (fun law : PMF (app).Action => (law suffix[index.val].action).toReal) equality

end Vegas
