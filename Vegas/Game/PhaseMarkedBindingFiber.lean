/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseMarkedRepairMass
import Vegas.Game.PhaseRepairMarkedHistory

/-! # Actual binding-history repair inside the focal information fiber -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Whole operational repair gives a genuine history at the SAME full
information of every other player, retaining every possible selected raw
binding-record decomposition and the exact counterfactual factor. -/
theorem phase_marked_repair_in_focal_fiber (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (owner focal : Player) (different : focal ≠ owner)
    (profile : ∀ player, (N).BehavioralPolicy player) (site : (N).InformationSite focal)
    (history : (N).InformationHistory focal site.1)
    (control : (phaseApplication runtime leaks).Control)
    (atControl : history.1.state = some control) (active : control.actor = some focal)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (clear : control.execution.application.current.excluded = ∅)
    (request : control.execution.application.SeedRequest focal
      ⟨control.execution.application.attempt, event⟩) :
    ∃ image : (N).InformationHistory focal site.1,
      (N).counterfactualReachProbability profile owner history.1.trace =
        (N).counterfactualReachProbability profile owner image.1.trace ∧
      PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler owner
        ((N).ownPlay owner history.1.trace) ((N).ownPlay owner image.1.trace) := by
  rcases history with ⟨⟨state, trace⟩, atSite⟩
  change state = some control at atControl
  cases atControl
  obtain ⟨memory, image, imageTrace, _sends, _waits, frame, _recorded, _bindings, counterfactual,
    _ordinary, marked, _operationalRecall⟩ := phase_repair_marked_binding_history setup mode
      runtime leaks bounds plan
      horizon scheduler covered maximal owner profile control trace event focal payload output
        clear request
  have sameInfo : (N).infoOf focal trace = (N).infoOf focal imageTrace := by
    change
      ((PhaseCount.onePacketMenu runtime leaks bounds).signals initial horizon scheduler).infoOf
      focal trace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).signals initial horizon scheduler).infoOf
        focal imageTrace
    rw [ReactiveApplication.ResponseMenu.info, ReactiveApplication.ResponseMenu.info]
    simp only [ReactiveApplication.observe, active, ↓reduceIte]
    exact congrArg some (frame.foreign_input focal different)
  let targetHistory : (N).InformationHistory focal site.1 :=
    ⟨⟨_, imageTrace⟩, sameInfo.symm.trans atSite⟩
  have word (current : (phaseApplication runtime leaks).Control)
      (currentTrace : (E).Trace (some current)) :
      (N).ownPlay owner currentTrace =
        (phaseApplication runtime leaks).recallOwnPlay (current.execution.recall owner) := by
    change
      ((PhaseCount.onePacketMenu runtime leaks bounds).signals initial horizon scheduler).ownPlay
      owner currentTrace = _
    rw [← ReactiveApplication.ResponseMenu.ownPlay_toRawTrace,
      ReactiveApplication.trace_ownPlay]
    rfl
  refine ⟨targetHistory, counterfactual, ?_⟩
  change PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler owner
    ((N).ownPlay owner trace) ((N).ownPlay owner imageTrace)
  rw [word control trace, word _ imageTrace]
  exact marked

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

variable (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
  (floor : ℝ) (positive : 0 < floor)
  (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
    (choice : setup.commitRecoveryModel.Choice player site.1),
    floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
  (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
  (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)

local notation "strategy" => phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial
  horizon scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
    slotWeight slotPositive.le slotBounded

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))) scheduler]

include maximal nature capacity positive floored in
open Classical in
/-- Every actual clear focal binding-history group admits a many-to-one repair
whose selected RAW-mixture contributions obey the fixed-horizon mass bound.
The target histories, complete focal information, counterfactual equality and
all marked callback pairings are derived from the actual operational driver. -/
theorem phase_raw_binding_fiber_mass_le
    (covered : bounds.CoversOutputValues) (owner focal : Player) (different : focal ≠ owner)
    (site : (N).InformationSite focal)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (output : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (histories : Finset ((N).InformationHistory focal site.1))
    (genuine : ∀ history ∈ histories,
      ∃ control : (phaseApplication runtime leaks).Control,
        history.1.state = some control ∧ control.actor = some focal ∧
          control.execution.application.current.excluded = ∅ ∧
          control.execution.application.SeedRequest focal
            ⟨control.execution.application.attempt, event⟩)
    (before after : (N).InformationHistory focal site.1 →
      List ((N).InfoState owner × (E).Action owner))
    (marked : (N).InformationHistory focal site.1 → (N).InfoState owner × (E).Action owner)
    (records : ∀ history ∈ histories,
      (N).ownPlay owner history.1.trace = before history ++ marked history :: after history)
    (rawBinding : ∀ history ∈ histories,
      phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler owner
        (marked history)) :
    ∃ repair : (N).InformationHistory focal site.1 → (N).InformationHistory focal site.1,
      (∑ history ∈ histories,
        phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler noise owner
          strategy history.1 (before history) (marked history) (after history)) ≤
        (Nat.card (E).History : ℝ) *
          (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
            (2 * horizon + 1) * (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) *
              InformationModel.finiteHistoryReach (M := N) strategy focal site
                (histories.image repair) := by
  have candidates : ∀ history ∈ histories,
      ∃ image : (N).InformationHistory focal site.1,
        (N).counterfactualReachProbability strategy owner history.1.trace =
          (N).counterfactualReachProbability strategy owner image.1.trace ∧
        PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler owner
          ((N).ownPlay owner history.1.trace) ((N).ownPlay owner image.1.trace) := by
    intro history member
    obtain ⟨control, atControl, active, clear, request⟩ := genuine history member
    exact phase_marked_repair_in_focal_fiber setup mode runtime leaks bounds plan horizon scheduler
      covered maximal owner focal different strategy site history control atControl active event
        payload
        output clear request
  let repair := fun history : (N).InformationHistory focal site.1 =>
    if member : history ∈ histories then Classical.choose (candidates history member) else history
  have repaired (history : (N).InformationHistory focal site.1) (member : history ∈ histories) :
      (N).counterfactualReachProbability strategy owner history.1.trace =
        (N).counterfactualReachProbability strategy owner (repair history).1.trace ∧
      PhaseRepairMarkedBindings setup mode runtime leaks bounds plan horizon scheduler owner
        ((N).ownPlay owner history.1.trace) ((N).ownPlay owner (repair history).1.trace) := by
    dsimp only [repair]
    rw [dite_eq_left member]
    exact Classical.choose_spec (candidates history member)
  refine ⟨repair, ?_⟩
  apply phase_raw_history_group_mass_le setup mode runtime leaks bounds plan horizon scheduler
    finite wellFormed target approximation maximal n capacity floor positive floored noise
      noiseNonnegative noiseSmall slotWeight slotPositive slotBounded owner focal site histories
        repair before after marked records
  · intro history member
    obtain ⟨targetBefore, targetMarked, targetAfter, sendsBefore, waitsBefore, sendsAfter,
      waitsAfter,
      targetRecords, beforePair, markedPair, afterPair⟩ :=
      (repaired history member).2 (before history) (marked history) (after history)
        (records history member) (rawBinding history member)
    exact ⟨targetBefore, targetAfter, targetMarked, sendsBefore, waitsBefore, sendsAfter,
      waitsAfter,
      targetRecords, beforePair, markedPair, afterPair⟩
  · intro history member
    exact (repaired history member).1

end Vegas
