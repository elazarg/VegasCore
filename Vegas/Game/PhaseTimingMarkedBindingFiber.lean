/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingRepairLikelihood
import Vegas.Game.PhaseMarkedBindingFiber

/-! # Actual timing raw-send mass under finite many-to-one repair -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)


variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))) scheduler]

include maximal nature in
open Classical in
/-- Every group of actual opponent raw-send contributions is bounded within
the SAME focal information fiber under the actual arbitrary-weight timing
strategy. The operational driver derives the repaired histories, marked
callback pairs and exact counterfactual factors. -/
theorem phase_timing_raw_binding_fiber_mass_le
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
            slotPositive.le
            slotBounded agent))
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
            (2 * horizon + 1)) * InformationModel.finiteHistoryReach (M := N) strategy focal site
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
  apply InformationModel.sum_contribution_le_of_repair (M := N) strategy histories
    (histories.image repair) repair
    (fun history => phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler
      noise owner strategy history.1 (before history) (marked history) (after history))
    _ (by positivity) (Nat.card (E).History)
  · intro history member
    exact Finset.mem_image_of_mem repair member
  · intro image _member
    exact (Finset.card_filter_le _ _).trans
      (phase_history_group_card_le setup mode runtime leaks bounds plan horizon scheduler
        focal site histories)
  · intro history member
    obtain ⟨targetBefore, targetMarked, targetAfter, sendsBefore, waitsBefore, sendsAfter,
      waitsAfter, targetRecords, beforePair, markedPair, afterPair⟩ :=
      (repaired history member).2 (before history) (marked history) (after history)
        (records history member) (rawBinding history member)
    exact phase_timing_raw_historyReach_prefix_of_floor setup mode runtime leaks bounds plan
      maximal horizon scheduler bound finite wellFormed target approximation n capacity floor
        positive floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded
          weights strategy assembled owner history.1 (repair history).1 (before history)
            (after history) targetBefore targetAfter (marked history) targetMarked
              (records history member) targetRecords sendsBefore waitsBefore sendsAfter waitsAfter
                beforePair markedPair afterPair (repaired history member).1

end Vegas
