/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseMarkedRepairLikelihood
import GameTheoryExtensions.Analysis.Protocol.FiniteRepairMass
import Interaction.ReactiveFiniteAssessment

/-! # Actual marked raw-binding reach over finite repair fibers -/

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

/-- The selected raw-mixture own-action weight is multiplied by the REAL
counterfactual reach of the same actual history. -/
def phaseMarkedHistoryWeight (noise : ℝ) (who : Player)
    (profile : ∀ player, (N).BehavioralPolicy player) (history : (E).History)
    (before : List ((N).InfoState who × (E).Action who))
    (marked : (N).InfoState who × (E).Action who)
    (after : List ((N).InfoState who × (E).Action who)) : ℝ :=
  phaseRawMixtureOwnPlayWeight setup mode runtime leaks bounds plan horizon scheduler noise who
      (profile who) before marked after *
    (N).counterfactualReachProbability profile who history.trace

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal in
/-- The actual chronological marked-send comparison becomes a FULL reach
comparison using the counterfactual equality proved by the operational repair
induction. No history likelihood inequality is assumed. -/
theorem phase_raw_historyReach_prefix_of_floor
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : (E).History)
    (firstBefore firstAfter secondBefore secondAfter : List ((N).InfoState who × (E).Action who))
    (firstMarked secondMarked : (N).InfoState who × (E).Action who)
    (firstRecords : (N).ownPlay who first.trace = firstBefore ++ firstMarked :: firstAfter)
    (secondRecords : (N).ownPlay who second.trace = secondBefore ++ secondMarked :: secondAfter)
    (sendsBefore waitsBefore sendsAfter waitsAfter : Nat)
    (beforePair : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstBefore secondBefore sendsBefore waitsBefore)
    (markedPair : phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler
      who firstMarked secondMarked)
    (afterPair : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      firstAfter secondAfter sendsAfter waitsAfter) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le
        slotWeight slotPositive.le slotBounded
    (N).counterfactualReachProbability strategy who first.trace =
        (N).counterfactualReachProbability strategy who second.trace →
      phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler noise who
          strategy first firstBefore firstMarked firstAfter ≤
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
            (2 * horizon + 1) *
          (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) *
            ((N).historyReachWeight strategy second).toReal := by
  intro strategy counterfactual
  have bound := (phase_raw_playerReach_prefix_of_floor setup mode runtime leaks bounds plan horizon
    scheduler finite wellFormed target approximation maximal n capacity floor positive floored noise
      noiseNonnegative noiseSmall slotWeight slotPositive slotBounded who first second firstBefore
        firstAfter secondBefore secondAfter firstMarked secondMarked firstRecords secondRecords
          sendsBefore waitsBefore sendsAfter waitsAfter beforePair markedPair afterPair).2.2
  have scaled := mul_le_mul_of_nonneg_right bound
    ((N).counterfactualReachProbability_nonneg strategy who first.trace)
  dsimp only [phaseMarkedHistoryWeight]
  rw [counterfactual, mul_assoc] at scaled
  rw [← (N).historyReachProbability_eq_player_mul_counterfactual strategy who second.trace]
    at scaled
  simpa only [phaseMarkedHistoryWeight, counterfactual] using scaled

/-- Marking one raw-mixture draw is an exact additive decomposition of the
actual history reach. All other draws, including accepted source failures,
retain their full original probabilities. -/
theorem phase_marked_history_decomposition (n : Nat)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (history : (E).History)
    (before after : List ((N).InfoState who × (E).Action who))
    (marked : (N).InfoState who × (E).Action who)
    (records : (N).ownPlay who history.trace = before ++ marked :: after) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed (approximation.sequence n) noise noiseNonnegative noiseBounded
        slotWeight slotNonnegative slotBounded
    let conditional := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler who marked.1)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        initial horizon scheduler who marked.1)
    ((N).historyReachWeight strategy history).toReal =
      phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler noise who
          strategy history before marked after +
        (N).ownPlayReachProbability (strategy who) before *
          ((1 - noise) * ((conditional.map Subtype.val) (some marked.2)).toReal) *
          (N).ownPlayReachProbability (strategy who) after *
          (N).counterfactualReachProbability strategy who history.trace := by
  intro strategy conditional
  rw [(N).historyReachProbability_eq_player_mul_counterfactual strategy who history.trace,
    (N).playerReachProbability_eq_ownPlayReachProbability, records]
  have split := phase_marked_ownPlay_decomposition setup mode runtime leaks bounds plan horizon
    scheduler finite wellFormed target approximation n noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded who before after marked
  rw [split]
  dsimp only [phaseMarkedHistoryWeight]
  ring

section FiniteGroups

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

include nature in
/-- The number of actual histories in any information-fiber group is bounded
by the SAME finite native history carrier, independently of every policy rate. -/
theorem phase_history_group_card_le (who : Player) (site : (N).InformationSite who)
    (histories : Finset ((N).InformationHistory who site.1)) :
    histories.card ≤ Nat.card (E).History := by
  classical
  have : Finite (E).History := @ReactiveApplication.ResponseMenu.finite_history
    Player inferInstance (phaseApplication runtime leaks)
    (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler inferInstance nature
  let := Fintype.ofFinite (E).History
  have bound := (Finset.card_le_univ histories).trans
    (Fintype.card_le_of_injective (fun history : (N).InformationHistory who site.1 => history.1)
      Subtype.val_injective)
  simpa only [Nat.card_eq_fintype_card] using bound

include maximal nature capacity positive floored in
open Classical in
/-- A finite group of actual selected raw sends is bounded after a many-to-one
repair. Concrete callback pairings derive each contribution bound. The repair
may vary with the approximation; its multiplicity is nevertheless bounded by
the fixed all-legal-history cardinal, with no injectivity assumption. -/
theorem phase_raw_history_group_mass_le
    (owner focal : Player) (site : (N).InformationSite focal)
    (histories : Finset ((N).InformationHistory focal site.1))
    (repair : (N).InformationHistory focal site.1 → (N).InformationHistory focal site.1)
    (before after : (N).InformationHistory focal site.1 →
      List ((N).InfoState owner × (E).Action owner))
    (marked : (N).InformationHistory focal site.1 → (N).InfoState owner × (E).Action owner)
    (records : ∀ history ∈ histories,
      (N).ownPlay owner history.1.trace = before history ++ marked history :: after history)
    (paired : ∀ history ∈ histories,
      ∃ (targetBefore targetAfter : List ((N).InfoState owner × (E).Action owner))
        (targetMarked : (N).InfoState owner × (E).Action owner)
        (sendsBefore waitsBefore sendsAfter waitsAfter : Nat),
        (N).ownPlay owner (repair history).1.trace =
            targetBefore ++ targetMarked :: targetAfter ∧
          PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler owner
            (before history) targetBefore sendsBefore waitsBefore ∧
          phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler owner
            (marked history) targetMarked ∧
          PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler owner
            (after history) targetAfter sendsAfter waitsAfter)
    (counterfactual : ∀ history ∈ histories,
      (N).counterfactualReachProbability strategy owner history.1.trace =
        (N).counterfactualReachProbability strategy owner (repair history).1.trace) :
    ∑ history ∈ histories,
        phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler noise owner
          strategy history.1 (before history) (marked history) (after history) ≤
      (Nat.card (E).History : ℝ) *
        (noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) ^
          (2 * horizon + 1) * (1 + noise / ((1 - noise) * floor)) ^ (2 * horizon + 1)) *
            InformationModel.finiteHistoryReach (M := N) strategy focal site
              (histories.image repair) := by
  classical
  apply InformationModel.sum_contribution_le_of_repair (M := N) strategy histories
    (histories.image repair) repair
    (fun history => phaseMarkedHistoryWeight setup mode runtime leaks bounds plan horizon scheduler
      noise owner strategy history.1 (before history) (marked history) (after history))
    _ (by positivity) (Nat.card (E).History)
  · intro history member
    exact Finset.mem_image_of_mem repair member
  · intro target _member
    exact (Finset.card_filter_le _ _).trans
      (phase_history_group_card_le setup mode runtime leaks bounds plan horizon scheduler
        focal site histories)
  · intro history member
    obtain ⟨targetBefore, targetAfter, targetMarked, sendsBefore, waitsBefore, sendsAfter,
      waitsAfter,
      targetRecords, beforePair, markedPair, afterPair⟩ := paired history member
    exact phase_raw_historyReach_prefix_of_floor setup mode runtime leaks bounds plan horizon
      scheduler finite wellFormed target approximation maximal n capacity floor positive floored
        noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded owner history.1
          (repair history).1 (before history) (after history) targetBefore targetAfter
            (marked history) targetMarked (records history member) targetRecords sendsBefore
              waitsBefore sendsAfter waitsAfter beforePair markedPair afterPair
                (counterfactual history member)

end FiniteGroups

end Vegas
