/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.OnePacketLateCommitments
import Vegas.Game.OnePacketValueTransport
import Vegas.Game.OnePacketUnpendingSites
import Vegas.Game.OnePacketLateRecords

/-! # Value-blindness inputs of the one-packet certificate

The base inputs, a gap bound above the spread of the utility over the exclusion
payoff, late options covering the bounded slots, value blindness of the
completion value at forced sites, and value-blind late commitments
(`Vegas.OnePacketBlindInputs`). The exclusion payoffs are bounded by the sum
over players of the spread between the exclusion payoff, zero and the utility
bounds (`Vegas.exclusionPayoffs_bounded`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- **The open inputs by value blindness.** The base inputs, a gap bound above
the spread of the utility over the exclusion payoff, late options covering the
bounded slots, value blindness of the completion value at forced late
deliveries and at the other forced sites, and value-blind late commitments. -/
structure OnePacketBlindInputs (upperUtility : Player → ℝ)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat) extends
    OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots where
  /-- The gap bound is at least the spread of the utility over the exclusion
  payoff. -/
  gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound
  /-- The late options cover the bounded prepared slots. -/
  slotsCover : bounds.candidateCount ≤ slots
  /-- **Value blindness away from late deliveries.** -/
  nonLateValueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          pendingEvent setup leaks who site.1 ≠ none →
          (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
            |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                (PMF.pure choice) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (PMF.pure choice)) *
              siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
              blindError n) ∧
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one n ((onePacketN).agentAt site)) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
                scale_pos scale_le_one n ((onePacketN).agentAt site))) *
            siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The exclusion payoffs are bounded** by the sum over players of the spread
between the exclusion payoff, zero and the utility bounds. -/
theorem exclusionPayoffs_bounded (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who) :
    (∀ who readout, |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
      ∑ player, (max 0 (max (excludedPayoff player) (upperUtility player)) -
        min 0 (min (excludedPayoff player) (lowerUtility player)))) ∧
    ∀ who, |excludedPayoff who| ≤
      ∑ player, (max 0 (max (excludedPayoff player) (upperUtility player)) -
        min 0 (min (excludedPayoff player) (lowerUtility player))) := by
  let range := fun who : Player => max 0 (max (excludedPayoff who) (upperUtility who)) -
    min 0 (min (excludedPayoff who) (lowerUtility who))
  have rangeNonneg : ∀ who, 0 ≤ range who := fun who => by
    have := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
    have := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
    simp only [range]
    linarith
  have rangeLe : ∀ who, range who ≤ ∑ player, range player := fun who =>
    Finset.single_le_sum (fun player _ => rangeNonneg player) (Finset.mem_univ who)
  have zeroLow := fun who => min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
  have zeroHigh := fun who => le_max_left 0 (max (excludedPayoff who) (upperUtility who))
  refine ⟨fun who readout => (abs_le.mpr ⟨?_, ?_⟩).trans (rangeLe who), fun who =>
    (abs_le.mpr ⟨?_, ?_⟩).trans (rangeLe who)⟩
  · have within := (exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff
      lowerUtility upperUtility lower_le le_upper readout who).1
    simp only [range]
    linarith [zeroHigh who]
  · have within := (exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff
      lowerUtility upperUtility lower_le le_upper readout who).2
    simp only [range]
    linarith [zeroLow who]
  · have low := min_le_left (excludedPayoff who) (lowerUtility who)
    have lower := min_le_right 0 (min (excludedPayoff who) (lowerUtility who))
    simp only [range]
    linarith [zeroHigh who]
  · have high := le_max_left (excludedPayoff who) (upperUtility who)
    have higher := le_max_right 0 (max (excludedPayoff who) (upperUtility who))
    simp only [range]
    linarith [zeroLow who]

end Vegas
