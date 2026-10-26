/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateDecomposition
import GameTheoryExtensions.Math.FiniteIntervalBounds

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
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- **The open inputs by value blindness.** The base inputs, a gap bound above
the spread of the utility over the exclusion payoff, late options covering the
bounded slots, value blindness of the completion value at forced late
deliveries and at the other forced sites, and value-blind late commitments. -/
structure OnePacketBlindInputs (upperUtility : Player → ℝ)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat) extends
    OnePacketBaseInputs setup runtime leaks bounds horizon scheduler sequence slots where
  /-- The gap bound is at least the spread of the utility over the exclusion
  payoff. -/
  gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound
  /-- The late options cover the bounded prepared slots. -/
  slotsCover : bounds.candidateCount ≤ slots
  /-- **Value blindness away from late deliveries.** -/
  nonLateValueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon
    scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu runtime leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
            (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          pendingEvent setup runtime leaks who site.1 ≠ none →
          (∀ choice, onePacketCompared setup runtime leaks bounds horizon scheduler who site
            choice →
            |siteStopValue setup runtime leaks bounds horizon scheduler parameter utility
              excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                (PMF.pure choice) -
              (1 - onePacketSiteFailure setup runtime leaks bounds horizon scheduler
                (targetSequence n)
                site (PMF.pure choice)) *
              siteValue setup runtime leaks bounds horizon scheduler parameter utility
                excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
              blindError n) ∧
          |siteStopValue setup runtime leaks bounds horizon scheduler parameter utility
            excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale
                scale_pos
                scale_le_one n ((onePacketN).agentAt site)) -
            (1 - onePacketSiteFailure setup runtime leaks bounds horizon scheduler (targetSequence
              n)
              site (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale
                scale_pos scale_le_one n ((onePacketN).agentAt site))) *
            siteValue setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The exclusion payoffs are bounded** by the sum over players of the spread
between the exclusion payoff, zero and the utility bounds. -/
theorem exclusionPayoffs_bounded (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who) :
    let budget := ∑ player, (max 0 (max (excludedPayoff player) (upperUtility player)) -
      min 0 (min (excludedPayoff player) (lowerUtility player)))
    0 ≤ budget ∧
      (∀ who readout, |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        budget) ∧ ∀ who, |excludedPayoff who| ≤ budget := by
  intro budget
  let lower := fun who => min 0 (min (excludedPayoff who) (lowerUtility who))
  let upper := fun who => max 0 (max (excludedPayoff who) (upperUtility who))
  have lowerNonpos : ∀ who, lower who ≤ 0 := fun _ => min_le_left _ _
  have upperNonneg : ∀ who, 0 ≤ upper who := fun _ => le_max_left _ _
  refine ⟨Finset.sum_nonneg (fun who _ => sub_nonneg.mpr
    ((lowerNonpos who).trans (upperNonneg who))), ?_, ?_⟩
  · intro who readout
    exact GameTheory.Math.abs_le_sum_interval_width lower upper lowerNonpos upperNonneg who
      (exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff lowerUtility
        upperUtility lower_le le_upper readout who)
  · intro who
    apply GameTheory.Math.abs_le_sum_interval_width lower upper lowerNonpos upperNonneg who
    exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩

end Vegas
