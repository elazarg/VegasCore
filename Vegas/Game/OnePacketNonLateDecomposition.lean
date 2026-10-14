/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketUnpendingSites

/-! # The value decomposition away from late deliveries, by pending event

Away from late deliveries, a forced site either has a pending event of its
player, and is then a first activation of its own next event, or has none.

**The continuation of an agent away from late deliveries.** At a site with a
pending event, the continuation value of the site (`Vegas.siteContinuation`); at
a site without one, the successful value of the prescribed component, since
there the player's own choices cannot complete or fail the next event
(`Vegas.nonLateContinuation`).

**The decomposition.** Under value-blind success at the sites with a pending
event, the successful part of every compared choice and of the prescribed
component is its success probability times the continuation value up to a
vanishing error, at every forced site away from late deliveries. The exclusion
payoff is at most the continuation value up to the error, with gap at most the
gap bound, wherever the site's failure set is nonempty
(`Vegas.onePacket_nonLateDecomposition_of_pending`). At a site without a pending
event the failure set is empty, and every compared choice is silence, which
succeeds like the prescribed component up to the uniform tier
(`Vegas.abs_siteSuccess_sub_prescribed_le_of_unpending`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- **The continuation of an agent away from late deliveries.** At a decision
information state without a pending event of its player, the successful value
of the prescribed component; elsewhere the continuation value of the agent
(`Vegas.siteContinuation`). -/
def nonLateContinuation (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1) (n : ℕ)
    (assessment : (onePacketN).BehavioralAssessment)
    (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) : ℝ :=
  if decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1 then
    if pendingEvent setup leaks agent.1 agent.2.1 = none then
      onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment ⟨agent.2.1, decision⟩
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent)
    else siteContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
      assessment (setup.intendedOpeningProfile (sequence n).strategy) agent
  else excludedPayoff agent.1

/-- **The value decomposition away from late deliveries, by pending event.** For
a well-formed setup under the asynchronous contract with timely delays and
retention of first covered canonical packets, with bounded utilities and a
vanishing scale, suppose value-blind success at the forced sites away from late
deliveries with a pending event: the completion value of each compared choice
and of the prescribed component is within a vanishing error of its success
probability times the site's continuation value. Then at every forced site away
from late deliveries the successful part of every compared choice and of the
prescribed component is its success probability times the continuation value of
`Vegas.nonLateContinuation` up to a vanishing error, and the exclusion payoff is
at most that continuation value up to the error, with gap at most the gap bound,
or the site has no pending event. -/
theorem onePacket_nonLateDecomposition_of_pending
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scale_vanishing : Tendsto scale atTop (nhds 0))
    (gapBound : ℝ) (gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound)
    (gapBound_nonneg : 0 ≤ gapBound) {slots : Nat}
    (valueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
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
            blindError n) :
    ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        ((excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
            continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound) ∨
          pendingEvent setup leaks who site.1 = none) ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site)) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site))) *
            continuation n ((onePacketN).agentAt site)| ≤ error n := by
  intro weights targetSequence assembled mixed bayes
  obtain ⟨blindError, blindLimit, blind⟩ := valueBlind weights targetSequence assembled mixed bayes
  obtain ⟨transportError, transportLimit, transportNonneg, holds⟩ :=
    siteDecomposition_of_completion setup leaks bounds horizon scheduler parameter utility
      excludedPayoff wellFormed contract timely retains lowerUtility upperUtility lower_le
      le_upper sequence below scale scale_pos scale_le_one scale_vanishing gapBound gap_le
      gapBound_nonneg weights targetSequence assembled
  let range := fun who : Player => max 0 (max (excludedPayoff who) (upperUtility who)) -
    min 0 (min (excludedPayoff who) (lowerUtility who))
  have rangeNonneg : ∀ who, 0 ≤ range who := fun who => by
    have := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
    have := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
    simp only [range]
    linarith
  let total := ∑ who, range who
  have rangeLe : ∀ who, range who ≤ total := fun who =>
    Finset.single_le_sum (fun player _ => rangeNonneg player) (Finset.mem_univ who)
  have totalNonneg : 0 ≤ total := Finset.sum_nonneg fun player _ => rangeNonneg player
  refine ⟨fun n => nonLateContinuation setup leaks bounds horizon scheduler parameter utility
      excludedPayoff sequence scale scale_pos scale_le_one n (targetSequence n),
    fun n => transportError n + |blindError n| + 2 * scale n ^ 3 * total, ?_,
    fun n who site notFree notKeyed => ?_⟩
  · have cube := ((scale_vanishing.pow 3).const_mul 2).mul_const total
    simpa using (transportLimit.add blindLimit.abs).add cube
  have cubeNonneg : 0 ≤ 2 * scale n ^ 3 * total := by
    have := (scale_pos n).le
    positivity
  have blindNonneg := abs_nonneg (blindError n)
  have transportZero := transportNonneg n
  by_cases pending : pendingEvent setup leaks who site.1 = none
  · -- Without a pending event the continuation is the prescribed success.
    have continuationEq : nonLateContinuation setup leaks bounds horizon scheduler parameter
        utility excludedPayoff sequence scale scale_pos scale_le_one n (targetSequence n)
        ((onePacketN).agentAt site) =
        onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
          excludedPayoff (targetSequence n) site (onePacketPrescribed setup leaks bounds horizon
            scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site)) := by
      unfold nonLateContinuation
      rw [dite_eq_left_of_eq_true (eq_true site.2)]
      simp only [pending, ↓reduceIte]
      rfl
    have emptyFailed : onePacketFailed setup leaks bounds horizon scheduler
        ((onePacketN).agentAt site) = ∅ := by
      unfold onePacketFailed
      change (match pendingEvent setup leaks who site.1 with
        | none => ∅
        | some event => EventFailedHistory setup leaks bounds horizon scheduler who event) = ∅
      rw [pending]
    have zeroFailure : ∀ law, onePacketSiteFailure setup leaks bounds horizon scheduler
        (targetSequence n) site law = 0 := fun law => by
      unfold onePacketSiteFailure localFailure
      rw [emptyFailed]
      simp only [Set.mem_empty_iff_false, ite_false]
      exact expect_constant _ 0
    obtain ⟨history, _⟩ := ((targetSequence n).belief who site).support_nonempty
    obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
      obtain ⟨_, _, action, member⟩ := site.2
      cases info : site.1 with
      | none =>
          rw [info] at member
          change some action = none at member
          cases member
      | some input => exact ⟨input.1, input.2, rfl⟩
    refine ⟨Or.inr pending, fun choice marked => ?_, ?_⟩
    · beta_reduce
      rw [zeroFailure, continuationEq, sub_zero, one_mul]
      refine (abs_siteSuccess_sub_prescribed_le_of_unpending setup leaks bounds horizon scheduler
        parameter utility excludedPayoff lowerUtility upperUtility lower_le le_upper sequence
        scale scale_pos scale_le_one n (targetSequence n) site atSite pending history choice
        marked).trans ?_
      have scaled : 2 * scale n ^ 3 * range who ≤ 2 * scale n ^ 3 * total :=
        mul_le_mul_of_nonneg_left (rangeLe who) (by have := (scale_pos n).le; positivity)
      change 2 * scale n ^ 3 * range who ≤ _
      linarith
    · beta_reduce
      rw [zeroFailure, continuationEq, sub_zero, one_mul, sub_self, abs_zero]
      linarith
  · -- With a pending event the continuation is the site's continuation value.
    have continuationEq : nonLateContinuation setup leaks bounds horizon scheduler parameter
        utility excludedPayoff sequence scale scale_pos scale_le_one n (targetSequence n)
        ((onePacketN).agentAt site) =
        siteContinuation setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy)
          ((onePacketN).agentAt site) := by
      unfold nonLateContinuation
      rw [dite_eq_left_of_eq_true (eq_true site.2)]
      simp only [pending, ↓reduceIte]
    obtain ⟨lower, gap, decompose⟩ := holds n who site
    obtain ⟨choices, prescribed⟩ := blind n who site notFree notKeyed pending
    beta_reduce
    rw [continuationEq]
    refine ⟨Or.inl ⟨by linarith, gap⟩, fun choice marked => ?_, ?_⟩
    · have near := decompose _ _ ((choices choice marked).trans (le_abs_self _))
      linarith
    · have near := decompose _ _ (prescribed.trans (le_abs_self _))
      linarith

end Vegas
