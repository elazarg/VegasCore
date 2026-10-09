/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceTimingSorting
import Vegas.Examples.LateOpeningRuntimeAliceTimingFloor
import Vegas.Examples.LateOpeningRuntimeLabelCross
import Vegas.Examples.LateOpeningRuntimeBobSafeProbability
import Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality

/-! # Native sequential-equilibrium obstruction from lawful late timing

The original finite raw runtime has no sequential equilibrium reproducing
the selected source terminal-store and payoff law when the specified late
service is sufficiently reliable. The source and target semantics, actual
auditing, complete information and all private raw representations remain
unchanged. The obstruction concerns outcome preservation, not existence of
native sequential equilibria.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSeObstruction

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeFirstRetryComparison
  LateOpeningRuntimeAliceTimingValues LateOpeningRuntimePreservingLaw

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem accepted_information_representative (positive : 0 < weight)
    (bit seen : Bool) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1),
      history.1.state = some ⟨14, some bob, answerDecision bit 0 0 seen⟩ := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨14, some bob, answerDecision bit 0 0 seen⟩,
      (LateOpeningRuntimeLateHistories.answerDecision_trace weight nonnegative positive
        bit 0 0 seen (Or.inl rfl)).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      bob history (by change ¬ (14 = 0 ∧ some bob = none); simp) rfl
  exact ⟨site, ⟨history, information.symm⟩, rfl⟩

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- Actual SE consistency and actual sender rationality force one of the two
successful receiver transcripts to assign zero mass to Safe. -/
theorem equilibrium_excludes_one_safe_probability
    (positive : 0 < weight) (rewardPositive : 0 < reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobCollateral : 1 < deposit bob)
    (retryMarginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
      weight reward forfeit deposit)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ∃ bit,
      LateOpeningRuntimeAliceSuccessfulReduction.safeProbability
        (players weight nonnegative assessment.strategy) bit true = 0 ∨
      LateOpeningRuntimeAliceSuccessfulReduction.safeProbability
        (players weight nonnegative assessment.strategy) bit false = 0 := by
  obtain ⟨bit, sender, holder, sends, holds⟩ :=
    LateOpeningRuntimeAliceTimingSorting.opposite_emission_probabilities weight nonnegative
      reward forfeit deposit positive rewardPositive forfeitPositive aliceDepositNonnegative
        bobCollateral retryMarginPositive openingMarginPositive assessment equilibrium.1
  obtain ⟨seenSite, seenHistory, seenCurrent⟩ :=
    accepted_information_representative weight nonnegative positive bit true
  obtain ⟨unseenSite, unseenHistory, unseenCurrent⟩ :=
    accepted_information_representative weight nonnegative positive bit false
  have productZero := LateOpeningRuntimeLabelCross.label_belief_product_zero weight nonnegative
    bit seenSite seenHistory 0 seenCurrent unseenSite unseenHistory 0 unseenCurrent positive
      reward forfeit deposit rewardPositive.le forfeitPositive.le aliceDepositNonnegative
        bobCollateral openingMarginPositive assessment equilibrium sender holder sends holds
  refine ⟨bit, ?_⟩
  exact LateOpeningRuntimeBobSafeProbability.safeProbability_zero_of_label_product_zero
    weight nonnegative positive seenSite unseenSite seenHistory unseenHistory bit 0 0
      seenCurrent unseenCurrent reward forfeit deposit forfeitPositive.le
        (lt_trans zero_lt_one bobCollateral).le assessment equilibrium.1 holder sender productZero

/-- With collateral fixed, an arbitrarily reliable but fallible late service
can prevent every native SE from reproducing this source's selected joint law. -/
theorem equilibrium_terminal_law_ne_safe
    (positive : 0 < weight) (rewardPositive : 0 < reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobCollateral : 1 < deposit bob)
    (retryMarginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
      weight reward forfeit deposit)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (profitable : reward / 2 < 3 * inclusionProbability weight * reward / 4 -
      (1 - inclusionProbability weight) * (forfeit + deposit alice))
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      deposit assessment.strategy ≠ safeTerminalLaw reward := by
  intro same
  obtain ⟨bit, oneZero⟩ := equilibrium_excludes_one_safe_probability weight nonnegative
    reward forfeit deposit positive rewardPositive forfeitPositive aliceDepositNonnegative
      bobCollateral retryMarginPositive openingMarginPositive assessment equilibrium
  let material := disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)
  have available : (⟨some material⟩ : app.Action) ∈ rawMenu.actions alice
      ((firstLateDecision bit 0).recall alice) ((firstLateDecision bit 0).observe app alice) :=
    opening_in_raw_menu bit alice _ _
  have genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit 0) material := by
    change app.packet (firstLateDecision bit 0).application alice [] material = _
    exact firstLate_opening_packet bit 0
  have currentValue := first_genuine_response_value weight nonnegative reward forfeit deposit
    positive rewardPositive.le forfeitPositive aliceDepositNonnegative assessment equilibrium.1
      retryMarginPositive bobCollateral bit 0 material available genuine
  have bound := LateOpeningRuntimeAliceTimingFloor.first_value_lower_of_safe_zero weight nonnegative
    reward forfeit deposit positive rewardPositive.le forfeitPositive aliceDepositNonnegative
      (lt_trans zero_lt_one bobCollateral) assessment equilibrium.1
        (players weight nonnegative assessment.strategy) rfl bit 0 (by decide) oneZero
  have rationalBound := LateOpeningRuntimeAliceProtectedOptimality.first_value_ge_response
    weight nonnegative bit 0 reward forfeit deposit assessment equilibrium.1
      ⟨some material⟩ available
  have preservingBound :=
    LateOpeningRuntimeAliceProtectedOptimality.preserving_first_value_le_half_all_types
      weight nonnegative bit 0 reward forfeit deposit assessment equilibrium.1 same
  change LateOpeningRuntimeAliceFirstOptimality.responseValue weight nonnegative bit 0
    reward forfeit deposit assessment ⟨some material⟩ = _ at currentValue
  rw [currentValue] at rationalBound
  exact not_le_of_gt profitable (bound.trans (rationalBound.trans preservingBound))

/-- The original typed source has the same selected joint law at every
mandatory-publication SE; none can be implemented by a native SE here. -/
theorem equilibrium_terminal_law_ne_intended
    (positive : 0 < weight) (rewardPositive : 0 < reward) (forfeitPositive : 0 < forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobCollateral : 1 < deposit bob)
    (retryMarginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
      weight reward forfeit deposit)
    (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (profitable : reward / 2 < 3 * inclusionProbability weight * reward / 4 -
      (1 - inclusionProbability weight) * (forfeit + deposit alice))
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (source : setup.intendedModel.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) :
    nativeTerminalLaw weight nonnegative reward forfeit (fun actual => PMF.pure actual)
      deposit assessment.strategy ≠ intendedTerminalLaw reward source.strategy := by
  rw [intended_equilibrium_terminal_law sourceEquilibrium]
  exact equilibrium_terminal_law_ne_safe weight nonnegative reward forfeit deposit positive
    rewardPositive forfeitPositive aliceDepositNonnegative bobCollateral retryMarginPositive
      openingMarginPositive profitable assessment equilibrium

end Vegas.Examples.LateOpeningRuntimeSeObstruction
