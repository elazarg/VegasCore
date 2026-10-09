/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceTimingValues
import Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality

/-! # Different native private labels choose opposite late sending times

Actual sender rationality fixes the aggregate probability of all genuine
first-opening aliases when its original continuation values differ strictly.
The exact accepted and omitted payoff branches supply those strict values
for two private labels sharing one immutable original bit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceTimingSorting

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeAliceTimingValues LateOpeningRuntimeFirstRetryComparison
  LateOpeningRuntimeFirstObservation
open LateOpeningRuntimeAliceFirstOptimality
  (sequentially_rational_genuineProbability_one_of_preference
    sequentially_rational_genuineProbability_zero_of_preference)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (positive : 0 < weight) (rewardPositive : 0 < reward)
  (forfeitPositive : 0 < forfeit) (aliceDepositNonnegative : 0 ≤ deposit alice)
  (bobCollateral : 1 < deposit bob)
  (retryMarginPositive : 0 < LateOpeningRuntimeAliceRationality.margin
    weight reward forfeit deposit)
  (openingMarginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
    weight reward forfeit deposit)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
  (rational : assessment.IsSequentiallyRational
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
      (fun actual => PMF.pure actual) deposit history.state who))

include positive rewardPositive forfeitPositive aliceDepositNonnegative bobCollateral
  retryMarginPositive rational in
private theorem genuine_value (bit : Bool) (label : Fin 3) (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice))
    (genuine : GenuineResponse weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label) response) :
    LateOpeningRuntimeAliceFirstOptimality.responseValue weight nonnegative bit label
      reward forfeit deposit assessment response =
    firstTimingValue weight nonnegative reward forfeit deposit
      (players weight nonnegative assessment.strategy) bit label := by
  obtain ⟨submission, transmitted, opening⟩ := genuine
  have same : response = ⟨some submission⟩ := by
    cases response
    cases transmitted
    rfl
  rw [same] at available ⊢
  exact first_genuine_response_value weight nonnegative reward forfeit deposit positive
    rewardPositive.le forfeitPositive aliceDepositNonnegative assessment rational
      retryMarginPositive
      bobCollateral bit label submission available opening

include positive rewardPositive forfeitPositive aliceDepositNonnegative bobCollateral
  openingMarginPositive rational in
private theorem silent_value (bit : Bool) (label : Fin 3) :
    LateOpeningRuntimeAliceFirstOptimality.responseValue weight nonnegative bit label
      reward forfeit deposit assessment ⟨none⟩ =
    secondTimingValue weight nonnegative reward forfeit deposit
      (players weight nonnegative assessment.strategy) bit label :=
  first_silence_response_value weight nonnegative reward forfeit deposit positive rewardPositive.le
    forfeitPositive aliceDepositNonnegative assessment rational openingMarginPositive bobCollateral
      bit label

private theorem first_representative (bit : Bool) (label : Fin 3) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1),
      history.1.state = some ⟨22, some alice, firstLateDecision bit label⟩ := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨22, some alice, firstLateDecision bit label⟩,
      (LateOpeningRuntimeAliceFirstWitness.firstLateDecision_trace
        weight nonnegative bit label).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (22 = 0 ∧ some alice = none); simp) rfl
  exact ⟨site, ⟨history, information.symm⟩, rfl⟩

include positive rewardPositive forfeitPositive aliceDepositNonnegative bobCollateral
  retryMarginPositive openingMarginPositive rational in
/-- Every globally rational original native profile has a bit class with one
private label sending at the first late opportunity and another waiting,
where emission probability includes all legal genuine private aliases. -/
theorem opposite_emission_probabilities :
    ∃ bit sender holder,
      genuineProbability weight nonnegative assessment.strategy bit sender = 1 ∧
      genuineProbability weight nonnegative assessment.strategy bit holder = 0 := by
  have bobPositive : 0 < deposit bob := lt_trans zero_lt_one bobCollateral
  obtain ⟨bit, sender, holder, sendsBetter, holdsBetter⟩ := opposite_preferences weight nonnegative
    reward forfeit deposit positive rewardPositive.le forfeitPositive aliceDepositNonnegative
      bobPositive assessment rational (players weight nonnegative assessment.strategy) rfl
        rewardPositive
  obtain ⟨senderSite, senderHistory, senderCurrent⟩ := first_representative
    weight nonnegative bit sender
  obtain ⟨holderSite, holderHistory, holderCurrent⟩ := first_representative
    weight nonnegative bit holder
  refine ⟨bit, sender, holder, ?_, ?_⟩
  · exact sequentially_rational_genuineProbability_one_of_preference
      weight nonnegative senderSite
        senderHistory bit sender senderCurrent reward forfeit deposit positive rewardPositive.le
          forfeitPositive.le aliceDepositNonnegative openingMarginPositive assessment rational
          _ _ (genuine_value weight nonnegative reward forfeit deposit positive rewardPositive
            forfeitPositive aliceDepositNonnegative bobCollateral retryMarginPositive assessment
              rational bit sender)
          (silent_value weight nonnegative reward forfeit deposit positive rewardPositive
            forfeitPositive aliceDepositNonnegative bobCollateral openingMarginPositive assessment
              rational bit sender) sendsBetter
  · exact sequentially_rational_genuineProbability_zero_of_preference
      weight nonnegative holderSite
        holderHistory bit holder holderCurrent reward forfeit deposit assessment rational _ _
          (genuine_value weight nonnegative reward forfeit deposit positive rewardPositive
            forfeitPositive aliceDepositNonnegative bobCollateral retryMarginPositive assessment
              rational bit holder)
          (silent_value weight nonnegative reward forfeit deposit positive rewardPositive
            forfeitPositive aliceDepositNonnegative bobCollateral openingMarginPositive assessment
              rational bit holder) holdsBetter

end Vegas.Examples.LateOpeningRuntimeAliceTimingSorting
