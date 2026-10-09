/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstTremble
import Vegas.Examples.LateOpeningRuntimeAliceTremble
import Vegas.Examples.LateOpeningRuntimeAliceOpeningTremble
import Vegas.Examples.LateOpeningRuntimeBindingPosterior

/-! # One native consistency witness for all opening errors and beliefs

The same fully mixed Bayes sequence witnesses every receiver readout limit
and uniformly bounds all three sender departures: nongenuine first packets,
retries after a genuine packet, and failure to open after earlier silence.
The error tends to zero without a lower bound on any earlier reach probability.
This theorem supplies proof data about the existing native game, not a new
runtime interface or independently prescribed off-path posterior.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeConsistency

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeBindingPosterior

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem equilibrium_consistency_witness
    (reward forfeit : ℝ) (deposit : Player → ℝ) (positive : 0 < weight)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who)) :
    ∃ sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed ∧
        InformationModel.BehavioralAssessment.IsBayesConsistent
          (LateOpeningRuntimeNash.model weight nonnegative) (sequence n)
          (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative))) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment ∧
      ∃ error : ℕ → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      (∀ n (site : LateOpeningRuntimeAliceFirstTremble.FirstOpeningSite weight nonnegative),
        LateOpeningRuntimeAliceFirstTremble.nongenuineProbability weight nonnegative
          (sequence n).strategy site ≤ error n) ∧
      (∀ n (site : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative),
        LateOpeningRuntimeAliceTremble.emissionProbability weight nonnegative
          (sequence n).strategy site.1 ≤ error n) ∧
      (∀ n (site : LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative),
        LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability weight nonnegative
          (sequence n).strategy site ≤ error n) ∧
      ∀ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
        (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
          bob site.1) (execution : app.Execution),
        representative.1.state = some ⟨14, some bob, execution⟩ →
        execution.application.config.cut.Ready bobBindEvent →
        ∀ (readout : app.ProtocolState → Option nativeGraph.Inputs)
          (value : Option nativeGraph.Inputs),
          Tendsto (fun n => conditionalPrefixProbability weight nonnegative site
            (sequence n).strategy readout value) atTop
              (nhds (readoutBelief weight nonnegative site assessment readout value)) := by
  obtain ⟨sequence, approximate, converges⟩ := equilibrium.2
  have retryMargin : 0 < LateOpeningRuntimeAliceRationality.margin
      weight reward forfeit deposit := by
    unfold LateOpeningRuntimeAliceOpeningRationality.margin at marginPositive
    unfold LateOpeningRuntimeAliceRationality.margin
    linarith [min_le_right forfeit (deposit alice)]
  obtain ⟨firstError, firstNonnegative, firstLimit, firstBound⟩ :=
    LateOpeningRuntimeAliceFirstTremble.sequentially_rational_uniform_nongenuine_bound
      weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitNonnegative
        depositNonnegative marginPositive assessment equilibrium.1 sequence converges
  obtain ⟨retryError, retryNonnegative, retryLimit, retryBound⟩ :=
    LateOpeningRuntimeAliceTremble.sequentially_rational_uniform_retry_bound
      weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitNonnegative
        depositNonnegative retryMargin assessment equilibrium.1 sequence converges
  obtain ⟨openingError, openingNonnegative, openingLimit, openingBound⟩ :=
    LateOpeningRuntimeAliceOpeningTremble.sequentially_rational_uniform_nongenuine_bound
      weight nonnegative reward forfeit deposit positive rewardNonnegative forfeitNonnegative
        depositNonnegative marginPositive assessment equilibrium.1 sequence converges
  let error : ℕ → ℝ := fun n => firstError n + retryError n + openingError n
  refine ⟨sequence, approximate, converges, error, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact add_nonneg (add_nonneg (firstNonnegative n) (retryNonnegative n)) (openingNonnegative n)
  · simpa only [add_zero] using (firstLimit.add retryLimit).add openingLimit
  · intro n site
    have bound := firstBound n site
    dsimp only [error]
    linarith [retryNonnegative n, openingNonnegative n]
  · intro n site
    have bound := retryBound n site
    dsimp only [error]
    linarith [firstNonnegative n, openingNonnegative n]
  · intro n site
    have bound := openingBound n site
    dsimp only [error]
    linarith [firstNonnegative n, retryNonnegative n]
  · intro site representative execution current ready readout value
    exact conditional_probability_tendsto weight nonnegative site representative execution current
      ready sequence assessment (fun n => (approximate n).1) (fun n => (approximate n).2)
        converges readout value

end Vegas.Examples.LateOpeningRuntimeConsistency
