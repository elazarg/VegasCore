/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood
import Vegas.Examples.LateOpeningRuntimeInitializedUnseenLikelihood
import Vegas.Examples.LateOpeningRuntimeInitializedSuccessReadout
import Vegas.Examples.LateOpeningRuntimeFirstResponseLimits
import Vegas.Examples.LateOpeningRuntimeConsistency
import Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation
import GameTheoryExtensions.Analysis.Protocol.AsymptoticLikelihood

/-! # Paired native label posteriors from one consistency sequence

The seen and unseen accepted-opening observations retain the same original
initialized type weights. Their remaining actual physical factors converge
to the first-opening probability and one minus half that probability. Exact
Bayes cancellation along one common native sequence therefore constrains the
two off-path posteriors without prescribing either posterior separately.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeLabelCross

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeBindingObservation
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeInitializedTypeLikelihood

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private def seenFactor (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) : ℝ :=
  ((originalLaw weight nonnegative profile bit label).toOuterMeasure
    (LateOpeningRuntimeSeenLikelihood.seenEvent bit label true)).toReal /
      (inclusionProbability weight / 2)

private def unseenFactor (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) : ℝ :=
  ((originalLaw weight nonnegative profile bit label).toOuterMeasure
    (LateOpeningRuntimeUnseenLikelihood.unseenEvent bit label)).toReal /
      inclusionProbability weight

private theorem inclusion_positive (positive : 0 < weight) : 0 < inclusionProbability weight := by
  unfold inclusionProbability MessageNetwork.inclusionMass
  positivity

private theorem seen_factor_tendsto (positive : 0 < weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (error : ℕ → ℝ) (errorNonnegative : ∀ n, 0 ≤ error n)
    (errorLimit : Tendsto error atTop (nhds 0))
    (retryBound : ∀ n
        (actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative),
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative (sequence n).strategy actual.1 ≤ error n)
    (bit : Bool) (label : Fin 3) :
    Tendsto (fun n => seenFactor weight nonnegative (sequence n).strategy bit label) atTop
      (nhds (genuineProbability weight nonnegative assessment.strategy bit label)) := by
  let mass := fun n => ((originalLaw weight nonnegative (sequence n).strategy
    bit label).toOuterMeasure (LateOpeningRuntimeSeenLikelihood.seenEvent bit label true)).toReal
  let leading := fun n => genuineProbability weight nonnegative (sequence n).strategy bit label *
    LateOpeningRuntimeSeenLikelihood.earlySilenceProbability weight nonnegative
      (sequence n).strategy bit label * inclusionProbability weight / 2
  have alpha := LateOpeningRuntimeFirstResponseLimits.genuineProbability_tendsto weight
    nonnegative (fun n => (sequence n).strategy) assessment.strategy
      (fun actual => converges.strategy alice actual) bit label
  have early := LateOpeningRuntimeInitializedSeenLikelihood.early_silence_tendsto
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral
      assessment rational sequence converges bit label
  have close (n : ℕ) : ‖mass n - leading n‖ ≤
      error n * genuineProbability weight nonnegative (sequence n).strategy bit label := by
    rw [Real.norm_eq_abs]
    exact LateOpeningRuntimeSeenLikelihood.original_seen_error weight nonnegative
      (sequence n).strategy bit label true (error n) (errorNonnegative n) (retryBound n)
  have negligible : Tendsto (fun n => mass n - leading n) atTop (nhds 0) :=
    squeeze_zero_norm close (by simpa only [zero_mul] using errorLimit.mul alpha)
  have leadingLimit : Tendsto leading atTop
      (nhds (genuineProbability weight nonnegative assessment.strategy bit label *
        inclusionProbability weight / 2)) := by
    simpa only [leading, mul_one] using
      ((alpha.mul early).mul tendsto_const_nhds).div_const (2 : ℝ)
  have massLimit : Tendsto mass atTop
      (nhds (genuineProbability weight nonnegative assessment.strategy bit label *
        inclusionProbability weight / 2)) := by
    have limit := negligible.add leadingLimit
    simpa only [sub_add_cancel, zero_add] using limit
  have limit := massLimit.div_const (inclusionProbability weight / 2)
  have nonzero := ne_of_gt (inclusion_positive weight positive)
  have cancel : (genuineProbability weight nonnegative assessment.strategy bit label *
      inclusionProbability weight / 2) / (inclusionProbability weight / 2) =
      genuineProbability weight nonnegative assessment.strategy bit label := by
    field_simp
  simpa only [seenFactor, mass, cancel] using limit

private theorem unseen_factor_tendsto (positive : 0 < weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (error : ℕ → ℝ) (errorNonnegative : ∀ n, 0 ≤ error n)
    (errorLimit : Tendsto error atTop (nhds 0))
    (retryBound : ∀ n
        (actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative),
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative (sequence n).strategy actual.1 ≤ error n)
    (openingBound : ∀ n
        (actual : LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative),
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative (sequence n).strategy actual ≤ error n)
    (firstBound : ∀ n
        (actual : LateOpeningRuntimeAliceFirstTremble.FirstOpeningSite weight nonnegative),
      LateOpeningRuntimeAliceFirstTremble.nongenuineProbability
        weight nonnegative (sequence n).strategy actual ≤ error n)
    (bit : Bool) (label : Fin 3) :
    Tendsto (fun n => unseenFactor weight nonnegative (sequence n).strategy bit label) atTop
      (nhds (1 - genuineProbability weight nonnegative assessment.strategy bit label / 2)) := by
  let mass := fun n => ((originalLaw weight nonnegative (sequence n).strategy
    bit label).toOuterMeasure (LateOpeningRuntimeUnseenLikelihood.unseenEvent bit label)).toReal
  let leading := fun n => (1 - genuineProbability weight nonnegative (sequence n).strategy
    bit label / 2) * LateOpeningRuntimeUnseenLikelihood.earlySilenceProbability weight nonnegative
      (sequence n).strategy bit label * inclusionProbability weight
  have alpha := LateOpeningRuntimeFirstResponseLimits.genuineProbability_tendsto weight
    nonnegative (fun n => (sequence n).strategy) assessment.strategy
      (fun actual => converges.strategy alice actual) bit label
  have early := LateOpeningRuntimeInitializedUnseenLikelihood.early_silence_tendsto
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral
      assessment rational sequence converges bit label
  have close (n : ℕ) : ‖mass n - leading n‖ ≤ 2 * error n := by
    rw [Real.norm_eq_abs]
    exact LateOpeningRuntimeUnseenLikelihood.original_unseen_error weight nonnegative
      (sequence n).strategy bit label (error n) (errorNonnegative n) (retryBound n)
        (openingBound n) (LateOpeningRuntimeUnseenLikelihood.first_nongenuine_probability_le
          weight nonnegative (sequence n).strategy bit label (error n) (firstBound n))
  have negligible : Tendsto (fun n => mass n - leading n) atTop (nhds 0) :=
    squeeze_zero_norm close (by simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).mul errorLimit)
  have leadingLimit : Tendsto leading atTop
      (nhds ((1 - genuineProbability weight nonnegative assessment.strategy bit label / 2) *
        inclusionProbability weight)) := by
    simpa only [leading, mul_one] using
      ((tendsto_const_nhds.sub (alpha.div_const (2 : ℝ))).mul early).mul tendsto_const_nhds
  have massLimit : Tendsto mass atTop
      (nhds ((1 - genuineProbability weight nonnegative assessment.strategy bit label / 2) *
        inclusionProbability weight)) := by
    have limit := negligible.add leadingLimit
    simpa only [sub_add_cancel, zero_add] using limit
  have limit := massLimit.div_const (inclusionProbability weight)
  have nonzero := ne_of_gt (inclusion_positive weight positive)
  have cancel : ((1 - genuineProbability weight nonnegative assessment.strategy bit label / 2) *
      inclusionProbability weight) / inclusionProbability weight =
      1 - genuineProbability weight nonnegative assessment.strategy bit label / 2 := by
    field_simp
  simpa only [unseenFactor, mass, cancel] using limit

variable (bit : Bool)
  (seenSite : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (seenRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob seenSite.1) (seenLabel : Fin 3)
  (seenCurrent : seenRepresentative.1.state =
    some ⟨14, some bob, answerDecision bit seenLabel 0 true⟩)
  (unseenSite : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (unseenRepresentative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob unseenSite.1) (unseenLabel : Fin 3)
  (unseenCurrent : unseenRepresentative.1.state =
    some ⟨14, some bob, answerDecision bit unseenLabel 0 false⟩)

include seenCurrent unseenCurrent in
/-- Two actual accepted-opening information classes obey this posterior
identity even when neither is reached in the limiting native strategy. -/
theorem label_belief_cross_identity (positive : 0 < weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobCollateral : 1 < deposit bob)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sender holder : Fin 3) :
    LateOpeningRuntimeBindingPosterior.readoutBelief weight nonnegative seenSite assessment
        LateOpeningRuntimeSuccessPosterior.initializedLabel (some holder) *
      LateOpeningRuntimeBindingPosterior.readoutBelief weight nonnegative unseenSite assessment
        LateOpeningRuntimeSuccessPosterior.initializedLabel (some sender) *
      (genuineProbability weight nonnegative assessment.strategy bit sender *
        (1 - genuineProbability weight nonnegative assessment.strategy bit holder / 2)) =
    LateOpeningRuntimeBindingPosterior.readoutBelief weight nonnegative seenSite assessment
        LateOpeningRuntimeSuccessPosterior.initializedLabel (some sender) *
      LateOpeningRuntimeBindingPosterior.readoutBelief weight nonnegative unseenSite assessment
        LateOpeningRuntimeSuccessPosterior.initializedLabel (some holder) *
      (genuineProbability weight nonnegative assessment.strategy bit holder *
        (1 - genuineProbability weight nonnegative assessment.strategy bit sender / 2)) := by
  obtain ⟨sequence, approximate, converges, error, errorNonnegative, errorLimit,
    firstBound, retryBound, openingBound, _⟩ :=
    LateOpeningRuntimeConsistency.equilibrium_consistency_witness weight nonnegative
      reward forfeit deposit positive rewardNonnegative forfeitNonnegative aliceDepositNonnegative
        marginPositive assessment equilibrium
  let seen : InformationModel.AsymptoticHistoryLikelihood
      (M := LateOpeningRuntimeNash.model weight nonnegative) bob Unit (Fin 3) sequence
        (fun n label => typeWeight weight nonnegative (sequence n).strategy bit label) := {
    site := fun _ => seenSite
    histories := fun _ label => readoutHistories weight nonnegative seenSite initializedInputs
      (some (setup.eventInputs (sourceInitial bit label)))
    observationFactor := fun _ _ => inclusionProbability weight / 2
    timingFactor := fun n _ label => seenFactor weight nonnegative (sequence n).strategy bit label
    limitTimingFactor := fun _ label => genuineProbability weight nonnegative assessment.strategy
      bit label
    reach_factored := by
      intro n _ label
      rw [initialized_type_reach_eq_prefix weight nonnegative seenSite seenRepresentative
        (answerDecision bit seenLabel 0 true) seenCurrent
          (LateOpeningRuntimeInitializedSeenLikelihood.seen_execution_ready bit seenLabel true),
        site_information weight nonnegative seenSite seenRepresentative
          (answerDecision bit seenLabel 0 true) seenCurrent]
      have factorization := LateOpeningRuntimeInitializedSeenLikelihood.initialized_seen_probability
        weight nonnegative seenSite seenRepresentative bit seenLabel true seenCurrent
          (sequence n).strategy label
      change ((bindingPrefix weight nonnegative (sequence n).strategy).toOuterMeasure
        (LateOpeningRuntimeInitializedSeenLikelihood.typedSeenEvent
          bit seenLabel label true)).toReal =
        typeWeight weight nonnegative (sequence n).strategy bit label *
          (inclusionProbability weight / 2) *
            seenFactor weight nonnegative (sequence n).strategy bit label
      rw [factorization]
      unfold seenFactor
      have nonzero := ne_of_gt (inclusion_positive weight positive)
      field_simp
    timing_tendsto := by
      intro _ label
      exact seen_factor_tendsto weight nonnegative positive reward forfeit deposit
        forfeitNonnegative bobCollateral assessment equilibrium.1 sequence converges
          error errorNonnegative errorLimit retryBound bit label
  }
  let unseen : InformationModel.AsymptoticHistoryLikelihood
      (M := LateOpeningRuntimeNash.model weight nonnegative) bob Unit (Fin 3) sequence
        (fun n label => typeWeight weight nonnegative (sequence n).strategy bit label) := {
    site := fun _ => unseenSite
    histories := fun _ label => readoutHistories weight nonnegative unseenSite initializedInputs
      (some (setup.eventInputs (sourceInitial bit label)))
    observationFactor := fun _ _ => inclusionProbability weight
    timingFactor := fun n _ label => unseenFactor weight nonnegative (sequence n).strategy bit label
    limitTimingFactor := fun _ label =>
      1 - genuineProbability weight nonnegative assessment.strategy bit label / 2
    reach_factored := by
      intro n _ label
      rw [initialized_type_reach_eq_prefix weight nonnegative unseenSite unseenRepresentative
        (answerDecision bit unseenLabel 0 false) unseenCurrent
          (LateOpeningRuntimeInitializedUnseenLikelihood.unseen_execution_ready bit unseenLabel),
        site_information weight nonnegative unseenSite unseenRepresentative
          (answerDecision bit unseenLabel 0 false) unseenCurrent]
      have factorization :=
        LateOpeningRuntimeInitializedUnseenLikelihood.initialized_unseen_probability
        weight nonnegative unseenSite unseenRepresentative bit unseenLabel unseenCurrent
          (sequence n).strategy label
      change ((bindingPrefix weight nonnegative (sequence n).strategy).toOuterMeasure
        (LateOpeningRuntimeInitializedUnseenLikelihood.typedUnseenEvent
          bit unseenLabel label)).toReal =
        typeWeight weight nonnegative (sequence n).strategy bit label *
          inclusionProbability weight *
            unseenFactor weight nonnegative (sequence n).strategy bit label
      rw [factorization]
      unfold unseenFactor
      have nonzero := ne_of_gt (inclusion_positive weight positive)
      field_simp
    timing_tendsto := by
      intro _ label
      exact unseen_factor_tendsto weight nonnegative positive reward forfeit deposit
        forfeitNonnegative bobCollateral assessment equilibrium.1 sequence converges
          error errorNonnegative errorLimit retryBound openingBound firstBound bit label
  }
  have factorLimit (first second : Fin 3) :
      Tendsto (fun n => seen.crossAt unseen n first second () ()) atTop
        (nhds (seen.crossLimit unseen first second () ())) :=
    (seen.timing_tendsto () first).mul (unseen.timing_tendsto () second)
  have leftLimit := ((InformationModel.finiteHistoryBelief_tendsto converges bob seenSite
      (seen.histories () holder)).mul
        (InformationModel.finiteHistoryBelief_tendsto converges bob unseenSite
          (unseen.histories () sender))).mul (factorLimit sender holder)
  have rightLimit := ((InformationModel.finiteHistoryBelief_tendsto converges bob seenSite
      (seen.histories () sender)).mul
        (InformationModel.finiteHistoryBelief_tendsto converges bob unseenSite
          (unseen.histories () holder))).mul (factorLimit holder sender)
  have same : (fun n => InformationModel.finiteHistoryBelief (sequence n) bob seenSite
      (seen.histories () holder) *
        InformationModel.finiteHistoryBelief (sequence n) bob unseenSite
          (unseen.histories () sender) * seen.crossAt unseen n sender holder () ()) =
    fun n => InformationModel.finiteHistoryBelief (sequence n) bob seenSite
      (seen.histories () sender) *
        InformationModel.finiteHistoryBelief (sequence n) bob unseenSite
          (unseen.histories () holder) * seen.crossAt unseen n holder sender () () := by
    funext n
    exact seen.bayes_cross_identity unseen
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))
        (fun n => (approximate n).1) (fun n => (approximate n).2) n sender holder () ()
  rw [same] at leftLimit
  have cross := tendsto_nhds_unique leftLimit rightLimit
  let seenDecision := LateOpeningRuntimeAliceSuccessfulContinuation.decisionHistory weight
    nonnegative positive bit seenLabel 0 true (Or.inl rfl)
  let unseenDecision := LateOpeningRuntimeAliceSuccessfulContinuation.decisionHistory weight
    nonnegative positive bit unseenLabel 0 false (Or.inl rfl)
  unfold LateOpeningRuntimeBindingPosterior.readoutBelief
  rw [LateOpeningRuntimeInitializedSuccessReadout.label_histories_eq_initialized_type
    weight nonnegative seenSite seenRepresentative seenDecision seenCurrent holder,
    LateOpeningRuntimeInitializedSuccessReadout.label_histories_eq_initialized_type
      weight nonnegative unseenSite unseenRepresentative unseenDecision unseenCurrent sender,
    LateOpeningRuntimeInitializedSuccessReadout.label_histories_eq_initialized_type
      weight nonnegative seenSite seenRepresentative seenDecision seenCurrent sender,
    LateOpeningRuntimeInitializedSuccessReadout.label_histories_eq_initialized_type
      weight nonnegative unseenSite unseenRepresentative unseenDecision unseenCurrent holder]
  exact cross

include seenCurrent unseenCurrent in
/-- A type that certainly sends first and a type that certainly defers cannot
both have positive posterior in the opposite accepted-opening observations. -/
theorem label_belief_product_zero (positive : 0 < weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (aliceDepositNonnegative : 0 ≤ deposit alice) (bobCollateral : 1 < deposit bob)
    (marginPositive : 0 < LateOpeningRuntimeAliceOpeningRationality.margin
      weight reward forfeit deposit)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sender holder : Fin 3)
    (sends : genuineProbability weight nonnegative assessment.strategy bit sender = 1)
    (holds : genuineProbability weight nonnegative assessment.strategy bit holder = 0) :
    LateOpeningRuntimeBindingPosterior.readoutBelief weight nonnegative seenSite assessment
        LateOpeningRuntimeSuccessPosterior.initializedLabel (some holder) *
      LateOpeningRuntimeBindingPosterior.readoutBelief weight nonnegative unseenSite assessment
        LateOpeningRuntimeSuccessPosterior.initializedLabel (some sender) = 0 := by
  have cross := label_belief_cross_identity weight nonnegative bit seenSite seenRepresentative
    seenLabel seenCurrent unseenSite unseenRepresentative unseenLabel unseenCurrent positive
      reward forfeit deposit rewardNonnegative forfeitNonnegative aliceDepositNonnegative
        bobCollateral marginPositive assessment equilibrium sender holder
  simpa only [sends, holds, zero_div, sub_zero, one_mul, zero_mul, mul_one, mul_zero] using cross

end Vegas.Examples.LateOpeningRuntimeLabelCross
