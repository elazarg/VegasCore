/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PowerReach
import GameTheoryExtensions.Math.Probability.PowerPosterior

/-! # Soundness of shared behavioral power certificates

The actual local positive power profiles form one common fully mixed sequence.
Their actual evaluator weights have the computed leading coefficients and
orders. Finite-fiber normalization proves consistency of the explicit limiting
assessment, and coefficient constraints identify any exactly prescribed belief.
No affine-ray completeness or assumed Bayes convergence is used.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  [∀ who info, Finite (M.Choice who info)]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]

/-- The prescribed strategy with its explicit leading-coefficient beliefs.
A minimal-order reference is supplied separately as a certificate witness. -/
def powerAssessment (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat)
    (reference : ∀ who (site : M.InformationSite who), M.InformationHistory who site.1) :
    M.BehavioralAssessment where
  strategy := base
  belief who site := leadingPowerLaw
    (fun history : M.InformationHistory who site.1 =>
      M.powerHistoryCoefficient coefficient history.1.trace)
    (fun history => M.powerHistoryCoefficient_pos coefficient positive history.1.trace)
    (fun history => M.powerHistoryOrder order history.1.trace) (reference who site)

/-- Positive coefficients and local constant terms construct an actual common
fully mixed Bayes sequence converging to the explicit power assessment. -/
theorem powerAssessment_consistent (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat)
    (constantTerm : ∀ who info choice,
      (if order who info choice = 0 then coefficient who info choice else 0) =
        (base who info choice).toReal)
    (reference : ∀ who (site : M.InformationSite who), M.InformationHistory who site.1)
    (minimal : ∀ who (site : M.InformationSite who)
      (history : M.InformationHistory who site.1),
      M.powerHistoryOrder order (reference who site).1.trace ≤
        M.powerHistoryOrder order history.1.trace)
    (antichain : M.DecisionInformationAntichain)
    {parameter : Nat → ℝ} (parameterPositive : ∀ n, 0 < parameter n)
    (vanishes : Tendsto parameter atTop (nhds 0)) :
    (M.powerAssessment base coefficient positive order reference).IsSequentiallyConsistent
      antichain := by
  let : ∀ who info, Fintype (M.Choice who info) := fun who info => Fintype.ofFinite _
  let profile := fun n => M.powerProfile base coefficient positive order
    (parameter n) (parameterPositive n)
  have mixed (n : Nat) := M.powerProfile_full base coefficient positive order
    (parameter n) (parameterPositive n)
  let sequence := fun n => M.bayesAssessment (profile n) (mixed n) antichain
  refine ⟨sequence, fun n => ⟨mixed n,
    M.bayesAssessment_isBayesConsistent (profile n) (mixed n) antichain⟩, ?_⟩
  constructor
  · intro who site
    exact normalizedPower_converges (base who site.1) (coefficient who site.1)
      (positive who site.1) (order who site.1) (constantTerm who site.1)
      parameterPositive vanishes
  · intro who site
    apply pmfConvergesPointwise_iff_toReal.mpr
    intro history
    have mass (n : Nat) :
        (M.informationMass (profile n) who site).toReal =
          ∑ member : M.InformationHistory who site.1,
            (M.historyReachWeight (profile n) member.1).toReal := by
      unfold informationMass
      exact (ENNReal.tsum_toReal_eq
        (f := fun member : M.InformationHistory who site.1 =>
          M.historyReachWeight (profile n) member.1)
        (fun _ => PMF.apply_ne_top _ _)).trans (tsum_fintype _)
    have limit := finite_power_ratio_tendsto
      (fun n (member : M.InformationHistory who site.1) =>
        (M.historyReachWeight (profile n) member.1).toReal)
      (fun member => M.powerHistoryCoefficient coefficient member.1.trace)
      (fun member => M.powerHistoryCoefficient_pos coefficient positive member.1.trace)
      (fun member => M.powerHistoryOrder order member.1.trace) (reference who site)
      (minimal who site) parameterPositive vanishes
      (fun member => M.powerProfile_history_scaled_tendsto base coefficient positive order
        constantTerm parameterPositive vanishes member.1.trace) history
    apply limit.congr'
    filter_upwards [] with n
    have bayes := M.bayesAssessment_isBayesConsistent (profile n) (mixed n) antichain
      who site (M.informationMass_pos_of_fullSupport (profile n) (mixed n) who site) history
    change (M.historyReachWeight (profile n) history.1).toReal /
      ∑ member : M.InformationHistory who site.1,
        (M.historyReachWeight (profile n) member.1).toReal =
          ((sequence n).belief who site history).toReal
    rw [bayes, ENNReal.toReal_div]
    change _ = (M.historyReachWeight (profile n) history.1).toReal /
      (M.informationMass (profile n) who site).toReal
    rw [mass]

omit [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)] in
/-- A supplied assessment is the exact consistent limit when its full beliefs
satisfy the leading coefficient constraints, including all zero-belief histories. -/
theorem powerCertificate_consistent
    [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]
    (assessment : M.BehavioralAssessment)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat)
    (constantTerm : ∀ who info choice,
      (if order who info choice = 0 then coefficient who info choice else 0) =
        (assessment.strategy who info choice).toReal)
    (reference : ∀ who (site : M.InformationSite who), M.InformationHistory who site.1)
    (minimal : ∀ who (site : M.InformationSite who)
      (history : M.InformationHistory who site.1),
      M.powerHistoryOrder order (reference who site).1.trace ≤
        M.powerHistoryOrder order history.1.trace)
    (support : ∀ who (site : M.InformationSite who)
      (history : M.InformationHistory who site.1),
      M.powerHistoryOrder order history.1.trace =
          M.powerHistoryOrder order (reference who site).1.trace ↔
        (assessment.belief who site history).toReal ≠ 0)
    (ratios : ∀ who (site : M.InformationSite who)
      (history : M.InformationHistory who site.1),
      (assessment.belief who site history).toReal ≠ 0 →
      M.powerHistoryCoefficient coefficient history.1.trace /
          M.powerHistoryCoefficient coefficient (reference who site).1.trace =
        (assessment.belief who site history).toReal /
          (assessment.belief who site (reference who site)).toReal)
    (antichain : M.DecisionInformationAntichain)
    {parameter : Nat → ℝ} (parameterPositive : ∀ n, 0 < parameter n)
    (vanishes : Tendsto parameter atTop (nhds 0)) :
    assessment.IsSequentiallyConsistent antichain := by
  let : ∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1) :=
    fun who site => Fintype.ofFinite _
  have same : M.powerAssessment assessment.strategy coefficient positive order reference =
      assessment := by
    cases assessment with
    | mk strategy belief =>
      apply congrArg (BehavioralAssessment.mk strategy)
      funext who site
      exact leadingPowerLaw_eq_of_ratios (belief who site)
        (fun member : M.InformationHistory who site.1 =>
          M.powerHistoryCoefficient coefficient member.1.trace)
        (fun member => M.powerHistoryCoefficient_pos coefficient positive member.1.trace)
        (fun member => M.powerHistoryOrder order member.1.trace) (reference who site)
        (support who site) (ratios who site)
  rw [← same]
  exact M.powerAssessment_consistent assessment.strategy coefficient positive order constantTerm
    reference minimal antichain parameterPositive vanishes

end GameTheory.Protocol.InformationModel
