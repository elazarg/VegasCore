/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryHonestDomination

/-! # Honest Bayes limits for the actual normalized pooled source assessments

The original setup and Nature laws remain in the derived execution domination.
Only a quantitative rate condition on the fixed honest consistency sequence
enters; there is no source-belief or target-likelihood identification premise.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

omit [Fintype Player] [Fintype setup.proposalRecoveryProtocol.History] in
private theorem original_info_length (who : Player)
    (history : setup.proposalRecoveryProtocol.History) :
    (setup.proposalRecoveryModel.infoOf who history.trace).1.2.length = history.trace.length := by
  exact setup.proposalRecoveryModel_word_length who history.trace


open Classical in
/-- The actual source Bayes beliefs at every honest site converge to the
original honest belief, for arbitrary pooled weights. The only rate condition
uses the FIXED original honest sequence's information mass, before completion. -/
theorem proposalRecovery_normalized_honest_beliefs_converge
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    (target : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (source n).IsFullyMixed)
    (sourceBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.intendedModel (source n) setup.intended_decision_antichain)
    (targetMixed : ∀ n, (target n).IsFullyMixed)
    (targetBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel (target n) setup.proposalRecoveryModel_decisionAntichain)
    (omission bad delivery floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badSmall : ∀ n, bad n < 1)
    (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliverySmall : ∀ n, delivery n < 1)
    (floorNonnegative : ∀ n, 0 ≤ floor n) (floorSmall : ∀ n, floor n < 1)
    (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      (target n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badNonnegative n) (badSmall n).le
          (delivery n) (deliveryNonnegative n) (deliverySmall n).le
          (setup.proposalRecoveryPooledDomainLaw finite
            (floor n) (floorNonnegative n) (floorSmall n).le
            (setup.proposalRecoveryHonestPoolPins wellFormed (source n).strategy)
            (weights n)) who (setup.proposalRecoveryModel.infoOf who history.trace))
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (negligible :
      let depth := ((setup.proposalRecoveryRestriction wellFormed).information who
        site.1).1.2.length
      let fraction := fun n =>
        ((1 - omission n) * (1 - bad n) * (1 - floor n) * (1 - delivery n)) ^
        (Fintype.card Player * depth)
      Tendsto (fun n => (1 - fraction n) /
        (fraction n * (setup.intendedModel.informationMass (source n).strategy who site).toReal))
          atTop (nhds 0))
    (limit : PMF (setup.intendedModel.InformationHistory who site.1))
    (converges : PMFConvergesPointwise (fun n => (source n).belief who site) limit) :
    PMFConvergesPointwise
      (fun n => (target n).belief who ((setup.proposalRecoveryRestriction wellFormed).site who
        site))
      (limit.map ((setup.proposalRecoveryRestriction wellFormed).informationHistory who site)) := by
  classical
  let restriction := setup.proposalRecoveryRestriction wellFormed
  let depth := (restriction.information who site.1).1.2.length
  let fraction := fun n =>
    ((1 - omission n) * (1 - bad n) * (1 - floor n) * (1 - delivery n)) ^
    (Fintype.card Player * depth)
  have clock : InformationModel.InformationSite.CommonDepth setup.proposalRecoveryModel
      (restriction.site who site) depth := by
    intro history
    rw [← setup.original_info_length who history.1, history.property]
    rfl
  have positive (n : ℕ) : 0 < fraction n := pow_pos
    (mul_pos
      (mul_pos (mul_pos (sub_pos.mpr (omissionSmall n)) (sub_pos.mpr (badSmall n)))
        (sub_pos.mpr (floorSmall n))) (sub_pos.mpr (deliverySmall n))) _
  have bounded (n : ℕ) : fraction n ≤ 1 := by
    apply pow_le_one₀
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr (omissionSmall n).le)
          (sub_nonneg.mpr (badSmall n).le)) (sub_nonneg.mpr (floorSmall n).le))
          (sub_nonneg.mpr (deliverySmall n).le)
    · have first : (1 - omission n) * (1 - bad n) ≤ 1 :=
        (mul_le_of_le_one_left (sub_nonneg.mpr (badSmall n).le)
          (sub_le_self 1 (omissionPositive n).le)).trans (sub_le_self 1 (badNonnegative n))
      have second : (1 - omission n) * (1 - bad n) * (1 - floor n) ≤ 1 :=
        (mul_le_of_le_one_left (sub_nonneg.mpr (floorSmall n).le) first).trans
          (sub_le_self 1 (floorNonnegative n))
      exact (mul_le_of_le_one_left (sub_nonneg.mpr (deliverySmall n).le) second).trans
        (sub_le_self 1 (deliveryNonnegative n))
  apply restriction.retained_beliefs_converge source target setup.intended_decision_antichain
    setup.proposalRecoveryModel_decisionAntichain sourceMixed targetMixed sourceBayes targetBayes
    who site depth clock fraction positive bounded _ negligible limit converges
  intro n history
  have sameRun := setup.proposalRecoveryModel.runBehavioralFrom_congr
    depth setup.proposalRecoveryProtocol.initHistory
    (fun later _ running owner => prescribed n owner later running)
  change setup.proposalRecoveryModel.runBehavioral (target n).strategy depth = _ at sameRun
  rw [sameRun]
  exact setup.proposalRecovery_normalized_honest_run_lower finite wellFormed (source n).strategy
    (omission n) (omissionPositive n).le (omissionSmall n).le
    (bad n) (badNonnegative n) (badSmall n).le
          (delivery n) (deliveryNonnegative n) (deliverySmall n).le
    (floor n) (floorNonnegative n) (floorSmall n).le (weights n)
    (omissionPositive n) depth history


omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L]
  [Fintype setup.proposalRecoveryProtocol.History] in
private theorem combined_loss_tendsto
    (reach mass omission bad delivery floor : ℕ → ℝ) (positive : ∀ n, 0 < reach n)
    (massBound : ∀ n, reach n ≤ mass n)
    (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionSmall : ∀ n, omission n ≤ 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badSmall : ∀ n, bad n ≤ 1)
    (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliverySmall : ∀ n, delivery n ≤ 1)
    (floorNonnegative : ∀ n, 0 ≤ floor n) (floorSmall : ∀ n, floor n ≤ 1)
    (omissionRate : ∀ n, omission n ≤ relativeTremble reach n)
    (badRate : ∀ n, bad n ≤ relativeTremble reach n)
    (deliveryRate : ∀ n, delivery n ≤ relativeTremble reach n)
    (floorRate : ∀ n, floor n ≤ relativeTremble reach n) (steps : Nat) :
    Tendsto (fun n =>
      (1 - ((1 - omission n) * (1 - bad n) * (1 - floor n) * (1 - delivery n)) ^ steps) /
        (((1 - omission n) * (1 - bad n) * (1 - floor n) * (1 - delivery n)) ^ steps * mass n))
      atTop (nhds 0) := by
  let baseline := fun n => (1 - relativeTremble reach n) ^ (4 * steps)
  let actual := fun n => ((1 - omission n) * (1 - bad n) * (1 - floor n) * (1 - delivery n)) ^ steps
  have baselinePositive (n : ℕ) : 0 < baseline n :=
    pow_pos (sub_pos.mpr (relativeTremble_lt_one reach n)) _
  have below (n : ℕ) : baseline n ≤ actual n := by
    have pair := mul_le_mul (sub_le_sub_left (omissionRate n) 1)
      (sub_le_sub_left (badRate n) 1)
      (sub_pos.mpr (relativeTremble_lt_one reach n)).le (sub_nonneg.mpr (omissionSmall n))
    have triple := mul_le_mul pair (sub_le_sub_left (floorRate n) 1)
      (sub_pos.mpr (relativeTremble_lt_one reach n)).le
      (mul_nonneg (sub_nonneg.mpr (omissionSmall n)) (sub_nonneg.mpr (badSmall n)))
    have fourth := mul_le_mul triple (sub_le_sub_left (deliveryRate n) 1)
      (sub_pos.mpr (relativeTremble_lt_one reach n)).le
      (mul_nonneg
        (mul_nonneg (sub_nonneg.mpr (omissionSmall n)) (sub_nonneg.mpr (badSmall n)))
        (sub_nonneg.mpr (floorSmall n)))
    have powered := pow_le_pow_left₀
      (pow_nonneg (sub_pos.mpr (relativeTremble_lt_one reach n)).le 4)
      (show (1 - relativeTremble reach n) ^ 4 ≤
        (1 - omission n) * (1 - bad n) * (1 - floor n) * (1 - delivery n) by
          nlinarith only [fourth]) steps
    simpa only [← pow_mul] using powered
  have bounded (n : ℕ) : actual n ≤ 1 := by
    apply pow_le_one₀
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr (omissionSmall n))
          (sub_nonneg.mpr (badSmall n))) (sub_nonneg.mpr (floorSmall n)))
          (sub_nonneg.mpr (deliverySmall n))
    · have first : (1 - omission n) * (1 - bad n) ≤ 1 :=
        (mul_le_of_le_one_left (sub_nonneg.mpr (badSmall n))
          (sub_le_self 1 (omissionNonnegative n))).trans (sub_le_self 1 (badNonnegative n))
      have second : (1 - omission n) * (1 - bad n) * (1 - floor n) ≤ 1 :=
        (mul_le_of_le_one_left (sub_nonneg.mpr (floorSmall n)) first).trans
          (sub_le_self 1 (floorNonnegative n))
      exact (mul_le_of_le_one_left (sub_nonneg.mpr (deliverySmall n)) second).trans
        (sub_le_self 1 (deliveryNonnegative n))
  apply squeeze_zero
  · intro n
    exact div_nonneg (sub_nonneg.mpr (bounded n))
      (mul_nonneg ((baselinePositive n).le.trans (below n)) ((positive n).le.trans (massBound n)))
  · intro n
    have denominator := mul_le_mul (below n) (massBound n) (positive n).le
      ((baselinePositive n).le.trans (below n))
    exact (div_le_div_of_nonneg_left (sub_nonneg.mpr (bounded n))
      (mul_pos (baselinePositive n) (positive n)) denominator).trans
        (div_le_div_of_nonneg_right (sub_le_sub_left (below n) 1)
          (mul_pos (baselinePositive n) (positive n)).le)
  · exact relativeTremble_power_ratio_tendsto reach positive (4 * steps)

open Classical in
/-- Fixed rates chosen below the ORIGINAL honest sequence's positive reach
bound preserve honest beliefs for every normalized pooled completion. The
quantitative Bayes loss is discharged here, before any optimized source reach
or completion weights are known. -/
theorem proposalRecovery_normalized_honest_beliefs_of_rates
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    (target : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (source n).IsFullyMixed)
    (sourceBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.intendedModel (source n) setup.intended_decision_antichain)
    (targetMixed : ∀ n, (target n).IsFullyMixed)
    (targetBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel (target n) setup.proposalRecoveryModel_decisionAntichain)
    (omission bad delivery floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badSmall : ∀ n, bad n < 1)
    (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliverySmall : ∀ n, delivery n < 1)
    (floorNonnegative : ∀ n, 0 ≤ floor n) (floorSmall : ∀ n, floor n < 1)
    (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      (target n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badNonnegative n) (badSmall n).le
          (delivery n) (deliveryNonnegative n) (deliverySmall n).le
          (setup.proposalRecoveryPooledDomainLaw finite
            (floor n) (floorNonnegative n) (floorSmall n).le
            (setup.proposalRecoveryHonestPoolPins wellFormed (source n).strategy)
            (weights n)) who (setup.proposalRecoveryModel.infoOf who history.trace))
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (reach : ℕ → ℝ) (reachPositive : ∀ n, 0 < reach n)
    (reachBound : ∀ n, reach n ≤
      (setup.intendedModel.informationMass (source n).strategy who site).toReal)
    (omissionRate : ∀ n, omission n ≤ relativeTremble reach n)
    (badRate : ∀ n, bad n ≤ relativeTremble reach n)
    (deliveryRate : ∀ n, delivery n ≤ relativeTremble reach n)
    (floorRate : ∀ n, floor n ≤ relativeTremble reach n)
    (limit : PMF (setup.intendedModel.InformationHistory who site.1))
    (converges : PMFConvergesPointwise (fun n => (source n).belief who site) limit) :
    PMFConvergesPointwise
      (fun n => (target n).belief who
        ((setup.proposalRecoveryRestriction wellFormed).site who site))
      (limit.map ((setup.proposalRecoveryRestriction wellFormed).informationHistory who site)) := by
  apply setup.proposalRecovery_normalized_honest_beliefs_converge finite wellFormed source target
    sourceMixed sourceBayes targetMixed targetBayes omission bad delivery floor
    omissionPositive omissionSmall badNonnegative badSmall deliveryNonnegative deliverySmall
    floorNonnegative floorSmall
    weights prescribed who site _ limit converges
  exact combined_loss_tendsto reach _ omission bad delivery floor reachPositive reachBound
    (fun n => (omissionPositive n).le) (fun n => (omissionSmall n).le)
    badNonnegative (fun n => (badSmall n).le)
    deliveryNonnegative (fun n => (deliverySmall n).le)
    floorNonnegative (fun n => (floorSmall n).le)
    omissionRate badRate deliveryRate floorRate _

end Vegas.SourceProgram.Setup
