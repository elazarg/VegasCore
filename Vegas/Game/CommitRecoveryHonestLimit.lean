/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHonestBeliefs
import Vegas.Game.CommitRecoveryDeviationPayoff
import GameTheory.Analysis.Protocol.RestrictionIncentives

/-! # Honest rationality of the same normalized source limit

The actual honest pins preserve strategies and beliefs through the original
consistency sequences. All legal honest deviations retain their original
continuation value; every additional source action pays the exclusion floor.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The same actual normalized source limit extends the given honest limit,
although the optimized weights and residual perturbation profiles vary. -/
theorem commitRecovery_normalized_honest_limit_extends
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    (target : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (sourceLimit : setup.intendedModel.BehavioralAssessment)
    (targetLimit : setup.commitRecoveryModel.BehavioralAssessment)
    (sourceConverges : InformationModel.BehavioralAssessmentConvergesPointwise source sourceLimit)
    (targetConverges : InformationModel.BehavioralAssessmentConvergesPointwise target targetLimit)
    (omission bad floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badSmall : ∀ n, bad n < 1)
    (floorNonnegative : ∀ n, 0 ≤ floor n) (floorSmall : ∀ n, floor n < 1)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (target n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badNonnegative n) (badSmall n).le
          (setup.commitRecoveryPooledDomainLaw finite
            (floor n) (floorNonnegative n) (floorSmall n).le
            (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
            (weights n)) who (setup.commitRecoveryModel.infoOf who history.trace))
    (omissionVanishes : Tendsto omission atTop (nhds 0))
    (badVanishes : Tendsto bad atTop (nhds 0))
    (floorVanishes : Tendsto floor atTop (nhds 0)) :
    (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
      sourceLimit.strategy targetLimit.strategy := by
  classical
  let restriction := setup.commitRecoveryRestriction wellFormed
  let fraction := fun n => (1 - omission n) * (1 - bad n) * (1 - floor n)
  have unit : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have fractionLimit : Tendsto fraction atTop (nhds 1) := by
    simpa only [sub_zero, mul_one] using
      ((unit.sub omissionVanishes).mul (unit.sub badVanishes)).mul (unit.sub floorVanishes)
  intro who site
  obtain ⟨history, running, _⟩ := site.property
  have observed := history.property
  let honest := fun n => ((source n).strategy who site.1).map
    (fun choice => CommitRecoveryMove.lift choice.val)
  let actual := fun n => ((target n).strategy who (restriction.information who site.1)).map
    Subtype.val
  have actualLower (n : ℕ) (action : Option (CommitRecoveryMove Player L)) :
      fraction n * ((honest n) action).toReal ≤ ((actual n) action).toReal := by
    have lower := setup.commitRecovery_normalized_honest_raw_lower finite wellFormed
      (source n).strategy (omission n) (omissionPositive n).le (omissionSmall n).le
      (bad n) (badNonnegative n) (badSmall n).le
      (floor n) (floorNonnegative n) (floorSmall n).le (weights n)
      who history.1 running action
    have lifted := restriction.observed who history.1
    have plays := prescribed n who (restriction.history history.1)
      (fun stopped => running ((restriction.terminal history.1).mp stopped))
    rw [lifted, observed] at plays
    rw [observed] at lower
    change fraction n * ((honest n) action).toReal ≤ _ at lower
    dsimp only [actual]
    rw [plays]
    simpa only [restriction, commitRecoveryRestriction] using lower
  apply pmf_map_injective Subtype.val_injective
  rw [PMF.map_comp]
  apply pmf_ext_toReal
  intro action
  have honestLimit := ((sourceConverges.strategy who site).map
    (fun choice => CommitRecoveryMove.lift choice.val)).toReal action
  have lowerLimit := fractionLimit.mul honestLimit
  simp only [one_mul] at lowerLimit
  have upperLimit := lowerLimit.add (unit.sub fractionLimit)
  simp only [sub_self, add_zero] at upperLimit
  have actualLimit := ((targetConverges.strategy who (restriction.site who site)).map
    Subtype.val).toReal action
  have bounded : ∀ n, ((actual n) action).toReal ≤
      fraction n * ((honest n) action).toReal + (1 - fraction n) := by
    intro n
    have excess := probOf_domination_excess (honest n) (actual n) (fraction n)
      (actualLower n) {action}
    simp only [PMF.toOuterMeasure_apply_singleton] at excess
    exact (sub_le_iff_le_add.mp excess).trans_eq (add_comm _ _)
  have converges := tendsto_of_tendsto_of_tendsto_of_le_of_le lowerLimit upperLimit
    (fun n => actualLower n action) bounded
  exact tendsto_nhds_unique actualLimit converges

open Classical in
/-- Honest beliefs, every honest-site local incentive, and the original
initialized joint law are preserved by the SAME normalized pooled limit.
Rates depend only on the given honest sequence, never optimized source reach. -/
theorem commitRecovery_normalized_honest_limit
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    (target : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (source n).IsFullyMixed)
    (sourceBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.intendedModel (source n) setup.intended_decision_antichain)
    (targetMixed : ∀ n, (target n).IsFullyMixed)
    (targetBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (target n) setup.commitRecoveryModel_decisionAntichain)
    (sourceLimit : setup.intendedModel.BehavioralAssessment)
    (targetLimit : setup.commitRecoveryModel.BehavioralAssessment)
    (sourceConverges : InformationModel.BehavioralAssessmentConvergesPointwise source sourceLimit)
    (targetConverges : InformationModel.BehavioralAssessmentConvergesPointwise target targetLimit)
    (omission bad floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badNonnegative : ∀ n, 0 ≤ bad n) (badSmall : ∀ n, bad n < 1)
    (floorNonnegative : ∀ n, 0 ≤ floor n) (floorSmall : ∀ n, floor n < 1)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (target n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badNonnegative n) (badSmall n).le
          (setup.commitRecoveryPooledDomainLaw finite
            (floor n) (floorNonnegative n) (floorSmall n).le
            (setup.commitRecoveryHonestPoolPins finite wellFormed (source n).strategy)
            (weights n)) who (setup.commitRecoveryModel.infoOf who history.trace))
    (reach : ℕ → ℝ) (reachPositive : ∀ n, 0 < reach n)
    (reachBound : ∀ n who (site : setup.intendedModel.InformationSite who), reach n ≤
      (setup.intendedModel.informationMass (source n).strategy who site).toReal)
    (omissionRate : ∀ n, omission n ≤ relativeTremble reach n)
    (badRate : ∀ n, bad n ≤ relativeTremble reach n)
    (floorRate : ∀ n, floor n ≤ relativeTremble reach n)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal, (∃ history : setup.intendedProtocol.History,
      setup.protocolReadout history.state = some terminal) →
      ∀ who, excludedPayoff who ≤ utility terminal who)
    (equilibrium : sourceLimit.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who history => (setup.protocolReadout history.state).elim 0
        (fun terminal => utility terminal who))) :
    (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
      sourceLimit.strategy targetLimit.strategy ∧
    (∀ who site, targetLimit.belief who
        ((setup.commitRecoveryRestriction wellFormed).site who site) =
      (sourceLimit.belief who site).map
        ((setup.commitRecoveryRestriction wellFormed).informationHistory who site)) ∧
    (∀ who (site : setup.intendedModel.InformationSite who)
      (law : PMF (setup.commitRecoveryModel.Choice who
        ((setup.commitRecoveryRestriction wellFormed).site who site).1)),
      (targetLimit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        ((setup.commitRecoveryRestriction wellFormed).site who site)
        (setup.commitRecoveryPayoff utility excludedPayoff who)).value
          ((targetLimit.strategy who).withLaw
            ((setup.commitRecoveryRestriction wellFormed).site who site).1 law) ≤
      (targetLimit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        ((setup.commitRecoveryRestriction wellFormed).site who site)
        (setup.commitRecoveryPayoff utility excludedPayoff who)).value
          (targetLimit.strategy who)) ∧
    (∀ fuel, (setup.intendedModel.runBehavioral sourceLimit.strategy fuel).map
        (fun history => (setup.protocolReadout history.state,
          fun who => (setup.protocolReadout history.state).elim 0
            (fun terminal => utility terminal who))) =
      (setup.commitRecoveryModel.runBehavioral targetLimit.strategy fuel).map
        (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
          fun who => setup.commitRecoveryPayoff utility excludedPayoff who history))) := by
  classical
  let restriction := setup.commitRecoveryRestriction wellFormed
  let _ := setup.commitRecovery_finite_history finite
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history restriction.history.injective
  have rateLimit := relativeTremble_tendsto reach reachPositive
  have omissionLimit := squeeze_zero (fun n => (omissionPositive n).le) omissionRate rateLimit
  have badLimit := squeeze_zero badNonnegative badRate rateLimit
  have floorLimit := squeeze_zero floorNonnegative floorRate rateLimit
  have agrees := setup.commitRecovery_normalized_honest_limit_extends finite wellFormed
    source target sourceLimit targetLimit sourceConverges targetConverges
    omission bad floor omissionPositive omissionSmall badNonnegative badSmall
    floorNonnegative floorSmall weights prescribed omissionLimit badLimit floorLimit
  have beliefs (who : Player) (site : setup.intendedModel.InformationSite who) :
      targetLimit.belief who (restriction.site who site) =
        (sourceLimit.belief who site).map (restriction.informationHistory who site) := by
    exact (targetConverges.belief who (restriction.site who site)).unique
      (setup.commitRecovery_normalized_honest_beliefs_of_rates finite wellFormed source target
        sourceMixed sourceBayes targetMixed targetBayes omission bad floor
        omissionPositive omissionSmall badNonnegative badSmall floorNonnegative floorSmall
        weights prescribed who site reach reachPositive (fun n => reachBound n who site)
        omissionRate badRate floorRate _ (sourceConverges.belief who site))
  refine ⟨agrees, beliefs, ?_, ?_⟩
  · intro who site law
    let sourcePayoff : setup.intendedProtocol.History → ℝ := fun history =>
      (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who)
    let targetPayoff := setup.commitRecoveryPayoff utility excludedPayoff who
    let comparator : setup.commitRecoveryModel.Choice who (restriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
      fun _ => PMF.pure (Classical.arbitrary _)
    apply restriction.retained_localOptimal_of_comparator
      setup.intended_bounded.wellFoundedHistories
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories sourceLimit targetLimit agrees
      (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
        setup.commitRecoveryModel_perfectRecall).actsOnceWhereItMatters
      who site (beliefs who site) sourcePayoff targetPayoff
      (setup.commitRecoveryPayoff_lift wellFormed utility excludedPayoff who)
      (equilibrium.1 who site) comparator ?_ law
    intro action extra history
    have deviation := setup.commitRecovery_deviation_payoff wellFormed utility excludedPayoff
      sourceLimit.strategy targetLimit.strategy agrees who site action extra history
    calc
      _ ≤ excludedPayoff who := expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
        (fun final supported => (deviation final supported).le)
      _ = expect (setup.intendedModel.runBehavioralTerminalFrom
          setup.intended_bounded.wellFoundedHistories
          (Profile.update (sig := setup.intendedModel.behavioralSignature) sourceLimit.strategy who
            ((sourceLimit.strategy who).withLaw site.1 (comparator action)))
          history.1) (fun _ => excludedPayoff who) := (expect_constant _ _).symm
      _ ≤ _ := expect_mono (fun final supported => by
          have stopped := setup.intendedModel.runBehavioralTerminalFrom_support_terminal
            setup.intended_bounded.wellFoundedHistories _ _ final supported
          obtain ⟨terminal, read⟩ := setup.exists_protocolReadout_of_terminal
            (CommitmentInterface.values setup.program) stopped
          change excludedPayoff who ≤ (setup.protocolReadout final.state).elim 0 _
          rw [read]
          exact below terminal ⟨final, read⟩ who) (payoffIntegrable_constant _ _)
        (payoffIntegrable_of_finite _ _)
  · exact setup.commitRecovery_initialized_joint wellFormed utility excludedPayoff
      sourceLimit.strategy targetLimit.strategy agrees

end Vegas.SourceProgram.Setup
