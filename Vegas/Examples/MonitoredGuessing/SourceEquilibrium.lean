/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.SourceEvaluation
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # All sequential equilibria of the actual source guessing game

Every receiver mixture is permitted. At every final source information set,
the informed sender opens surely. These characterize rationality among
consistent assessments, including source choices that have zero probability.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

theorem source_rational_of_opens (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain)
    (opens : Opens assessment.strategy) :
    assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (sourcePayoff who) 3 := by
  intro who site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => payoffIntegrable_of_finite _ _).mpr fun alternative _ => ?_
  fin_cases who
  · change (assessment.truncatedContinuationContext site (sourcePayoff alice) 3).value alternative ≤
      (assessment.truncatedContinuationContext site (sourcePayoff alice)
          3).value (assessment.strategy alice)
    obtain ⟨bit, guess, rfl⟩ := source_alice_site site
    rw [source_alice_context, source_alice_context, Profile.update_eq_self,
      opens, expect_pure]
    refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun disclose _ => ?_
    cases disclose <;> split_ifs <;> norm_num at *
  · change (assessment.truncatedContinuationContext site (sourcePayoff bob) 3).value alternative ≤
      (assessment.truncatedContinuationContext site (sourcePayoff bob)
          3).value (assessment.strategy bob)
    rw [source_bob_site site, source_bob_context assessment consistent opens,
      source_bob_context assessment consistent opens]
  · exact (source_no_watcher_site site).elim

theorem opening_law_of_optimal (law : PMF Bool) (reward : ℝ) (nonnegative : 0 ≤ reward)
    (optimal : reward ≤ expect law (fun disclose => if disclose then reward else -4)) :
    law = PMF.pure true := by
  have normalized := pmf_sum_toReal_eq_one law
  simp only [Fintype.sum_bool] at normalized
  have positiveTrue : 0 ≤ (law true).toReal := ENNReal.toReal_nonneg
  have positiveFalse : 0 ≤ (law false).toReal := ENNReal.toReal_nonneg
  simp only [expect_eq_sum, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at optimal
  have absent : (law false).toReal = 0 := by nlinarith
  have present : (law true).toReal = 1 := by linarith
  apply pmf_ext_toReal
  intro disclose
  cases disclose <;> simp [absent, present]

theorem source_rational_opens (assessment : sourceModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (sourcePayoff who) 3) :
    Opens assessment.strategy := by
  intro bit guess
  let replacement := (sourceProfile (PMF.pure false) (PMF.pure true)) alice
  have optimal := (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    fun _ _ => (payoffIntegrable_of_finite _ _)).mp
        (rational alice (sourceAliceSite bit guess)) replacement
      (Set.mem_univ _)
  change (assessment.truncatedContinuationContext (sourceAliceSite bit guess) (sourcePayoff alice)
      3).value
    replacement ≤ _ at optimal
  rw [source_alice_context, source_alice_context, Profile.update_eq_self] at optimal
  have chosen : sourceDecisionLaw
      (Profile.update (sig := sourceModel.behavioralSignature)
        assessment.strategy alice replacement) alice (sourceAliceSite bit guess).1 =
      PMF.pure true := by
    simpa only [sourceDecisionLaw, sourceChoice, Profile.update_same, replacement] using
      sourceProfile_opens (PMF.pure false) bit guess
  rw [chosen, expect_pure] at optimal
  simp only [↓reduceIte] at optimal
  exact opening_law_of_optimal _ _ (by split_ifs <;> norm_num) optimal

theorem source_rational_iff_opens (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain) :
    (assessment.IsSequentiallyRationalFor fun who site =>
        assessment.truncatedContinuationContext site (sourcePayoff
            who) 3) ↔ Opens assessment.strategy :=
  ⟨source_rational_opens assessment, source_rational_of_opens assessment consistent⟩

/-- Every Boolean guessing mixture has a source sequential equilibrium, in
the actual setup protocol. The same profile supplies Alice's off-path opening. -/
theorem source_sequential_equilibrium (guess : PMF Bool) :
    ∃ assessment : sourceModel.BehavioralAssessment,
      assessment.strategy = sourceProfile guess (PMF.pure true) ∧
      assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        assessment.truncatedContinuationContext site (sourcePayoff who) 3) := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile)
      uniformSourceProfile_fullyMixed sourceAntichain (sourceProfile guess (PMF.pure true))
  refine ⟨assessment, strategy, ?_, consistent⟩
  apply source_rational_of_opens assessment consistent
  rw [strategy]
  exact sourceProfile_opens guess

theorem source_initialized_states (profile : Profile sourceModel.behavioralSignature)
    (opens : Opens profile) :
    (sourceModel.runBehavioral profile 3).map History.state =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (sourceDecisionLaw profile bob sourceBobSite.1).map fun guess =>
          (SourcePath.done bit guess true).state := by
  change (sourceModel.runBehavioralFrom profile 3 sourceArena.initHistory).map History.state = _
  rw [source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind]
  change ((sourceSetup.initialLaw.map
    (fun state => (some (.inl (sourceSetup.initialConfig state)) : sourceArena.State))).bind
      (sourceKernel profile)).bind (sourceKernel profile) = _
  change ((((PMF.uniformOfFintype Bool).map initialState).map
    (fun state => (some (.inl (sourceSetup.initialConfig state)) : sourceArena.State))).bind
      (sourceKernel profile)).bind (sourceKernel profile) = _
  simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def]
  apply bind_congr_on_support _
  intro bit _
  have first : sourceBobSite.1 =
      sourceModel.infoOf bob (SourcePath.drawn bit).history.trace :=
    (drawn_bob_info bit false).symm
  rw [first, source_info]
  simp only [sourceKernel, sourceDecisionLaw, PMF.bind_map, PMF.map_comp]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro choice _
  have last := opens bit (OwnAction.disclosure choice)
  simp only [sourceDecisionLaw, sourceAliceSite, InformationModel.informationSite,
    source_info] at last
  change ((sourceChoice profile alice
    (some (.inr (.inl ((guessConfig bit (OwnAction.disclosure choice)).view alice))))).map
      OwnAction.disclosure) = PMF.pure true at last
  have mapped := congrArg
    (PMF.map (fun disclose => (SourcePath.done bit (OwnAction.disclosure choice)
      disclose).state)) last
  rw [PMF.map_comp, PMF.pure_map] at mapped
  exact mapped

/-- Every actual source SE has exactly one initialized law in this family.
The equality retains the entire terminal source state, including the initial
commitments, public results, and the players' remembered actions. -/
theorem source_equilibrium_states (assessment : sourceModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      assessment.truncatedContinuationContext site (sourcePayoff who) 3)) :
    (sourceModel.runBehavioral assessment.strategy 3).map History.state =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (sourceDecisionLaw assessment.strategy bob sourceBobSite.1).map fun guess =>
          (SourcePath.done bit guess true).state :=
  source_initialized_states assessment.strategy (source_rational_opens assessment equilibrium.1)

end Vegas.Examples.MonitoredGuessing
