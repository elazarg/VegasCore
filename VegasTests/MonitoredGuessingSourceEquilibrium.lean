/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingSourceEvaluation

/-! # All sequential equilibria of the actual source guessing game

Every receiver mixture is permitted. At every final source information set,
the informed sender opens surely. These characterize rationality among
consistent assessments, including source choices that have zero probability.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

theorem source_rational_of_opens (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain)
    (opens : Opens assessment.strategy) :
    assessment.IsSequentiallyRationalWithin sourcePayoff 3 := by
  intro who site alternative _
  fin_cases who
  · change (assessment.continuationContext site (sourcePayoff alice) 3).value alternative ≤
      (assessment.continuationContext site (sourcePayoff alice) 3).value (assessment.strategy alice)
    obtain ⟨bit, guess, rfl⟩ := source_alice_site site
    rw [source_alice_context, source_alice_context, Profile.update_eq_self,
      opens, FinDist.expect_pure]
    apply FinDist.expect_le_of_forall
    intro disclose _
    cases disclose <;> split_ifs <;> norm_num at *
  · change (assessment.continuationContext site (sourcePayoff bob) 3).value alternative ≤
      (assessment.continuationContext site (sourcePayoff bob) 3).value (assessment.strategy bob)
    rw [source_bob_site site, source_bob_context assessment consistent opens,
      source_bob_context assessment consistent opens]
  · exact (source_no_watcher_site site).elim

theorem opening_law_of_optimal (law : FinDist Bool) (reward : ℝ) (nonnegative : 0 ≤ reward)
    (optimal : reward ≤ law.expect (fun disclose => if disclose then reward else -4)) :
    law = FinDist.pure true := by
  have normalized := law.sum_prob
  simp only [Fintype.sum_bool] at normalized
  have positive := law.prob_nonneg false
  simp only [FinDist.expect_eq_sum, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at optimal
  have absent : law.prob false = 0 := by nlinarith
  have present : law.prob true = 1 := by linarith
  apply FinDist.ext_of_prob
  intro disclose
  cases disclose <;> simp [absent, present, FinDist.prob_pure_eq_ite]

theorem source_rational_opens (assessment : sourceModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin sourcePayoff 3) :
    Opens assessment.strategy := by
  intro bit guess
  let replacement := (sourceProfile (FinDist.pure false) (FinDist.pure true)) alice
  have optimal := rational alice (sourceAliceSite bit guess) replacement (Set.mem_univ _)
  change (assessment.continuationContext (sourceAliceSite bit guess) (sourcePayoff alice) 3).value
    replacement ≤ _ at optimal
  rw [source_alice_context, source_alice_context, Profile.update_eq_self] at optimal
  have chosen : sourceDecisionLaw
      (Profile.update (sig := sourceModel.behavioralSignature)
        assessment.strategy alice replacement) alice (sourceAliceSite bit guess).1 =
      FinDist.pure true := by
    simpa only [sourceDecisionLaw, sourceChoice, Profile.update_same, replacement] using
      sourceProfile_opens (FinDist.pure false) bit guess
  rw [chosen, FinDist.expect_pure] at optimal
  simp only [↓reduceIte] at optimal
  exact opening_law_of_optimal _ _ (by split_ifs <;> norm_num) optimal

theorem source_rational_iff_opens (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain) :
    assessment.IsSequentiallyRationalWithin sourcePayoff 3 ↔ Opens assessment.strategy :=
  ⟨source_rational_opens assessment, source_rational_of_opens assessment consistent⟩

/-- Every Boolean guessing mixture has a source sequential equilibrium, in
the actual setup protocol. The same profile supplies Alice's off-path opening. -/
theorem source_sequential_equilibrium (guess : FinDist Bool) :
    ∃ assessment : sourceModel.BehavioralAssessment,
      assessment.strategy = sourceProfile guess (FinDist.pure true) ∧
      assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        assessment.continuationContext site (sourcePayoff who) 3) := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile)
      uniformSourceProfile_fullyMixed sourceAntichain (sourceProfile guess (FinDist.pure true))
  refine ⟨assessment, strategy, ?_, consistent⟩
  apply source_rational_of_opens assessment consistent
  rw [strategy]
  exact sourceProfile_opens guess

theorem source_initialized_states (profile : Profile sourceModel.behavioralSignature)
    (opens : Opens profile) :
    (sourceModel.runBehavioral profile 3).map History.state =
      (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
        (sourceDecisionLaw profile bob sourceBobSite.1).map fun guess =>
          (SourcePath.done bit guess true).state := by
  change (sourceModel.runBehavioralFrom profile 3 sourceArena.initHistory).map History.state = _
  rw [source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind]
  change ((sourceSetup.initialLaw.map
    (fun state => (some (.inl (sourceSetup.initialConfig state)) : sourceArena.State))).bind
      (sourceKernel profile)).bind (sourceKernel profile) = _
  change ((((FinDist.uniformOfFintype (α := Bool)).map initialState).map
    (fun state => (some (.inl (sourceSetup.initialConfig state)) : sourceArena.State))).bind
      (sourceKernel profile)).bind (sourceKernel profile) = _
  simp only [FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro bit _
  have first : sourceBobSite.1 =
      sourceModel.infoOf bob (SourcePath.drawn bit).history.trace :=
    (drawn_bob_info bit false).symm
  rw [first, source_info]
  simp only [sourceKernel, sourceDecisionLaw, FinDist.bind_map, FinDist.map_comp]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro choice _
  have last := opens bit (OwnAction.disclosure choice)
  simp only [sourceDecisionLaw, sourceAliceSite, InformationModel.informationSite,
    source_info] at last
  change ((sourceChoice profile alice
    (some (.inr (.inl ((guessConfig bit (OwnAction.disclosure choice)).view alice))))).map
      OwnAction.disclosure) = FinDist.pure true at last
  have mapped := congrArg
    (FinDist.map (fun disclose => (SourcePath.done bit (OwnAction.disclosure choice)
      disclose).state)) last
  rw [FinDist.map_comp, FinDist.map_pure] at mapped
  exact mapped

/-- Every actual source SE has exactly one initialized law in this family.
The equality retains the entire terminal source state, including the initial
commitments, public results, and the players' remembered actions. -/
theorem source_equilibrium_states (assessment : sourceModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      assessment.continuationContext site (sourcePayoff who) 3)) :
    (sourceModel.runBehavioral assessment.strategy 3).map History.state =
      (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
        (sourceDecisionLaw assessment.strategy bob sourceBobSite.1).map fun guess =>
          (SourcePath.done bit guess true).state :=
  source_initialized_states assessment.strategy (source_rational_opens assessment equilibrium.1)

end VegasTests.MonitoredGuessing
